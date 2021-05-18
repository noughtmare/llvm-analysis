{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, DeriveGeneric #-}
{-# LANGUAGE ViewPatterns #-}
-- | This module defines an abstraction over field accesses of
-- structures called AccessPaths.  A concrete access path is rooted at
-- a value, while an abstract access path is rooted at a type.  Both
-- include a list of 'AccessType's that denote dereferences of
-- pointers, field accesses, and array references.
module LLVM.Analysis.AccessPath (
  -- * Types
  AccessPath(..),
  accessPathComponents,
  AbstractAccessPath(..),
  abstractAccessPathComponents,
  AccessType(..),
  AccessPathError(..),
  -- * Constructor
  accessPath,
  abstractAccessPath,
  appendAccessPath,
  followAccessPath,
  reduceAccessPath,
  externalizeAccessPath
  ) where

import Data.List (isPrefixOf)
import Control.DeepSeq
import Control.Exception
import Control.Failure hiding ( failure )
import qualified Control.Failure as F
import Data.Hashable
import qualified Data.List as L
-- import qualified Data.Text as T
import Text.PrettyPrint.GenericPretty

import LLVM.Analysis

-- import Text.Printf
-- import Debug.Trace
-- debug = flip trace

data AccessPathError = NoPathError Value
                     | NotMemoryInstruction Stmt
                     | CannotFollowPath AbstractAccessPath Value
                     | BaseTypeMismatch Type Type
                     | NonConstantInPath AbstractAccessPath Value
                     | EndpointTypeMismatch Type Type
                     | IrreducableAccessPath AbstractAccessPath
                     | CannotExternalizeType Type
                     deriving (Show)

instance Exception AccessPathError

-- | The sequence of field accesses used to reference a field
-- structure.
data AbstractAccessPath =
  AbstractAccessPath { abstractAccessPathBaseType :: Type
                     , abstractAccessPathEndType :: Type
                     , abstractAccessPathTaggedComponents :: [(Type, AccessType)]
                     }
  deriving (Eq, Ord, Generic, Show)

abstractAccessPathComponents :: AbstractAccessPath -> [AccessType]
abstractAccessPathComponents = map snd . abstractAccessPathTaggedComponents

-- TODO
-- instance Out AbstractAccessPath
-- instance Show AbstractAccessPath where
--   show = pretty

instance Hashable AbstractAccessPath where
  hashWithSalt s (AbstractAccessPath bt et cs) =
    s `hashWithSalt` bt `hashWithSalt` et `hashWithSalt` cs

appendAccessPath :: (Failure AccessPathError m)
                    => AbstractAccessPath
                    -> AbstractAccessPath
                    -> m AbstractAccessPath
appendAccessPath (AbstractAccessPath bt1 et1 cs1) (AbstractAccessPath bt2 et2 cs2) =
  case et1 == bt2 of
    True -> return $ AbstractAccessPath bt1 et2 (cs1 ++ cs2)
    False -> F.failure $ EndpointTypeMismatch et1 bt2

-- | If the access path has more than one field access component, take
-- the first field access and the base type to compute a new base type
-- (the type of the indicated field) and the rest of the path
-- components.  Also allows for the discarding of array accesses.
--
-- Each call reduces the access path by one component
reduceAccessPath :: (Failure AccessPathError m)
                    => AbstractAccessPath -> m AbstractAccessPath
reduceAccessPath (AbstractAccessPath (PtrTo t) et ((_, AccessDeref):cs)) =
  return $! AbstractAccessPath t et cs
-- FIXME: Some times (e.g., pixmap), the field number is out of range.
-- Have to figure out what could possibly cause that. Until then, just
-- ignore those cases.  Users of this are working at best-effort anyway.
reduceAccessPath p@(AbstractAccessPath (Struct _ ts _) et ((_,AccessField fldNo):cs)) =
  case fldNo < length ts of
    True -> return $! AbstractAccessPath (ts !! fldNo) et cs
    False -> F.failure $ IrreducableAccessPath p
reduceAccessPath (AbstractAccessPath (Array _ t) et ((_,AccessArray):cs)) =
  return $! AbstractAccessPath t et cs
reduceAccessPath p = F.failure $ IrreducableAccessPath p

instance NFData AbstractAccessPath where
  rnf a@(AbstractAccessPath _ _ ts) = ts `deepseq` a `seq` ()

data AccessPath =
  AccessPath { accessPathBaseValue :: Value
             , accessPathBaseType :: Type
               -- ^ If there are some wonky bitcasts in play, this
               -- type records the real type of this path, even if the
               -- base was something unrelated and bitcast.  The real
               -- type is the type casted /to/.
             , accessPathEndType :: Type
             , accessPathTaggedComponents :: [(Type, AccessType)]
             }
  deriving (Generic, Eq, Ord, Show)

instance NFData AccessPath

accessPathComponents :: AccessPath -> [AccessType]
accessPathComponents = map snd . accessPathTaggedComponents

-- TODO
-- instance Out AccessPath
-- instance Show AccessPath where
--   show = pretty

-- instance NFData AccessPath where
--   rnf a@(AccessPath _ _ _ ts) = ts `deepseq` a `seq` ()
-- 
-- instance Hashable AccessPath where
--   hashWithSalt s (AccessPath bv bt ev cs) =
--     s `hashWithSalt` bv `hashWithSalt` bt `hashWithSalt` ev `hashWithSalt` cs

data AccessType = AccessField !Int
                  -- ^ Field access of the field with this index
                | AccessUnion
                  -- ^ A union access.  The union discriminator is the
                  -- /type/ that this AccessType is tagged with in the
                  -- AccessPath.  Unions in LLVM do not have an
                  -- explicit representation of their fields, so there
                  -- is no index possible here.
                | AccessArray
                  -- ^ An array access; all array elements are treated
                  -- as a unit
                | AccessDeref
                  -- ^ A plain pointer dereference
                deriving (Read, Show, Eq, Ord, Generic)

instance Out AccessType

instance NFData AccessType where
  rnf a@(AccessField i) = i `seq` a `seq` ()
  rnf _ = ()

instance Hashable AccessType where
  hashWithSalt s (AccessField ix) =
    s `hashWithSalt` (1 :: Int) `hashWithSalt` ix
  hashWithSalt s AccessUnion = s `hashWithSalt` (154 :: Int)
  hashWithSalt s AccessArray = s `hashWithSalt` (26 :: Int)
  hashWithSalt s AccessDeref = s `hashWithSalt` (300 :: Int)

followAccessPath :: (Failure AccessPathError m) => AbstractAccessPath -> Value -> m Value
followAccessPath aap@(AbstractAccessPath bt _ components) val =
  case derefPointerType bt /= valType val of
    True -> F.failure (BaseTypeMismatch bt (valType val))
    False -> walk components val
  where
    walk [] v = return v
    walk ((_, AccessField ix) : rest) v =
      case valValue v of
        ValStruct vs _ ->
          case ix < length vs of
            False -> error $ concat [ "LLVM.Analysis.AccessPath.followAccessPath.walk: "
                                    ," Invalid access path: ", show aap, " / ", show val
                                    ]
            True -> walk rest (vs !! ix)
        _ -> F.failure (NonConstantInPath aap val)
    walk _ _ = F.failure (CannotFollowPath aap val)

abstractAccessPath :: AccessPath -> AbstractAccessPath
abstractAccessPath (AccessPath _ vt t p) =
  AbstractAccessPath vt t p
-- | For Store, RMW, and CmpXchg instructions, the returned access
-- path describes the field /stored to/.  For Load instructions, the
-- returned access path describes the field loaded.  For
-- GetElementPtrInsts, the returned access path describes the field
-- whose address was taken/computed.
accessPath :: (Failure AccessPathError m) => Stmt -> m AccessPath
accessPath i = case stmtInstr i of
  Store sv sa _ _ -> return $! addDeref $ go
    (AccessPath sa (valType sa) (valType sv) [])
    (valType sa)
    sa
  Load la _ _ -> return $! addDeref $ go
    (AccessPath la (valType la) (getType i) [])
    (valType la)
    la
  CmpXchg _ _ p _ nv _ _ _ -> return $! addDeref $ go
    (AccessPath p (valType p) (valType nv) [])
    (valType p)
    p
  AtomicRW _ _ p v _ _ -> return $! addDeref $ go
    (AccessPath p (valType p) (valType v) [])
    (valType p)
    p
  GEP{} ->
      -- FIXME: Should this really get a deref tag?  Unclear...
           return $! addDeref $ go
    (AccessPath
      (toValue i)
      (getType i)
      (getType i)
      []
    )
    (getType i)
    (toValue i)
    -- If this is an argument to a function call, it could be a
    -- bitcasted GEP or Load
  Conv BitCast (valValue -> ValIdent (IdentValStmt i')) _ ->
    accessPath i'
  _ -> F.failure (NotMemoryInstruction i)
  where
    addDeref p =
      let t = accessPathBaseType p
          cs' = (t, AccessDeref) : accessPathTaggedComponents p
      in p { accessPathTaggedComponents = cs' }
    go :: AccessPath -> Type -> Value -> AccessPath
    go p vt v =
      -- Note that @go@ does not need to update the accessPathBaseType
      -- until the end (fallthrough) case.
      case valValue v of
        -- Unions have no representation in the IR; the only way we
        -- can identify a union is by looking for instances where a
        -- struct pointer type beginning with '%union.' is being cast
        -- into something else.  This lets us know the union variant
        -- being accessed.
        ValIdent (IdentValStmt Stmt { stmtInstr = Conv BitCast cv _ })
          | isUnionPointerType (valType cv) ->
            let p' = p { accessPathTaggedComponents =
                            (valType v, AccessUnion) : accessPathTaggedComponents p
                       }
            in go p' (valType v) cv
          | otherwise -> go p (valType v) cv
        ValConstExpr (ConstConv BitCast cv _) ->
          go p (valType v) cv
        ValIdent (IdentValStmt Stmt { stmtInstr = GEP _ base [_] }) ->
          let p' = p { accessPathBaseValue = base
                     , accessPathTaggedComponents = (valType v, AccessArray) : accessPathTaggedComponents p
                     }
          in go p' (valType base) base
        ValIdent (IdentValStmt Stmt { stmtInstr = GEP _ base ixs }) ->
          let p' = p { accessPathBaseValue = base
                     , accessPathTaggedComponents =
                       gepIndexFold base ixs ++ accessPathTaggedComponents p
                     }
          in go p' (valType base) base
        ValConstExpr (ConstGEP _ _ _ (base:ixs)) ->
          let p' = p { accessPathBaseValue = base
                     , accessPathTaggedComponents =
                       gepIndexFold base ixs ++ accessPathTaggedComponents p
                     }
          in go p' (valType base) base
        -- InstructionC LoadInst { loadAddress = la } ->
        ValIdent (IdentValStmt Stmt { stmtInstr = Load la _ _ }) ->
          let p' = p { accessPathBaseValue  = la
                     , accessPathTaggedComponents =
                          (vt, AccessDeref) : accessPathTaggedComponents p
                     }
          in go p' (valType la) la
        _ -> p { accessPathBaseValue = v
               , accessPathBaseType = vt
               }

isUnionPointerType :: Type -> Bool
isUnionPointerType t =
  case t of
    PtrTo (Struct (Right (Ident name)) _ _) ->
      "union." `isPrefixOf` name
    _ -> False

-- | Convert an 'AbstractAccessPath' to a format that can be written
-- to disk and read back into another process.  The format is the pair
-- of the base name of the structure field being accessed (with
-- struct. stripped off) and with any numeric suffixes (which are
-- added by llvm) chopped off.  The actually list of 'AccessType's is
-- preserved.
--
-- The struct name mangling here basically assumes that the types
-- exposed via the access path abstraction have the same definition in
-- all compilation units.  Ensuring this between runs is basically
-- impossible, but it is pretty much always the case.
externalizeAccessPath :: (Failure AccessPathError m)
                         => AbstractAccessPath
                         -> m (String, [AccessType])
externalizeAccessPath accPath =
  maybe (F.failure (CannotExternalizeType bt)) return $ do
    baseName <- structTypeToName (stripPointerTypes bt)
    return (baseName, abstractAccessPathComponents accPath)
  where
    bt = abstractAccessPathBaseType accPath

-- Internal Helpers

derefPointerType :: Type -> Type
derefPointerType (PtrTo p) = p
derefPointerType t = error ("LLVM.Analysis.AccessPath.derefPointerType: Type is not a pointer type: " ++ show t)

gepIndexFold :: Value -> [Value] -> [(Type, AccessType)]
gepIndexFold base (ptrIx : ixs) =
  -- GEPs always have a pointer as the base operand
  let ty@(PtrTo baseType) = valType base
  in case valValue ptrIx of
    ValInteger 0 ->
      snd $ L.foldl' walkGep (baseType, []) ixs
    _ ->
      snd $ L.foldl' walkGep (baseType, [(ty, AccessArray)]) ixs
  where
    walkGep (ty, acc) ix =
      case ty of
        -- If the current type is a pointer, this must be an array
        -- access; that said, this wouldn't even be allowed because a
        -- pointer would have to go through a Load...  check this
        PtrTo ty' -> (ty', (ty, AccessArray) : acc)
        Array _ ty' -> (ty', (ty, AccessArray) : acc)
        Vector _ ty' -> (ty', (ty, AccessArray) : acc) -- TODO: this is not really an array
        Struct _ ts _ ->
          case valValue ix of
            ValInteger fldNo ->
              let fieldNumber = fromIntegral fldNo
                  ty' = ts !! fieldNumber
              in (ty', (ty', AccessField fieldNumber) : acc)
            _ -> error ("LLVM.Analysis.AccessPath.gepIndexFold.walkGep: Invalid non-constant GEP index for struct: " ++ show ty)
        _ -> error ("LLVM.Analysis.AccessPath.gepIndexFold.walkGep: Unexpected type in GEP: " ++ show ty)
gepIndexFold v [] =
  error ("LLVM.Analysis.AccessPath.gepIndexFold: GEP instruction/base with empty index list: " ++ show v)

{-# ANN module "HLint: ignore Use if" #-}
