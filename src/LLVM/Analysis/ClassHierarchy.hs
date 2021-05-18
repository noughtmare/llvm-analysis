{-# LANGUAGE ViewPatterns #-}
-- | This module defines a class hierarchy analysis for C++.
--
-- This analysis operates entirely at the bitcode level and does not
-- rely on metadata.
--
-- The hierarchy analysis result only includes class instantiations in
-- the bitcode provided (i.e., it is most useful for whole-program
-- bitcodes).  Results for single compilation units will be
-- incomplete.
--
-- Also note that this analysis requires the input bitcode to be built
-- with C++ run-time type information.
module LLVM.Analysis.ClassHierarchy (
  -- * Types
  CHA,
  VTable,
  -- * Functions
  resolveVirtualCallee,
  classSubtypes,
  classTransitiveSubtypes,
  classParents,
  classAncestors,
  classVTable,
  defineAtSlot,
  runCHA,
  -- * Testing
  classHierarchyToTestFormat
  ) where

import ABI.Itanium
import Data.Foldable ( toList )
import Data.Generics.Uniplate.Data
import Data.List ( stripPrefix )
import Data.Map ( Map )
import qualified Data.Map as M
import qualified Data.Map.Strict as MS (insertWith)
import Data.Maybe ( fromMaybe, mapMaybe )
import Data.Set ( Set )
import qualified Data.Set as S
import Data.Vector ( Vector, (!?) )
import qualified Data.Vector as V

import LLVM.Analysis
import LLVM.Analysis.Util.Names

-- | The result of the class hierarchy analysis
data CHA = CHA { childrenMap :: Map Name (Set Name)
                 -- ^ All classes derived from the class used as the map key
               , parentMap :: Map Name (Set Name)
                 -- ^ The parent classes of the map key
               , vtblMap :: Map Name VTable
                 -- ^ The virtual function pointer table for the map key
               , typeMapping :: Map Name Type
                 -- ^ A relation between ABI names and LLVM Types
               , chaModule :: Module
                 -- ^ A saved reference to the module
               }

-- Note that all keys are by Name here.  The name is the name of the
-- class, with conversions done between LLVM types and Names
-- as-needed.  This is simplest because it isn't possible to get an
-- LLVM type at all stages of the analysis - those can only be
-- reconstructed after the entire module is analyzed.  Since LLVM
-- records namespace information in class type names, this process is
-- robust enough.

-- | An interface for inspecting virtual function tables
data VTable = ExternalVTable
            | VTable (Vector Define)
            deriving (Show)

resolveVirtualCallee :: CHA -> Instr -> Maybe [Define]
resolveVirtualCallee cha i =
  case i of
    -- Resolve direct calls (note, this does not cover calls to
    -- external functions, unfortunately).
    Call _ _ (valValue -> ValSymbol (SymValDefine f)) _ -> Just [f]
    -- Resolve actual virtual dispatches.  Note that the first
    -- argument is always the @this@ pointer.
    Call _ _ (ValInstr (Load la _ _)) (thisVal : _) ->
      virtualDispatch cha la thisVal
    Invoke _ (valValue -> ValSymbol (SymValDefine f)) _ _ _ -> Just [f]
    Invoke _ (ValInstr (Load la _ _)) (thisVal : _) _ _ ->
      virtualDispatch cha la thisVal
    _ -> Nothing

-- | Dispatch to one of the vtable lookup strategies based on the
-- value that was loaded from the vtable.
virtualDispatch :: CHA -> Value -> Value -> Maybe [Define]
virtualDispatch cha loadAddr thisVal = do
  slotNumber <- getVFuncSlot cha loadAddr thisVal
  return $! mapMaybe (defineAtSlot slotNumber) vtbls
  where
    PtrTo thisType = valType thisVal
    derivedTypes = classTransitiveSubtypes cha thisType
    vtbls = mapMaybe (classVTable cha) derivedTypes

-- TODO check if these patterns still hold
-- TODO I added valValue here in the comparisons, but maybe the equality
--      instance of Value itself should be changed
--
-- | Identify the slot number of a virtual function call.  Basically,
-- work backwards from the starred instructions in the virtual
-- function call dispatch patterns:
--
-- clang:
--
--   %2 = bitcast %struct.Base* %0 to void (%struct.Base*)***
--   %vtable = load void (%struct.Base*)*** %2
--   %vfn = getelementptr inbounds void (%struct.Base*)** %vtable, i64 1
-- * %3 = load void (%struct.Base*)** %vfn
--   call void %3(%struct.Base* %0)
--
-- clang-13 (from tests/virtual-dispatch/second-method.cpp):
--
--   %0 = bitcast %struct.DispatchBase* %b to void (%struct.DispatchBase*)***
--   %vtable = load void (%struct.DispatchBase*)**, void (%struct.DispatchBase*)*** %0, align 8, !tbaa !2
--   %vfn = getelementptr inbounds void (%struct.DispatchBase*)*, void (%struct.DispatchBase*)** %vtable, i64 1
-- * %1 = load void (%struct.DispatchBase*)*, void (%struct.DispatchBase*)** %vfn, align 8
--   call void %1(%struct.DispatchBase* nonnull dereferenceable(8) %b)
--
-- clang0:
--
--   %0 = bitcast %struct.Base* %b to void (%struct.Base*)***
--   %vtable = load void (%struct.Base*)*** %0
-- * %1 = load void (%struct.Base*)** %vtable
--   call void %1(%struct.Base* %b)
--
-- dragonegg:
--
--   %2 = getelementptr inbounds %struct.Base* %1, i32 0, i32 0
--   %3 = load i32 (...)*** %2, align 4
--   %4 = bitcast i32 (...)** %3 to i8*
--   %5 = getelementptr i8* %4, i32 4
--   %6 = bitcast i8* %5 to i32 (...)**
-- * %7 = load i32 (...)** %6, align 4
--   %8 = bitcast i32 (...)* %7 to void (%struct.Base*)*
--   call void %8(%struct.Base* %1)
--
-- dragonegg0 (first method slot):
--
--   %2 = getelementptr inbounds %struct.Base* %1, i32 0, i32 0
--   %3 = load i32 (...)*** %2, align 4
-- * %4 = load i32 (...)** %3, align 4
--   %5 = bitcast i32 (...)* %4 to void (%struct.Base*)*
--   call void %5(%struct.Base* %1)

getVFuncSlot :: CHA -> Value -> Value -> Maybe Int
getVFuncSlot cha loadAddr thisArg =
  case loadAddr of
    -- Clang style
    ValInstr (GEP _
        (ValInstr (Load (ValInstr (Conv BitCast thisPtr _)) _ _))
        [valValue -> ValInteger slotNo])
      | thisArg == thisPtr -> Just $! fromIntegral slotNo
    ValInstr (Load (ValInstr (Conv BitCast base _)) _ _)
      | thisArg == base -> Just 0
    -- Dragonegg0 style (slot 0 call)
    ValInstr (Load (ValInstr (GEP _ thisPtr [valValue -> ValInteger 0, valValue -> ValInteger 0])) _ _)
      | thisArg == thisPtr -> Just 0
    -- Dragonegg general case
    ValInstr (Conv BitCast
      (ValInstr (GEP _
        (ValInstr (Conv BitCast
          (ValInstr (Load
            (ValInstr (GEP _ thisPtr [valValue -> ValInteger 0, valValue -> ValInteger 0])) _ _)) _))
        [valValue -> ValInteger offset])) _)
      | thisArg == thisPtr -> Just $! indexFromOffset cha (fromIntegral offset)
    _ -> Nothing

indexFromOffset :: CHA -> Int -> Int
indexFromOffset cha bytes = (bytes * 8) `div` pointerBits
  where
    m = chaModule cha
    targetData = modDataLayout m
    -- TODO I'm not sure that this should be specialized to address space 0
    pointerBits = fromMaybe 64 (do [x] <- sequence (do PointerSize 0 _ _ y <- targetData; pure y); pure x)

-- | List of all types derived from the given 'Type'.
classSubtypes :: CHA -> Type -> [Type]
classSubtypes cha t =
  namesToTypes cha (M.findWithDefault mempty (typeToName t) (childrenMap cha))

-- | List of all types *transitively* drived from the given 'Type'
classTransitiveSubtypes :: CHA -> Type -> [Type]
classTransitiveSubtypes = transitiveTypes childrenMap

-- | List of the immediate parent types of the given 'Type'.  The list
-- is only empty for the root of a class hierarchy.
classParents :: CHA -> Type -> [Type]
classParents cha t =
  namesToTypes cha (M.findWithDefault mempty (typeToName t) (parentMap cha))

-- | List of all (transitive) parent types of the given 'Type'.
classAncestors :: CHA -> Type -> [Type]
classAncestors = transitiveTypes parentMap

transitiveTypes :: (CHA -> Map Name (Set Name)) -> CHA -> Type -> [Type]
transitiveTypes selector cha t0 =
  namesToTypes cha (go (S.singleton (typeToName t0)))
  where
    go ts =
      let nextLevel = foldMap getParents ts
      in case mempty == nextLevel of
        True -> ts
        False -> go nextLevel `mappend` ts
    getParents t = M.findWithDefault mempty t (selector cha)

-- | Retrieve the vtbl for a given type.  Will return Nothing if the
-- type is not a class or if the class has no virtual methods.
classVTable :: CHA -> Type -> Maybe VTable
classVTable cha t = M.lookup (typeToName t) (vtblMap cha)

-- | Get the function at the named slot in a vtable.  Returns Nothing
-- for external vtables.
defineAtSlot :: Int -> VTable -> Maybe Define
defineAtSlot _ ExternalVTable = Nothing
defineAtSlot slot (VTable v) = v !? slot

-- | The analysis reconstructs the class hierarchy by looking at
-- typeinfo structures (which are probably only generated when
-- compiling with run-time type information enabled).  It also finds
-- vtables by demangling the names of the vtables in the module.
runCHA :: Module -> CHA
runCHA m = foldr buildTypeMap cha1 ctors
  where
    gvs = modGlobals m
    ctors = moduleConstructors m
    cha0 = CHA mempty mempty mempty mempty m
    cha1 = foldr recordParents cha0 gvs

moduleConstructors :: Module -> [Define]
moduleConstructors = filter isC2Constructor . modDefines

-- | Fill in the mapping from Names to LLVM Types in the class
-- hierarchy analysis by examining the first argument of each
-- constructor.  This argument indicates the LLVM type of the type
-- being constructed; parsing the LLVM type name into a Name yields
-- the map key.
buildTypeMap :: Define -> CHA -> CHA
buildTypeMap f cha =
  case parseTypeName fname of
    Left e -> error ("LLVM.Analysis.ClassHierarchy.buildTypeMap: " ++ e)
    Right n ->
      cha { typeMapping = M.insert n t (typeMapping cha) }
  where
    t = constructedType f
    fname = case t of
      Struct       (Right (Ident tn)) _ _ -> stripNamePrefix tn
      _ -> error ("LLVM.Analysis.ClassHierarchy.buildTypeMap: Expected class type: " ++ show t)

-- | Determine the parent classes for each class type (if any) and
-- record them in the class hierarchy analysis summary.  This
-- information is derived from the typeinfo structures.  Additionally,
-- record the vtable for each type.
recordParents :: Global -> CHA -> CHA
recordParents gv acc =
  case dname of
    Left _ -> acc
    Right structuredName ->
      case structuredName of
        VirtualTable (ClassEnumType name) ->
          recordVTable acc name (globalValue gv)
        VirtualTable tn -> error ("LLVM.Analysis.ClassHierarchy.recordParents: Expected a class name for virtual table: " ++ show tn)
        TypeInfo (ClassEnumType name) ->
          recordTypeInfo acc name (globalValue gv)
        TypeInfo tn -> error ("LLVM.Analysis.ClassHierarchy.recordParents: Expected a class name for typeinfo: " ++ show tn)
        _ -> acc
  where
    Symbol n = globalName gv
    dname = demangleName n

-- TODO I added a case for a struct with a array fields, which seems to be a new
--      way that clang 13 encodes classes, but I should investigate further.
-- | Record the vtable by storing only the function pointers from the
recordVTable :: CHA -> Name -> Maybe Value -> CHA
recordVTable cha name Nothing =
  cha { vtblMap = M.insert name ExternalVTable (vtblMap cha) }
recordVTable cha name (Just (valValue -> ValArray _ vs))
  = cha { vtblMap = M.insert name (makeVTable vs) (vtblMap cha) }
recordVTable cha name (Just (valValue -> ValStruct vss _))
  = cha { vtblMap = M.insert name (makeVTable (arrayElems =<< vss)) (vtblMap cha) }
  where
    arrayElems (valValue -> ValArray _ vs) = vs
    arrayElems _ = []
recordVTable cha name _ = recordVTable cha name Nothing

-- | Build a VTable given the list of values in the vtable array.  The
-- actual vtable (as indexed) doesn't begin at index zero, so we drop
-- all of the values that are not functions, then take everything that
-- is.
makeVTable :: [Value] -> VTable
makeVTable =
  VTable . V.fromList . map unsafeToDefine . takeWhile isVTableFunctionType . dropWhile (not . isVTableFunctionType)

unsafeToDefine :: Value -> Define
unsafeToDefine (valValue -> ValSymbol (SymValDefine f)) = f
unsafeToDefine (valValue -> ValConstExpr (ConstConv BitCast (valValue -> ValSymbol (SymValDefine f)) _)) = f
unsafeToDefine v = error ("LLVM.Analysis.ClassHierarchy.unsafeToDefine: Expected vtable function entry: " ++ show v)

-- TODO I added a case for bitcasts here, reevalutate!
isVTableFunctionType :: Value -> Bool
isVTableFunctionType (valValue -> ValSymbol (SymValDefine _)) = True
isVTableFunctionType (valValue -> ValConstExpr (ConstConv BitCast (valValue -> ValSymbol (SymValDefine _)) _)) = True
isVTableFunctionType _ = False

recordTypeInfo :: CHA -> Name -> Maybe Value -> CHA
recordTypeInfo cha _ Nothing = cha
recordTypeInfo cha name (Just (valValue -> ValStruct vs _)) =
  let parentClassNames = mapMaybe toParentClassName vs
  in cha { parentMap = MS.insertWith S.union name (S.fromList parentClassNames) (parentMap cha)
         , childrenMap = foldr (addChild name) (childrenMap cha) parentClassNames
         }
recordTypeInfo _ _ (Just tbl) = error ("LLVM.Analysis.ClassHierarchy.recordTypeInfo: Expected typeinfo literal " ++ show tbl)

toParentClassName :: Value -> Maybe Name
toParentClassName (valValue -> ValConstExpr (ConstConv BitCast (valValue -> ValSymbol (SymValGlobal Global {globalName=Symbol gvn})) _)) =
      case demangleName gvn of
        Left _ -> Nothing
        Right (TypeInfo (ClassEnumType n)) -> Just n
        _ -> Nothing
toParentClassName _ = Nothing

addChild :: Name -> Name -> Map Name (Set Name) -> Map Name (Set Name)
addChild thisType parentType =
  MS.insertWith S.union parentType (S.singleton thisType)

constructedType :: Define -> Type
constructedType f =
  case map argType $ defArgs f of
    PtrTo t@(Struct (Right _) _ _) : _ -> t
    t -> error ("LLVM.Analysis.ClassHierarchy.constructedType: Expected pointer to struct type: " ++ show t)

-- Helpers

-- | Determine if the given function is a C2 constructor or not.  C1
-- and C3 don't give us the information we want, so ignore them
isC2Constructor :: Define -> Bool
isC2Constructor f =
  case dname of
    Left _ -> False
    Right structuredName ->
      case universeBi structuredName of
        [C2] -> True
        _ -> False
  where
    Symbol n = defName f
    dname = demangleName n

-- | Strip a prefix, operating as the identity if the input string did
-- not have the prefix.
stripPrefix' :: String -> String -> String
stripPrefix' pfx s = fromMaybe s (stripPrefix pfx s)

stripNamePrefix :: String -> String
stripNamePrefix =
  stripPrefix' "struct." . stripPrefix' "class."

typeToName :: Type -> Name
typeToName (Opaque (Right (Ident n))) = typeToName' n
typeToName (Struct (Right (Ident n)) _ _) = typeToName' n
typeToName t = error ("LLVM.Analysis.ClassHierarchy.typeToName: Expected named struct or opaque type, got: " ++ show t)

typeToName' :: String -> Name
typeToName' n =
  case parseTypeName (stripNamePrefix n) of
    Right tn -> tn
    Left e -> error ("LLVM.Analysis.ClassHierarchy.typeToName: " ++ e)

nameToString :: Name -> String
nameToString n = fromMaybe errMsg (unparseTypeName n)
  where
    errMsg = error ("Could not encode name as string: " ++ show n)

nameToType :: CHA -> Name -> Type
nameToType cha n = M.findWithDefault errMsg n (typeMapping cha)
  where
    errMsg = error ("Expected name in typeMapping for CHA: " ++ show n)

namesToTypes :: CHA -> Set Name -> [Type]
namesToTypes cha = map (nameToType cha) . toList


-- Testing

classHierarchyToTestFormat :: CHA -> Map String (Set String)
classHierarchyToTestFormat cha =
  foldr mapify mempty (M.toList (childrenMap cha))
  where
    mapify (ty, subtypes) =
      let ss = S.map nameToString subtypes
      in M.insertWith S.union (nameToString ty) ss

{-# ANN module "HLint: ignore Use if" #-}
