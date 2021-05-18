{-# LANGUAGE ViewPatterns #-}
-- | This module implements a trivial points-to analysis that is
-- intended only for fast conservative callgraph construction.  All
-- function pointers can point to all functions with compatible types.
--
-- Other pointers are considered to alias if they are of the same
-- type.  The 'pointsTo' function only returns empty sets for
-- non-function pointers.
module LLVM.Analysis.PointsTo.TrivialFunction (
  -- * Types
  TrivialFunction,
  -- * Constructor
  runPointsToAnalysis
  ) where

import Data.HashMap.Strict ( HashMap )
import Data.Set ( Set )
import qualified Data.HashMap.Strict as M
import qualified Data.Set as S

import LLVM.Analysis
import LLVM.Analysis.PointsTo
import LLVM.Analysis (IsValue (..))

-- | The result of the TrivialFunction points-to analysis.  It is an
-- instance of the 'PointsToAnalysis' typeclass and is intended to be
-- queried through that interface.
--
-- Again, note that this analysis is not precise (just fast) and does
-- not provide points-to sets for non-function types.  It provides
-- only type-based answers and does not respect typecasts at all.
newtype TrivialFunction = TrivialFunction (HashMap Type (Set Value))

instance PointsToAnalysis TrivialFunction where
  mayAlias = trivialMayAlias
  pointsTo = trivialPointsTo

-- | Run the points-to analysis and return its results in an opaque
-- handle.
runPointsToAnalysis :: Module -> TrivialFunction
runPointsToAnalysis m = TrivialFunction finalMap
  where
    externMap = foldr buildMap M.empty (modDeclares m)
    finalMap = foldr buildMap externMap (modDefines m)

-- | Add function-typed values to the result map.
buildMap :: (IsValue a) => a -> HashMap Type (Set Value) -> HashMap Type (Set Value)
buildMap v =
  M.insertWith S.union vtype (S.singleton (toValue v))
  where
    vtype = valType (toValue v)

trivialMayAlias :: TrivialFunction -> Value -> Value -> Bool
trivialMayAlias _ v1 v2 = valType v1 == valType v2

-- Note, don't use the bitcast stripping functions here since we need
-- the surface types of functions.  This affects cases where function
-- pointers are stored generically in a struct and then taken out and
-- casted back to their original type.
trivialPointsTo :: TrivialFunction -> Value -> [Value]
trivialPointsTo p@(TrivialFunction m) v =
  case v of
    (valValue -> ValSymbol SymValDefine {}) -> [v]
    (valValue -> ValSymbol SymValDeclare {}) -> [v]
    (valValue -> ValSymbol (SymValAlias ga)) -> trivialPointsTo p (toValue ga)
    ValInstr (Conv BitCast c _) ->
      case c of
        (valValue -> ValSymbol SymValDefine {}) -> trivialPointsTo p c
        (valValue -> ValSymbol SymValDeclare {}) -> trivialPointsTo p c
        (valValue -> ValSymbol SymValAlias {}) -> trivialPointsTo p c
        _ -> S.toList $ M.lookupDefault S.empty (derefPointer v) m
    _ -> S.toList $ M.lookupDefault S.empty (derefPointer v) m

derefPointer :: Value -> Type
derefPointer v = case valType v of
  PtrTo p -> p
  _ -> error ("LLVM.Analysis.PointsTo.TrivialPointer.derefPointer: Non-pointer type given to trivalPointsTo: " ++ show v)
