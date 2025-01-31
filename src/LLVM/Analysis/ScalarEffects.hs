{-# LANGUAGE ViewPatterns, NoMonomorphismRestriction #-}
{-|

This analysis identifies the (memory) effects that functions have on
the scalar components of their arguments.

Only pointer parameters are interesting because only their effects can
escape the callee.  Effects are currently restricted to increments and
decrements of integral types.  The affected memory can be a struct
member; the effects are described in terms of abstract AccessPaths.

This is a must analysis.  Effects are only reported if they *MUST*
occur (modulo non-termination style effects like calls to exit or
infinite loops).

Currently, sequential effects are not composed and nothing useful will
be reported.

-}
module LLVM.Analysis.ScalarEffects (
  ScalarEffectResult,
  ScalarEffect(..),
  scalarEffectAnalysis
  ) where

import Control.DeepSeq
import Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as HM

import LLVM.Analysis
import LLVM.Analysis.AccessPath
import LLVM.Analysis.CFG
import LLVM.Analysis.Dataflow

-- | The types of effects tracked by this analysis.  This can be expanded
-- as the analysis becomes more sophisticated (it could include general
-- affine relations or even relate arguments to each other).
data ScalarEffect = EffectAdd1 AbstractAccessPath
                  | EffectSub1 AbstractAccessPath
                  deriving (Eq)

instance NFData ScalarEffect where
  rnf e@(EffectAdd1 ap) = ap `deepseq` e `seq` ()
  rnf e@(EffectSub1 ap) = ap `deepseq` e `seq` ()

type ScalarEffectResult = HashMap Argument ScalarEffect

data ScalarInfo = SI (HashMap Argument (Maybe ScalarEffect))
                | SITop

instance Eq ScalarInfo where
  (SI s1) == (SI s2) = s1 == s2
  SITop == SITop = True
  _ == _ = False

meet :: ScalarInfo -> ScalarInfo -> ScalarInfo
meet SITop s = s
meet s SITop = s
meet (SI s1) (SI s2) = SI (HM.unionWith mergeEffect s1 s2)
  where
    -- | If there is an entry in both maps, it must be the same to be
    -- retained.
    mergeEffect e1 e2 = if e1 == e2 then e1 else Nothing

-- For each function, initialize all arguments to Nothing
scalarEffectAnalysis :: (Monad m, HasCFG funcLike, HasDefine funcLike)
                        => funcLike
                        -> ScalarEffectResult
                        -> m ScalarEffectResult
scalarEffectAnalysis funcLike summ = do
  let cfg = getCFG funcLike
      analysis = fwdDataflowAnalysis SITop meet scalarTransfer

  localRes <- dataflow cfg analysis SITop
  let xi = case dataflowResult localRes of
        SITop -> HM.empty
        SI m -> HM.foldlWithKey' discardNothings HM.empty m
  return $! HM.union xi summ

discardNothings :: HashMap Argument ScalarEffect
                   -> Argument
                   -> Maybe ScalarEffect
                   -> HashMap Argument ScalarEffect
discardNothings acc _ Nothing = acc
discardNothings acc a (Just e) = HM.insert a e acc

scalarTransfer :: (Monad m) => ScalarInfo -> Stmt -> m ScalarInfo
scalarTransfer si i =
  case stmtInstr i of
    AtomicRW _ AtomicAdd _ (valValue -> ValInteger 1) _ _ ->
      recordIfAffectsArgument EffectAdd1 i si
    AtomicRW _ AtomicAdd _ (valValue -> ValInteger (-1)) _ _ ->
      recordIfAffectsArgument EffectSub1 i si
    AtomicRW _ AtomicSub _ (valValue -> ValInteger 1) _ _ ->
      recordIfAffectsArgument EffectSub1 i si
    AtomicRW _ AtomicSub _ (valValue -> ValInteger (-1)) _ _ ->
      recordIfAffectsArgument EffectAdd1 i si
    Store sv sa _ _
      | isNonAtomicAdd sa sv -> recordIfAffectsArgument EffectAdd1 i si
      | isNonAtomicSub sa sv -> recordIfAffectsArgument EffectSub1 i si
    _ -> return si

isNonAtomicSub :: (IsValue a) => Value -> a -> Bool
isNonAtomicSub sa sv =
  case toValue sv of
    ValInstr (Arith Sub {}
      (valValue -> ValInteger (-1))
      (ValInstr (Load la _ _))) ->
      sa == la
    ValInstr (Arith Sub {}
      (ValInstr (Load la _ _))
      (valValue -> ValInteger (-1))) ->
      sa == la
    ValInstr (Arith Add {}
      (ValInstr (Load la _ _))
      (valValue -> ValInteger 1)) ->
      sa == la
    _ -> False

isNonAtomicAdd :: (IsValue a) => Value -> a -> Bool
isNonAtomicAdd sa sv =
  case toValue sv of
    ValInstr (Arith Add {}
      (valValue -> ValInteger 1)
      (ValInstr (Load la _ _))) ->
      sa == la
    ValInstr (Arith Add {}
      (ValInstr (Load la _ _))
      (valValue -> ValInteger 1)) ->
      sa == la
    ValInstr (Arith Sub {}
      (ValInstr (Load la _ _))
      (valValue -> ValInteger (-1))) ->
      sa == la
    _ -> False

recordIfAffectsArgument :: (Monad m)
                           => (AbstractAccessPath -> ScalarEffect)
                           -> Stmt
                           -> ScalarInfo
                           -> m ScalarInfo
recordIfAffectsArgument con i si =
  case accessPath i of
    Nothing -> return si
    Just cap ->
      case valValue (accessPathBaseValue cap) of
        ValIdent (IdentValArgument a) ->
          let e = Just $ con (abstractAccessPath cap)
          in case si of
            SITop -> return $! SI $ HM.insert a e HM.empty
            SI m -> return $! SI $ HM.insert a e m
        _ -> return si

{-# ANN module "HLint: ignore Use if" #-}
