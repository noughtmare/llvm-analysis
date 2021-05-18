module LLVM.Analysis.UsesOf (
  UseSummary,
  computeUsesOf,
  usedBy
  ) where

import qualified Data.Foldable as F
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import Data.Map.Strict (Map)
import Data.Maybe ( fromMaybe )

import LLVM.Analysis

newtype UseSummary = UseSummary (Map Value [Stmt])

-- | Compute the uses of every value in the 'Module'
--
-- This information can be used to answer the query:
--
-- > usedBy useSummary foo
--
-- which will return all of the Instructions that reference
-- the provided value @foo@.
--
-- Note that this is a simple index.  It does not look through bitcasts
-- at all.
computeUsesOf :: Module -> UseSummary
computeUsesOf m = UseSummary $ fmap S.toList uses
  where
    uses = F.foldl' funcUses M.empty fs
    fs = modDefines m
    funcUses acc f = F.foldl' addInstUses acc (defStmts f)
    addInstUses acc i = F.foldl' (addUses i) acc (instructionOperands (stmtInstr i))
    addUses i acc v = M.insertWith S.union v (S.singleton i) acc

-- | > usedBy summ val
--
-- Find the instructions using @val@ in the function that @summ@ was
-- computed for.
usedBy :: UseSummary -> Value -> [Stmt]
usedBy (UseSummary m) v = fromMaybe [] $ M.lookup v m
