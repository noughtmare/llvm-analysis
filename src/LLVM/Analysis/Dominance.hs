-- | Tools to compute dominance information for functions.  Includes
-- postdominators.
--
-- A node @m@ postdominates a node @n@ iff every path from @n@ to
-- @exit@ passes through @m@.
--
-- This implementation is based on the dominator implementation in fgl,
-- which is based on the algorithm from Cooper, Harvey, and Kennedy:
--
--   http://www.cs.rice.edu/~keith/Embed/dom.pdf
module LLVM.Analysis.Dominance (
  -- * Types
  DominatorTree,
  PostdominatorTree,
  HasDomTree(..),
  HasPostdomTree(..),
  -- * Constructors
  dominatorTree,
  postdominatorTree,
  -- * Queries
  dominates,
  postdominates,
  postdominators,
  postdominatorsFor,
  immediatePostdominators,
  immediatePostdominator,
  ) where

import Control.Arrow ( (&&&) )
import Control.Monad.Identity
import qualified Data.Foldable as F
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Maybe ( fromMaybe )
import Data.Monoid
import Data.Set ( Set )
import qualified Data.Set as S
import Data.GraphViz

import LLVM.Analysis
import LLVM.Analysis.CFG
import LLVM.Analysis.Dataflow

-- import qualified Text.PrettyPrint.GenericPretty as PP
-- import Debug.Trace
-- debug = flip trace

data DominatorTree = DT CFG (Map Instruction Instruction)

class HasDomTree a where
  getDomTree :: a -> DominatorTree

instance HasDomTree DominatorTree where
  getDomTree = id

-- | Note, this instance constructs the dominator tree and could be
-- expensive
instance HasDomTree CFG where
  getDomTree = dominatorTree

instance HasCFG DominatorTree where
  getCFG (DT cfg _) = cfg

instance HasFunction DominatorTree where
  getFunction = getFunction . getCFG

-- | Construct a DominatorTree from something that behaves like a
-- control flow graph.
dominatorTree :: (HasCFG cfg) => cfg -> DominatorTree
dominatorTree f = DT cfg (toImmediateDominators doms)
  where
    cfg = getCFG f
    doms = dominatorAnalysis cfg

-- | Check whether n dominates m
dominates :: (HasDomTree t) => t -> Instruction -> Instruction -> Bool
dominates dt n m = checkDom m
  where
    (DT _ t) = getDomTree dt
    -- Walk backwards in the dominator tree looking for n
    checkDom i
      | i == n = True
      | otherwise = maybe False checkDom (M.lookup i t)

data PostdominatorTree = PDT CFG (Map Instruction Instruction)

class HasPostdomTree a where
  getPostdomTree :: a -> PostdominatorTree

-- | Note that this instance constructs the postdominator tree from
-- scratch.
instance HasPostdomTree CFG where
  getPostdomTree = postdominatorTree

instance HasPostdomTree PostdominatorTree where
  getPostdomTree = id

instance HasCFG PostdominatorTree where
  getCFG (PDT cfg _) = cfg

instance HasFunction PostdominatorTree where
  getFunction = getFunction . getCFG

-- | Construct a PostdominatorTree from something that behaves like a
-- control flow graph.
postdominatorTree :: (HasCFG f) => f -> PostdominatorTree
postdominatorTree f = PDT cfg (toImmediateDominators pdoms)
  where
    cfg = getCFG f
    pdoms = postdominatorAnalysis cfg

-- | Tests whether or not an Instruction n postdominates Instruction m
postdominates :: (HasPostdomTree t) => t -> Instruction -> Instruction -> Bool
postdominates pdt n m = checkPDom m
  where
    PDT _ t = getPostdomTree pdt
    checkPDom i
      | i == n = True
      | otherwise = maybe False checkPDom (M.lookup i t)

postdominators :: (HasPostdomTree t) => t -> [(Instruction, [Instruction])]
postdominators pt =
  zip is (map (getDominators t) is)
  where
    pdt@(PDT _ t) = getPostdomTree pt
    f = getFunction pdt
    is = functionInstructions f

postdominatorsFor :: (HasPostdomTree t) => t -> Instruction -> [Instruction]
postdominatorsFor pt = getDominators t
  where
    PDT _ t = getPostdomTree pt

immediatePostdominator :: (HasPostdomTree t) => t -> Maybe Instruction
immediatePostdominator = undefined

immediatePostdominators :: (HasPostdomTree t) => t -> [(Instruction, Instruction)]
immediatePostdominators = undefined

-- | Return the dominators (or postdominators) of the given
-- instruction, in order (with the nearest dominators at the beginning
-- of the list).  Note that the instruction iself is not included
-- (every instruction trivially dominates itself).
getDominators :: Map Instruction Instruction
                     -> Instruction
                     -> [Instruction]
getDominators m = go
  where
    go i =
      case M.lookup i m of
        Nothing -> []
        Just dom -> dom : go dom

-- Internal builder code


type Fact = Set Instruction

domAnalysis :: (Monad m) => Fact -> DataflowAnalysis m Fact
domAnalysis top = dataflowAnalysis top meet transfer
  where
    meet = S.intersection
    transfer doms i = return (S.insert i doms)

-- | Compute the set of dominators for each instruction in the CFG.
--
-- This is a simple dataflow analysis where top is the universal set
-- (all instructions in the function) and meet is set intersection.
-- The transfer function simply adds the current instruction to the
-- dataflow fact.
dominatorAnalysis :: CFG -> Map Instruction (Set Instruction)
dominatorAnalysis cfg = foldr (addInstFact dfr) mempty allInsts
  where
    s0 = S.singleton entryInst
    top = S.fromList allInsts
    allInsts@(entryInst:_)= functionInstructions (getFunction cfg)
    analysis = domAnalysis top
    dfr = runIdentity $ forwardDataflow cfg analysis s0

addInstFact :: DataflowResult Identity a
               -> Instruction
               -> Map Instruction a
               -> Map Instruction a
addInstFact dfr i acc =
  let f = runIdentity (dataflowResultAt dfr i)
  in M.insert i f acc

-- | In this case, we don't have an instruction that is a unique exit
-- point.  However, we know perfectly well that the virtual exit node
-- in the CFG postdominates everything so there isn't much need to
-- explicitly track that.
--
-- Thus, we start off with the empty set in the beginning.
--
-- Everything should actually remain the same here, despite this,
-- since users can't query based on the virtual exit node anyway.
postdominatorAnalysis :: CFG -> Map Instruction (Set Instruction)
postdominatorAnalysis cfg = foldr (addInstFact dfr) mempty allInsts
  where
    s0 = S.empty
    top = S.fromList allInsts
    allInsts = functionInstructions (getFunction cfg)
    analysis = domAnalysis top
    dfr = runIdentity $ backwardDataflow cfg analysis s0

-- | Compute the immediate dominators from the set of all dominators.
-- The entry instruction is not in the map because it has no immediate
-- dominator.
--
-- m `idom` n  IFF  m `sdom` n  AND  (p sdom n => p dom m)
toImmediateDominators :: Map Instruction (Set Instruction) -> Map Instruction Instruction
toImmediateDominators allDoms =
  foldr (addIdom allDoms) mempty $ M.toList allDoms

-- | Find m such that, for each node p in sdom n, p must also be in
-- dom[m]
addIdom :: Map Instruction (Set Instruction)
           -> (Instruction, Set Instruction)
           -> Map Instruction Instruction
           -> Map Instruction Instruction
addIdom allDoms (n, doms) acc =
  fromMaybe acc $ do
    m <- F.find tryOneM sdoms
    return $ M.insert n m acc
  where
    sdoms = S.delete n doms
    -- The immediate dominator of a node strictly dominates that node
    -- but does not strictly dominate any other node in dom[n].
    tryOneM m =
      -- Return True if m is not in sdom[x] for x in sdoms
      F.all (notInSDoms m) sdoms
    notInSDoms m d =
      let Just ddom = M.lookup d allDoms
          sddom = S.delete d ddom
      in not (S.member m sddom)


-- Visualization
domTreeParams :: GraphvizParams n Instruction el () Instruction
domTreeParams =
  nonClusteredParams { fmtNode = \(_, l) -> [ toLabel (toValue l) ] }

treeToGraphviz :: CFG -> Map Instruction Instruction -> DotGraph Int
treeToGraphviz cfg t = graphElemsToDot domTreeParams ns es
  where
    f = getFunction cfg
    is = functionInstructions f
    ns = map (instructionUniqueId &&& id) is
    es = foldr toDomEdge [] is

    toDomEdge i acc =
      case M.lookup i t of
        Nothing -> acc
        Just d ->
          (instructionUniqueId i, instructionUniqueId d, ()) : acc

instance ToGraphviz DominatorTree where
  toGraphviz (DT cfg t) = treeToGraphviz cfg t

instance ToGraphviz PostdominatorTree where
  toGraphviz (PDT cfg t) = treeToGraphviz cfg t

{-# ANN module "HLint: ignore Use if" #-}
