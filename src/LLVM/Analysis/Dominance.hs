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
  dominators,
  dominatorsFor,
  immediateDominatorFor,
  immediateDominators,
  postdominates,
  postdominators,
  postdominatorsFor,
  immediatePostdominatorFor,
  immediatePostdominators
  ) where

import Control.Arrow ( (&&&) )
import qualified Data.Graph.Inductive.Graph as G
import qualified Data.Graph.Inductive.Basic as G
import qualified Data.Graph.Inductive.PatriciaTree as G
import qualified Data.Graph.Inductive.Query.Dominators as G
import Data.IntMap ( IntMap )
import qualified Data.IntMap as IM
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Maybe ( fromMaybe )
import Data.Monoid
import Data.GraphViz

import LLVM.Analysis
import LLVM.Analysis.CFG

-- import qualified Text.PrettyPrint.GenericPretty as PP
-- import Debug.Trace
-- debug = flip trace

data DominatorTree = DT CFG (Map Stmt Stmt)

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

instance HasDefine DominatorTree where
  getDefine = getDefine . getCFG

-- | Construct a DominatorTree from something that behaves like a
-- control flow graph.
dominatorTree :: (HasCFG cfg) => cfg -> DominatorTree
dominatorTree f = DT cfg idomMap
  where
    cfg = getCFG f
    (g, revmap) = cfgToGraph cfg
    idoms = G.iDom g (stmtUniqueId entryInst)
    idomMap = foldr (remapInst revmap) mempty idoms
    -- to make the rooted graph, we don't need any extra nodes here -
    -- just pull out the entry instruction
    entryBlock : _ = defBody (getDefine cfg)
    entryInst : _ = bbStmts entryBlock

immediateDominatorFor :: (HasDomTree t) => t -> Stmt -> Maybe Stmt
immediateDominatorFor dt i = M.lookup i t
  where
    DT _ t = getDomTree dt

immediateDominators :: (HasDomTree t) => t -> [(Stmt, Stmt)]
immediateDominators dt = M.toList t
  where
    DT _ t = getDomTree dt

-- | Check whether n dominates m
dominates :: (HasDomTree t) => t -> Stmt -> Stmt -> Bool
dominates dt n = checkDom
  where
    (DT _ t) = getDomTree dt
    -- Walk backwards in the dominator tree looking for n
    checkDom i
      | i == n = True
      | otherwise = maybe False checkDom (M.lookup i t)

dominators :: (HasDomTree t) => t -> [(Stmt, [Stmt])]
dominators pt =
  zip is (map (getDominators t) is)
  where
    dt@(DT _ t) = getDomTree pt
    f = getDefine dt
    is = defStmts f

dominatorsFor :: (HasDomTree t) => t -> Stmt -> [Stmt]
dominatorsFor pt = getDominators t
  where
    DT _ t = getDomTree pt


data PostdominatorTree = PDT CFG (Map Stmt Stmt)

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

instance HasDefine PostdominatorTree where
  getDefine = getDefine . getCFG

-- | Construct a PostdominatorTree from something that behaves like a
-- control flow graph.
postdominatorTree :: (HasCFG f) => f -> PostdominatorTree
postdominatorTree f = PDT cfg idomMap
  where
    cfg = getCFG f
    (g, revmap) = cfgToGraph cfg
    idoms = G.iDom (G.grev g) (-1)
    idomMap = foldr (remapInst revmap) mempty idoms
    -- To make the rooted graph here, we need to add a virtual exit
    -- node.  Also note that we reverse the edges in the graph because
    -- this is a postdominator tree.

remapInst :: (Ord a) => IntMap a -> (Int, Int) -> Map a a -> Map a a
remapInst revmap (n, d) acc = fromMaybe acc $ do
  nI <- IM.lookup n revmap
  dI <- IM.lookup d revmap
  return $ M.insert nI dI acc

immediatePostdominatorFor :: (HasPostdomTree t) => t -> Stmt -> Maybe Stmt
immediatePostdominatorFor pt i = M.lookup i t
  where
    PDT _ t = getPostdomTree pt

immediatePostdominators :: (HasPostdomTree t) => t -> [(Stmt, Stmt)]
immediatePostdominators pt = M.toList t
  where
    PDT _ t = getPostdomTree pt

-- | Tests whether or not an Stmt n postdominates Stmt m
postdominates :: (HasPostdomTree t) => t -> Stmt -> Stmt -> Bool
postdominates pdt n = checkPDom
  where
    PDT _ t = getPostdomTree pdt
    checkPDom i
      | i == n = True
      | otherwise = maybe False checkPDom (M.lookup i t)

postdominators :: (HasPostdomTree t) => t -> [(Stmt, [Stmt])]
postdominators pt =
  zip is (map (getDominators t) is)
  where
    pdt@(PDT _ t) = getPostdomTree pt
    f = getDefine pdt
    is = defStmts f

postdominatorsFor :: (HasPostdomTree t) => t -> Stmt -> [Stmt]
postdominatorsFor pt = getDominators t
  where
    PDT _ t = getPostdomTree pt

-- | Return the dominators (or postdominators) of the given
-- instruction, in order (with the nearest dominators at the beginning
-- of the list).  Note that the instruction iself is not included
-- (every instruction trivially dominates itself).
getDominators :: Map Stmt Stmt
                     -> Stmt
                     -> [Stmt]
getDominators m = go
  where
    go i =
      case M.lookup i m of
        Nothing -> []
        Just dom -> dom : go dom

-- Internal

-- | Convert the nice CFG to a less nice Graph format; this is a
-- linear process.  We'll then pass this new graph to dom-lt to
-- compute immediate dominators for us efficiently.
--
-- IDs will be Stmt UniqueIds, and the root will be the ID of
-- the entry instruction.
cfgToGraph :: CFG -> (G.Gr () (), IntMap Stmt)
cfgToGraph cfg = (G.mkGraph ns es, revMap)
  where
    f = getDefine cfg
    blocks = defBody f
    is = defStmts f
    revMap = foldr (\i -> IM.insert (stmtUniqueId i) i) mempty is
    -- Make sure we add the virtual exit node
    ns = (-1, ()) : map (\i -> (stmtUniqueId i, ())) is
    es = concatMap (blockEdges cfg) blocks

-- | Construct all of the edges internal to a basic block, as well as
-- the edges from the terminator instruction to its successors.  If
-- the terminator has no successors (it is an exit instruction), give
-- it a virtual edge to -1.
blockEdges :: (HasCFG cfg) => cfg -> BasicBlock -> [(UniqueId, UniqueId, ())]
blockEdges cfg b =
  addSuccessorEdges internalEdges
  where
    mkEdge s d = (s, d, ())
    is = map stmtUniqueId $ bbStmts b
    ti = stmtUniqueId $ bbTerminatorStmt b
    succs = map blockEntryId $ basicBlockSuccessors cfg b
    internalEdges = zipWith mkEdge is (tail is)
    -- If we have successors, do the sensible thing.  If we don't have
    -- successors, add an edge from ti -> -1 (a virtual catchall
    -- exit),
    addSuccessorEdges a
      | null succs = mkEdge ti (-1) : a
      | otherwise = map (mkEdge ti) succs ++ a

blockEntryId :: BasicBlock -> UniqueId
blockEntryId bb = stmtUniqueId ei
  where
    ei : _ = bbStmts bb


-- Visualization
-- domTreeParams :: GraphvizParams n Stmt el () Stmt
-- domTreeParams =
--   nonClusteredParams { fmtNode = \(_, l) -> [ toLabel (toValue l) ] }
-- 
-- treeToGraphviz :: CFG -> Map Stmt Stmt -> DotGraph Int
-- treeToGraphviz cfg t = graphElemsToDot domTreeParams ns es
--   where
--     f = getDefine cfg
--     is = defStmts f
--     ns = map (stmtUniqueId &&& id) is
--     es = foldr toDomEdge [] is
-- 
--     toDomEdge i acc =
--       case M.lookup i t of
--         Nothing -> acc
--         Just d ->
--           (stmtUniqueId i, stmtUniqueId d, ()) : acc
-- 
-- instance ToGraphviz DominatorTree where
--   toGraphviz (DT cfg t) = treeToGraphviz cfg t
-- 
-- instance ToGraphviz PostdominatorTree where
--   toGraphviz (PDT cfg t) = treeToGraphviz cfg t
-- 
-- {-# ANN module "HLint: ignore Use if" #-}
