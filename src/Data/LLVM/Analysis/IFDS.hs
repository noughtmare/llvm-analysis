{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}
module Data.LLVM.Analysis.IFDS (
  IFDSAnalysis(..),
  ifds
  ) where

import Data.Graph.Inductive hiding ( (><) )
import Data.List ( foldl' )
import Data.Map ( Map )
import Data.Sequence ( Seq, ViewL(..), (|>), viewl )
import Data.Set ( Set )
import qualified Data.Map as M
import qualified Data.Sequence as Seq
import qualified Data.Set as S

import Text.Printf

import Data.LLVM
import Data.LLVM.CFG
import Data.LLVM.ICFG

type Worklist a = Seq (PathEdge a)

-- | The interface to define an IFDS analysis.  There are variants of
-- the interprocedural flow functions to handle /external/ functions.
-- Known references are provided for known external functions.
-- Unknown functions can be called in Modules that do not have a
-- 'main' function or when they contain calls to dlopen.
class IFDSAnalysis a domType where
  flow :: a -> Maybe domType -> Instruction -> [CFGEdge] -> [Maybe domType]
  -- ^ Compute local flow information for the domain element after this
  -- instruction is executed.  The returned list is the list of domain
  -- variables reachable from this domain element after the statement is
  -- executed.  This models local control flow.
  callFlow :: a -> Maybe domType -> Instruction -> [Maybe domType]
  -- ^ Similar to 'flow', but models local information flow across
  -- call->return edges.
  passArgs :: a -> Maybe domType -> Instruction -> [Maybe domType]
  returnVal :: a -> Maybe domType -> Instruction -> [Maybe domType]
  externReturnVal :: a -> Maybe domType -> Maybe ExternalFunction -> [Maybe domType]
  -- ^ 'retVal' for external functions.  The external function is
  -- 'Nothing' when the return is from an unknown external function.
  analysisBandwidth :: a -> Int


-- | An edge from <s_p, d_1> to <n, d_2> noting that <n, d_2> is
-- reachable in the exploded supergraph from <s_p, d_1>.  s_p is not
-- explicitly recorded because it is uniquely determined by n.
data PathEdge domType = PathEdge !(Maybe domType) !Node !(Maybe domType)
                      deriving (Ord, Eq)

-- After the analysis is done, reduce the Set PathEdge -> Map (Node,
-- domType) [domType] to start answering queries.  Really, only the
-- second two members are useful (reachable vs not reachable).

-- | An edge summarizing the flow information for the call site
-- identified by the node.
data SummaryEdge domType = SummaryEdge !Node !(Maybe domType) !(Maybe domType)
                           deriving (Ord, Eq)

data IFDSNode domType = IFDSNode !Node !(Maybe domType)
                        deriving (Ord, Eq)

data IFDS domType = IFDS { pathEdges :: Set (PathEdge domType)
                           -- ^ The PathEdge set from the algorithm
                         , summaryEdges :: Set (SummaryEdge domType)
                           -- ^ The SummaryEdge set from the algorithm
                         , incomingNodes :: Map (IFDSNode domType) (Set (IFDSNode domType))
                           -- ^ A reverse mapping.  This maps G#
                           -- (exploded supergraph) nodes
                           -- corresponding to function entries to the
                           -- calls that induce them.
                         , endSummary :: Map (IFDSNode domType) (Set (IFDSNode domType))
                         , entryValues :: Map Node (Set (Maybe domType))
                           -- ^ A cache of domain elements reachable
                           -- at the entry node of a procedure (the
                           -- key in the set is the entry node of the
                           -- function)
                         , summaryValues :: Map Node (Set (Maybe domType))
                           -- ^ A cache of domain elements at the
                           -- target of a summary edge.  This lets us
                           -- implement the second query at line 17
                           -- efficiently
                         , worklist :: Worklist domType
                           -- ^ A simple worklist
                         , icfg :: ICFG
                           -- ^ The ICFG that this analysis is operating on
                         }

ifds :: (IFDSAnalysis a domType, Ord domType) => a -> ICFG -> Set (PathEdge domType)
ifds analysis g =
  tabulate analysis IFDS { pathEdges = S.fromList initialEdges
                         , summaryEdges = S.empty
                         , worklist = Seq.fromList initialEdges
                         , incomingNodes = M.empty
                         , endSummary = M.empty
                         , entryValues = M.empty
                         , summaryValues = M.empty
                         , icfg = g
                         }
  where
    initialEdges = map mkInitialEdge (icfgEntryPoints g)

tabulate :: (IFDSAnalysis a domType, Ord domType)
            => a
            -> IFDS domType
            -> Set (PathEdge domType)
tabulate analysis currentState = case viewl (worklist currentState) of
  EmptyL -> pathEdges currentState
  -- Grab an edge off of the worklist and dispatch to the correct case
  e@(PathEdge _{-d1-} n _{-d2-}) :< rest ->
    let nextState = currentState { worklist = rest }
        Just lbl = lab ((icfgGraph . icfg) currentState) n
    in case lbl of
      -- Case 1 of the algorithm (call nodes)
      InstNode ci@CallInst { } -> addCallEdges ci e analysis nextState
      InstNode ii@InvokeInst { } -> addCallEdges ii e analysis nextState


      -- Case 2 of the algorithm (return nodes)
      ExternalExit (Just ef) -> tabulate analysis nextState
      InstNode ri@RetInst { } -> addExitEdges ri e analysis nextState
      -- Slightly special subcase - will see about how to handle unknown functions
      ExternalExit Nothing -> tabulate analysis nextState


      -- Case 3 of the algorithm (intraprocedural information flow)
      InstNode i -> addIntraEdges i e analysis nextState
      -- FIXME: Handle the case of ExternalEntry?


-- | Handle adding edges for function call instructions (and invokes).
-- This function covers lines 14-19 in the algorithm from Naeem et al
addCallEdges :: (IFDSAnalysis a domType, Ord domType)
                => Instruction
                -> PathEdge domType
                -> a
                -> IFDS domType
                -> Set (PathEdge domType)
addCallEdges ci (PathEdge d1 n d2) analysis currentState =
  tabulate analysis nextState
  where
    callEntryNodes = getICFGCallEntries (icfg currentState) n
    nextState = foldl' edgesForCallee currentState callEntryNodes

    -- | Need to add edges for all possible callees (the original RHS
    -- algorithm only handles single-target calls)
    edgesForCallee s calledProcEntry =
      -- This handles lines 17-19 (propagating edges)
      foldl' extendCallToReturn summEdgeState d3s
      where
        argEdges = passArgs analysis d2 ci
        summEdgeState = foldl' (edgesForCalleeWithValue calledProcEntry) s argEdges
        -- ^ This is the block from 14-16 in the algorithm.
        d3s = concat [ callFlow analysis d2 ci
                     , filter isInSummaryEdge $ S.toList (maybe S.empty id (M.lookup n (summaryValues currentState)))
                     ]
        isInSummaryEdge d3 = S.member (SummaryEdge n d2 d3) (summaryEdges currentState)

    -- | This is lines 15, 15.1 (add <n,d2> to Incoming) and the loop
    -- following them, which adds summary edges.
    edgesForCalleeWithValue calledProcEntry s argEdge =
      S.fold addSummaries s' callerExits
      where
        s' = addIncomingNode (propagate s loop) entryNode callNode
        -- ^ This propagate call (embedded in the incoming node
        -- addition) is line 15 of the algorithm
        loop = PathEdge argEdge calledProcEntry argEdge
        entryNode = IFDSNode calledProcEntry argEdge
        callNode = IFDSNode n d2
        callerExits = maybe S.empty id $ M.lookup entryNode (endSummary s')

    -- | The inner loop (line 15.3-15.5) adds some summary edges
    addSummaries {-callerExit@-}(IFDSNode e_p d4) s =
      foldl' addSummaryEdge s summEdges
      where
        -- FIXME: Here we could call an alternate returnVal function
        -- for externals (when retInst is not actually an instruction)
        -- rvs = returnVal analysis d4 retInst
        -- Just (InstNode retInst) = lab ((icfgGraph . icfg) currentState) e_p
        Just exitNode = lab ((icfgGraph . icfg) currentState) e_p
        rvs = case exitNode of
          InstNode retInst -> returnVal analysis d4 retInst
          ExternalExit ef -> externReturnVal analysis d4 ef
        summEdges = map (\d5 -> SummaryEdge n d2 d5) rvs

    -- | Obviously, propagates the reachability of <s_p,d1> to
    -- <return(n),d3>.  Less obviously, cache the fact that d1 reaches
    -- a call in this function.  This is an overapproximation of the
    -- information we need later, but we can filter out excess
    -- information then by checking to see if the edge from d1 to d3
    -- is actually in PathEdge.
    --
    -- FIXME could make this more precise by making the key be the call?
    extendCallToReturn s d3 =
      let s' = propagate s (PathEdge d1 (callNodeToReturnNode n) d3)
          callerEntryNode = nodeToFunctionEntryNode (icfg s) n
          newEntryVals = case M.lookup callerEntryNode (entryValues s) of
            Nothing -> S.singleton d1
            Just vs -> S.insert d1 vs
      in s' { entryValues = M.insert callerEntryNode newEntryVals (entryValues s') }
{-# INLINE addCallEdges #-}

addIncomingNode :: (Ord domType)
                   => IFDS domType
                   -> IFDSNode domType
                   -> IFDSNode domType
                   -> IFDS domType
addIncomingNode s entryNode callNode =
  s { incomingNodes = updatedNodes }
  where
    currentNodes = incomingNodes s
    updatedNodes = case M.lookup entryNode currentNodes of
      Nothing -> M.insert entryNode (S.singleton callNode) currentNodes
      Just ns -> M.insert entryNode (S.insert callNode ns) currentNodes
{-# INLINE addIncomingNode #-}

getICFGCallEntries :: ICFG -> Node -> [Node]
getICFGCallEntries g n = map fst $ filter (isCallToEntry . snd) $ lsuc (icfgGraph g) n
{-# INLINE getICFGCallEntries #-}

isCallToEntry :: ICFGEdge -> Bool
isCallToEntry (CallToEntry _) = True
isCallToEntry _ = False

{-
data IFDS domType = IFDS { pathEdges :: Set (PathEdge domType)
                         , summaryEdges :: Set (SummaryEdge domType)
                         , incomingEdges :: Map (IFDSNode domType) (Set (IFDSNode domType))
                         , worklist :: Worklist domType
                         }

-}

-- | Handle case 2 of the algorithm: function exit nodes (e_p, d_2).
-- This function adds a summary edge in the caller and adds propagates
-- local information in the caller along call-to-return edges.
--
-- A lot of the work actually happens in 'summarizeCallEdge', which is
-- broken out just because it was getting large.  Hopefully the
-- inliner will take care of pasting everything back together for
-- additional optimization.
--
-- Note: n is e_p in the algorithm
addExitEdges :: (IFDSAnalysis a domType, Ord domType)
                => Instruction
                -> PathEdge domType
                -> a
                -> IFDS domType
                -> Set (PathEdge domType)
addExitEdges ri (PathEdge d1 n d2) analysis currentState =
  tabulate analysis nextState { endSummary = nextEndSummary }
  where
    e_p = n
    s_p = nodeToFunctionEntryNode (icfg currentState) e_p

    funcEntry = IFDSNode s_p d1
    funcExit = IFDSNode e_p d2

    retEdges = returnVal analysis d2 ri

    currentEndSummary = endSummary currentState
    updatedEndSummary =
      maybe (S.singleton funcExit) (S.insert funcExit) $
        M.lookup funcEntry currentEndSummary
    nextEndSummary = M.insert funcEntry updatedEndSummary currentEndSummary
    -- ^ Add a node to the EndSummary set saying that <e_p, d_2> is an
    -- exit node for <s_p,d_1>.

    callEdges = maybe S.empty id $ M.lookup funcEntry (incomingNodes currentState)
    -- ^ These edges (memoized since we can't compute the inverse flow
    -- function) are edges from call nodes to the beginning of this
    -- function.

    nextState = S.fold (summarizeCallEdge retEdges) currentState callEdges
    -- ^ Insert summary edges for the call edge now that we have
    -- reached the end of this function.
{-# INLINE addExitEdges #-}

-- | Insert a summary edge in the caller for this call edge.
--
--  From the algorithm:
--
-- > foreach d_5 in retVal
summarizeCallEdge :: (Ord domType)
                     => [Maybe domType]
                     -- ^ Edges from the ret node back to the caller
                     -> IFDSNode domType
                     -- ^ Call node
                     -> IFDS domType
                     -> IFDS domType
summarizeCallEdge retEdges (IFDSNode c d4) currentState =
  foldl' mkSummaryEdges currentState retEdges
  where
    -- | d5 is one of the values that d4 maps to from the return node
    -- This function makes the summary edges and propagates local
    -- information in the caller along call-to-return edges.
    mkSummaryEdges s d5 = case S.member summEdge (summaryEdges s) of
      True -> s -- Already have summary edge, can skip doing any work here
      False -> S.fold addCallToReturns s' entVals -- Note, state here includes the summary edge
      where
        summEdge = SummaryEdge c d4 d5
        s' = addSummaryEdge s summEdge
        callerEntryNode = nodeToFunctionEntryNode (icfg currentState) c

        entVals = maybe S.empty id (M.lookup callerEntryNode (entryValues currentState))
        -- ^ These are a superset of the d3s on line 26.
        -- 'addCallToReturns' filters out the values where there is
        -- not an edge in PathEdge.

        addCallToReturns d3 summState =
          let e1 = PathEdge d3 c d4
              callToReturnEdge = PathEdge d3 (callNodeToReturnNode c) d5
          in case S.member e1 (pathEdges summState) of
            -- This case statement is the condition check in line 26,
            -- ensuring that this d3 actually produces an edge in
            -- PathEdge
            False -> summState
            True -> propagate summState callToReturnEdge
{-# INLINE summarizeCallEdge #-}

callNodeToReturnNode :: Node -> Node
callNodeToReturnNode = negate
{-# INLINE callNodeToReturnNode #-}

-- | Given a node in the ICFG corresponding to some instruction, find
-- the entry node for the function containing it.
nodeToFunctionEntryNode :: ICFG -> Node -> Node
nodeToFunctionEntryNode g n = instructionUniqueId s
  where
    Just (InstNode i) = lab (icfgGraph g) n
    Just bb = instructionBasicBlock i
    f = basicBlockFunction bb
    s = functionEntryInstruction f
{-# INLINE nodeToFunctionEntryNode #-}

-- | Handle the case of local control flow (extending the
-- intraprocedural part of the exploded supergraph).
addIntraEdges :: (IFDSAnalysis a domType, Ord domType)
                 => Instruction
                 -> PathEdge domType
                 -> a
                 -> IFDS domType
                 -> Set (PathEdge domType)
addIntraEdges i (PathEdge d1 n d2) analysis currentState =
  tabulate analysis (foldl' propagate currentState newEdges)
  where
    g = (icfgGraph . icfg) currentState
    currentEdges = pathEdges currentState

    dests = flow analysis d2 i intraPredEdges
    intraPredEdges = map (toIntraEdge . snd) $ lpre g n

    intraSuccessors = suc g n
    inducedEdges = concatMap (mkIntraEdge dests) intraSuccessors
    newEdges = filter (not . (flip S.member) currentEdges) inducedEdges
    -- ^ Only keep the edges that are not already known

    mkIntraEdge ipes successor = map (\d3 -> PathEdge d1 successor d3) ipes
{-# INLINE addIntraEdges #-}

{-# INLINE toIntraEdge #-}
toIntraEdge :: ICFGEdge -> CFGEdge
toIntraEdge (IntraEdge e) = e

{-# INLINE propagate #-}
propagate :: (Ord domType) => IFDS domType -> PathEdge domType -> IFDS domType
propagate s newEdge = s { pathEdges = newEdge `S.insert` currentEdges
                         , worklist = worklist s |> newEdge
                         }
  where
    currentEdges = pathEdges s

-- FIXME: Populate the exitValues cache here iff the path edge
-- involves a call node?

{-# INLINE addSummaryEdge #-}
addSummaryEdge :: (Ord domType) => IFDS domType -> SummaryEdge domType -> IFDS domType
addSummaryEdge state se@(SummaryEdge callNode _ d') =
  state { summaryEdges = S.insert se (summaryEdges state)
        , summaryValues = M.insert callNode updatedCache (summaryValues state)
        }
  where
    updatedCache = case M.lookup callNode (summaryValues state) of
      Nothing -> S.singleton d'
      Just s -> S.insert d' s

-- | Build a self loop on the special "null" element for the given
-- entry point
mkInitialEdge :: Function -> PathEdge domType
mkInitialEdge f = PathEdge Nothing (instructionUniqueId inst0) Nothing
  where
    inst0 = functionEntryInstruction f


{-

For the main switch statement, there are three cases:

 * Call node

   Can distinguish these InstNodes because it will always be a call or
   invoke instruction

 * Exit node

   These will always be ret instructions

 * Everything else


The current function is always accessible in constant time because any
instruction has constant-time access to its enclosing function.
Matching edges is a simple equality test on the set of all outgoing
edges from ret nodes.

Don't bother building any of the exploded supergraph explicitly.  Just
keep a Set of the PathEdges.  Reachability queries are then of the form:

  S.member (s_p, nodeid) pathEdge

For nodeid in procedure p.

-}