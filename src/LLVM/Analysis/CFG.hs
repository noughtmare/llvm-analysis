{-# LANGUAGE ExistentialQuantification, TemplateHaskell #-}
-- | This module defines control flow graphs over the LLVM IR.
module LLVM.Analysis.CFG (
  -- * Types
  CFG(..),
  RCFG(..),
  CFGEdge(..),
  CFGType,
  HasCFG(..),
  -- * Constructors
  mkCFG,
  reverseCFG,
  -- * Accessors
  basicBlockPredecessors,
  basicBlockSuccessors,
  basicBlockPredecessorEdges,
  basicBlockSuccessorEdges,
  basicBlockLabeledPredecessors,
  basicBlockLabeledSuccessors,
  instructionReachable,
  -- * Visualization
  cfgGraphvizRepr
  ) where

import Data.GraphViz
import Data.List ( foldl' )
import Debug.Trace.LocationTH
import Text.Printf

import Data.Graph.Interface
import Data.Graph.LazyHAMT
import Data.Graph.Algorithms.Basic

import LLVM.Analysis
import LLVM.Analysis.Types

type CFGType = Gr Instruction CFGEdge
type LEdgeType = LEdge CFGType
type NodeType = Node CFGType
type LNodeType = LNode CFGType

instance Labellable CFGEdge where
  toLabelValue = toLabelValue . show

-- | The control flow graph representation
data CFG = CFG { cfgGraph :: CFGType
               , cfgEntryValue :: Instruction
               , cfgEntryNode :: NodeType
               , cfgExitValue :: Instruction
               , cfgExitNode :: NodeType
               , cfgFunction :: Function
               }

-- | The control flow graph with the edges reversed
data RCFG = RCFG { rcfgGraph :: CFGType
                 , rcfgEntryValue :: Instruction
                 , rcfgEntryNode :: NodeType
                 , rcfgExitValue :: Instruction
                 , rcfgExitNode :: NodeType
                 , rcfgFunction :: Function
                 }

-- | The types of edges that appear in the 'CFG'
data CFGEdge =
  UnconditionalEdge
  -- ^ An unconditional jump from somewhere
  | DefaultEdge
    -- ^ A default jump due to a case statement
  | TrueEdge Value
    -- ^ True edge successor for the comparison contained in the
    -- value.  This value was the argument to the branch instruction.
  | FalseEdge Value
    -- ^ False edge successor for the comparison contained in the
    -- value.  This value was the argument to a branch instruction.
  | EqualityEdge Value Value
    -- ^ A case equality edge (the case value v1 was equal to val v2)
  | IndirectEdge Value
    -- ^ Jump from the given indirect branch value
  | NormalEdge Instruction
    -- ^ The normal return from an invoke
  | UnwindEdge Instruction
    -- ^ Exceptional return from an invoke
  deriving (Ord, Eq)

instance Show CFGEdge where
  show UnconditionalEdge = ""
  show DefaultEdge = "<default>"
  show (TrueEdge v) = printf "[%s] is true" (show v)
  show (FalseEdge v) = printf "[%s] is false" (show v)
  show (EqualityEdge v1 v2) = printf "[%s] is [%s]" (show v1) (show v2)
  show (IndirectEdge v) = printf "[%s] (indirect)" (show v)
  show (NormalEdge i) = printf "[%s] (invoke normal)" (show i)
  show (UnwindEdge i) = printf "[%s] (invoke unwind)" (show i)

-- | Types that have control flow graphs.
class HasCFG a where
  getCFG :: a -> CFG

instance HasCFG CFG where
  getCFG = id

instance HasCFG Function where
  getCFG = mkCFG

instance HasFunction CFG where
  getFunction = cfgFunction

instance HasFunction RCFG where
  getFunction = rcfgFunction

instance FuncLike CFG where
  fromFunction = mkCFG

-- | Build a control flow graph for the given function.  Each
-- instruction in the function body is a node in the graph.  Branching
-- instructions induce edges.  This form of the CFG is fine-grained in
-- that each instruction has its own CFG node.
--
-- The other function, 'mkCompactCFG', has a basic-block-granularity
-- CFG that can be easier to visualize.
mkCFG :: Function -> CFG
mkCFG func = CFG { cfgGraph = g
                 , cfgFunction = func
                 , cfgEntryValue = entryVal
                 , cfgEntryNode = instructionUniqueId entryVal
                 , cfgExitValue = exitVal
                 , cfgExitNode = instructionUniqueId exitVal
                 }
  where
    entryVal = functionEntryInstruction func
    exitVal = functionExitInstruction func

    g = mkGraph cfgNodes (concat cfgEdges)
    (cfgNodes, cfgEdges) = foldl' buildBlockGraph ([], []) (functionBody func)

reverseCFG :: CFG -> RCFG
reverseCFG g = RCFG { rcfgGraph = grev (cfgGraph g)
                    , rcfgFunction = cfgFunction g
                    , rcfgEntryValue = cfgExitValue g
                    , rcfgEntryNode = cfgExitNode g
                    , rcfgExitValue = cfgEntryValue g
                    , rcfgExitNode = cfgEntryNode g
                    }

callEdgeNStub :: a -> Maybe b
callEdgeNStub _ = Nothing

-- | Build the local control flow nodes and edges for the given
-- 'Function'.  The nodes and edges are placed on the front of the
-- input lists.
--
-- Note: This function is only exposed to make the ICFG construction
-- more efficient without copying code.
-- buildLocalGraph :: (LEdgeType -> LEdge a)        -- ^ A function to convert CFG edges to another type of edge
--                    -> (LEdgeType -> LEdge a)     -- ^ A function to convert a CFG edge from a Call or Invoke to another type of edge
--                    -> (Instruction -> Maybe (LNode a)) -- ^ A function to generate an extra node from a Call or Invoke edge
--                    -> (LNodeType -> LNode a) -- ^ A function to convert CFG nodes to another type of node
--                    -> (Instruction -> [LEdge a])     -- ^ A function to apply to Call and Invoke instructions to generate extra edges
--                    -> Function                      -- ^ The current function
--                    -> ([LNode a], [LEdge a])        -- ^ Accumulator
--                    -> ([LNode a], [LEdge a])
-- buildLocalGraph edgeF callEdgeF callEdgeN nodeF callF f acc =
--   foldr (buildBlockGraph edgeF callEdgeF callEdgeN nodeF callF) acc (functionBody f)

-- buildBlockGraph :: (LEdgeType -> LEdge a)        -- ^ A function to convert CFG edges to another type of edge
--                    -> (LEdgeType -> LEdge a)     -- ^ A function to convert a CFG edge from a Call or Invoke to another type of edge
--                    -> (Instruction -> Maybe (LNode a)) -- ^ A function to generate an extra node from a Call or Invoke edge
--                    -> (LNodeType -> LNode a) -- ^ A function to convert CFG nodes to another type of node
--                    -> (Instruction -> [LEdge a])     -- ^ A function to apply to Call and Invoke instructions to generate extra edges
--                    -> BasicBlock
--                    -> ([LNode a], [LEdge a])
--                    -> ([LNode a], [LEdge a])
-- buildBlockGraph edgeF callEdgeF callEdgeN nodeF callF bb acc =
--   foldr (buildGraphInst edgeF callEdgeF callEdgeN nodeF callF) acc instsAndSuccessors
--   where
--     blockInsts = basicBlockInstructions bb
--     (_:successors) = blockInsts
--     instsAndSuccessors = case null successors of
--       True -> terminator
--       False -> offsetPairs ++ terminator
--     offsetPairs = zip blockInsts $ map Just successors
--     terminator = [(last blockInsts, Nothing)]

toInternalEdge :: (Instruction, Instruction) -> LEdge CFGType
toInternalEdge (s, d) = LEdge (Edge sid did) UnconditionalEdge
  where
    sid = instructionUniqueId s
    did = instructionUniqueId d

buildBlockGraph :: ([LNodeType], [[LEdgeType]]) -> BasicBlock -> ([LNodeType], [[LEdgeType]])
buildBlockGraph (nacc, eacc) bb = (newNodes ++ nacc, concat [termEdges, internalEdges] :eacc)
  where
    blockInsts = basicBlockInstructions bb
    newNodes = map (\i -> LNode (instructionUniqueId i) i) blockInsts
    termInst = basicBlockTerminatorInstruction bb
    termNodeId = instructionUniqueId termInst
    otherInsts = filter (/= termInst) blockInsts
    internalEdgePairings = case null otherInsts of
      True -> []
      False -> zip blockInsts (tail blockInsts)

    internalEdges = map toInternalEdge internalEdgePairings

    -- FIXME: Examine call instructions to pick out calls to the
    -- libstdc++ unwind function, which marks the end of control flow
    -- in a function... that said, calls to __cxa_throw are properly
    -- marked as not returning (and are followed by the unreachable
    -- instruction), so maybe no special handling is required at the
    -- intraprocedural level.  This will still be important for
    -- interprocedural analyses, though.
    termEdges = case termInst of
      -- Returns have no intraprocedural edges
      RetInst {} -> []
      -- A single target (no label needed)
      UnconditionalBranchInst { unconditionalBranchTarget = tgt } ->
        [ LEdge (Edge termNodeId (jumpTargetId tgt)) UnconditionalEdge ]
      -- Two edges (cond is true, cond is false)
      BranchInst { branchCondition = cond
                 , branchTrueTarget = tTarget
                 , branchFalseTarget = fTarget
                 } ->
        [ LEdge (Edge termNodeId (jumpTargetId tTarget)) (TrueEdge cond)
        , LEdge (Edge termNodeId (jumpTargetId fTarget)) (FalseEdge cond)
        ]
      SwitchInst { switchValue = cond
                 , switchDefaultTarget = defTarget
                 , switchCases = cases
                 } ->
        LEdge (Edge termNodeId (jumpTargetId defTarget)) DefaultEdge :
        map (caseEdge termNodeId cond) cases
      IndirectBranchInst { indirectBranchAddress = addr
                         , indirectBranchTargets = targets
                         } ->
        map (indirectEdge termNodeId addr) targets
      InvokeInst { invokeNormalLabel = n
                 , invokeUnwindLabel = u
                 } ->
        [ LEdge (Edge termNodeId (jumpTargetId n)) (NormalEdge termInst)
        , LEdge (Edge termNodeId (jumpTargetId u)) (UnwindEdge termInst)
        ]
      -- No code after unreachable instructions is executed
      UnreachableInst {} -> []
      -- The resume instruction resumes propagating exceptions, so
      -- control will transfer to the caller.  In theory, another
      -- handler in the same function could pick it up...  Resolving
      -- that might require some more sophisticated analysis.
      ResumeInst {} -> []
      _ -> $failure ("Last instruction in a block should be a terminator: " ++ show (toValue termInst))


-- buildGraph :: ([LNodeType], [[LEdgeType]]) -> Instruction -> ([LNodeType], [[LEdgeType]])
-- buildGraph (nacc, eacc) i = (thisNode : nacc, theseEdges : eacc)
--   where
--     thisNode = LNode (instructionUniqueId i) i
--     theseEdges = case inst of
--       -- Returns have no intraprocedural edges
--       RetInst {} -> []
--       -- Unwinds also have no intraprocedural edges
--       UnwindInst {} -> []
--       -- A single target (no label needed)
--       UnconditionalBranchInst { unconditionalBranchTarget = tgt } ->
--         [ LEdge (Edge thisNodeId (jumpTargetId tgt)) UnconditionalEdge ]
--       -- Two edges (cond is true, cond is false)
--       BranchInst { branchCondition = cond
--                  , branchTrueTarget = tTarget
--                  , branchFalseTarget = fTarget
--                  } ->
--         [ LEdge (Edge thisNodeId (jumpTargetId tTarget)) (TrueEdge cond)
--         , LEdge (Edge thisNodeId (jumpTargetId fTarget)) (FalseEdge cond)
--         ]
--       SwitchInst { switchValue = cond
--                  , switchDefaultTarget = defTarget
--                  , switchCases = cases
--                  } ->
--         LEdge (Edge thisNodeId (jumpTargetId defTarget)) DefaultEdge :
--         map (caseEdge thisNodeId cond) cases
--       IndirectBranchInst { indirectBranchAddress = addr
--                          , indirectBranchTargets = targets
--                          } ->
--         map (indirectEdge thisNodeId addr) targets
--       InvokeInst { invokeNormalLabel = n
--                  , invokeUnwindLabel = u
--                  } ->
--         [ LEdge (Edge thisNodeId (jumpTargetId n)) (NormalEdge inst)
--         , LEdge (Edge thisNodeId (jumpTargetId u)) (UnwindEdge inst)
--         ]
--       -- No code after unreachable instructions is executed
--       UnreachableInst {} -> []
--       -- The resume instruction resumes propagating exceptions, so
--       -- control will transfer to the caller.  In theory, another
--       -- handler in the same function could pick it up...  Resolving
--       -- that might require some more sophisticated analysis.
--       ResumeInst {} -> []
--       _ -> $failure ("Last instruction in a block should be a terminator: " ++ show (Value inst))

-- buildGraphInst :: (LEdgeType -> LEdge a)        -- ^ A function to convert CFG edges to another type of edge
--                   -> (LEdgeType -> LEdge a)     -- ^ A function to convert a CFG edge from a Call or Invoke to another type of edge
--                   -> (Instruction -> Maybe (LNode a)) -- ^ A function to generate an extra node from a Call or Invoke edge
--                   -> (LNodeType -> LNode a) -- ^ A function to convert CFG nodes to another type of node
--                   -> (Instruction -> [LEdge a])     -- ^ A function to apply to Call and Invoke instructions to generate extra edges
--                   -> (Instruction, Maybe Instruction)    -- ^ Current instruction and successor (if any)
--                   -> ([LNode a], [LEdge a])        -- ^ Accumulator
--                   -> ([LNode a], [LEdge a])
-- buildGraphInst edgeF callEdgeF callEdgeN nodeF callF (inst, Nothing) (nodeAcc, edgeAcc) =
--    -- Note, when adding the edges, put the accumulator second in the
--    -- list append so that only the short list (new edges) needs to be
--    -- reallocated
--   case (callEdgeN inst, inst) of
--     (Just en, InvokeInst { }) -> (nodeF thisNode : en : nodeAcc, allEdges ++ edgeAcc)
--     _ -> (nodeF thisNode : nodeAcc, allEdges ++ edgeAcc)
--   where
--     thisNodeId = instructionUniqueId inst
--     thisNode = LNode thisNodeId inst
--     allEdges = case inst of
--       InvokeInst { } -> callF inst ++ map callEdgeF theseEdges
--       _ -> map edgeF theseEdges

--     -- Note: branch targets are all basic blocks.  The
--     -- lookup function handles grabbing the first real
--     -- instruction from the basic block.
--     theseEdges = case inst of
--       -- Returns have no intraprocedural edges
--       RetInst {} -> []
--       -- Unwinds also have no intraprocedural edges
--       UnwindInst {} -> []
--       -- A single target (no label needed)
--       UnconditionalBranchInst { unconditionalBranchTarget = tgt } ->
--         [ LEdge (Edge thisNodeId (jumpTargetId tgt)) UnconditionalEdge ]
--       -- Two edges (cond is true, cond is false)
--       BranchInst { branchCondition = cond
--                  , branchTrueTarget = tTarget
--                  , branchFalseTarget = fTarget
--                  } ->
--         [ LEdge (Edge thisNodeId (jumpTargetId tTarget)) (TrueEdge cond)
--         , LEdge (Edge thisNodeId (jumpTargetId fTarget)) (FalseEdge cond)
--         ]
--       SwitchInst { switchValue = cond
--                  , switchDefaultTarget = defTarget
--                  , switchCases = cases
--                  } ->
--         LEdge (Edge thisNodeId (jumpTargetId defTarget)) DefaultEdge :
--         map (caseEdge thisNodeId cond) cases
--       IndirectBranchInst { indirectBranchAddress = addr
--                          , indirectBranchTargets = targets
--                          } ->
--         map (indirectEdge thisNodeId addr) targets
--       InvokeInst { invokeNormalLabel = n
--                  , invokeUnwindLabel = u
--                  } ->
--         [ LEdge (Edge thisNodeId (jumpTargetId n)) (NormalEdge inst)
--         , LEdge (Edge thisNodeId (jumpTargetId u)) (UnwindEdge inst)
--         ]
--       -- No code after unreachable instructions is executed
--       UnreachableInst {} -> []
--       -- The resume instruction resumes propagating exceptions, so
--       -- control will transfer to the caller.  In theory, another
--       -- handler in the same function could pick it up...  Resolving
--       -- that might require some more sophisticated analysis.
--       ResumeInst {} -> []
--       _ -> $failure ("Last instruction in a block should be a terminator: " ++ show (Value inst))
-- buildGraphInst edgeF callEdgeF callEdgeN nodeF callF (inst, Just successor) (nodeAcc, edgeAcc) =
--   case (callEdgeN inst, inst) of
--     (Just en, CallInst { }) -> (nodeF thisNode : en : nodeAcc, theseEdges ++ edgeAcc)
--     _ -> (nodeF thisNode : nodeAcc, theseEdges ++ edgeAcc)
--   where
--     thisNodeId = instructionUniqueId inst
--     thisNode = LNode thisNodeId inst
--     thisEdge = LEdge (Edge thisNodeId (instructionUniqueId successor)) UnconditionalEdge
--     theseEdges = case inst of
--       CallInst { } -> callEdgeF thisEdge : callF inst
--       _ -> [edgeF thisEdge]

-- | Only BasicBlocks are targets of jumps.  This function finds the
-- identifier for the given block.
jumpTargetId :: BasicBlock -> Int
jumpTargetId bb = instructionUniqueId t
  where
    (t:_) = basicBlockInstructions bb

caseEdge :: NodeType -> Value -> (Value, BasicBlock) -> LEdgeType
caseEdge thisNodeId cond (val, dest) =
  LEdge (Edge thisNodeId (jumpTargetId dest)) (EqualityEdge cond val)

indirectEdge :: NodeType -> Value -> BasicBlock -> LEdgeType
indirectEdge thisNodeId addr target =
  LEdge (Edge thisNodeId (jumpTargetId target)) (IndirectEdge addr)

{-# INLINE toBlock #-}
toBlock :: CFGType -> NodeType -> BasicBlock
toBlock cfg n =
  case lab cfg n of
    Nothing -> $failure ("Instruction missing from CFG: " ++ show n)
    Just i ->
      case instructionBasicBlock i of
        Nothing -> $failure ("Instruction in CFG should have a basic block: " ++ show i)
        Just b -> b

{-# INLINE toInstruction #-}
toInstruction :: CFG -> NodeType -> Instruction
toInstruction cfg nod =
  case lab (cfgGraph cfg) nod of
    Just v -> v
    Nothing -> $failure ("No value for cfg node: " ++ show nod)

-- | Get all of the predecessor blocks for basic block @bb@
--
-- > basicBlockPredecessors cfg bb
basicBlockPredecessors :: CFG -> BasicBlock -> [BasicBlock]
basicBlockPredecessors cfg bb = map (toBlock cfg') ps
  where
    cfg' = cfgGraph cfg
    firstInst : _ = basicBlockInstructions bb
    ps = pre cfg' (instructionUniqueId firstInst)

-- | Get all of the successor blocks for basic block @bb@
--
-- > basicBlockSuccessors cfg bb
basicBlockSuccessors :: CFG -> BasicBlock -> [BasicBlock]
basicBlockSuccessors cfg bb = map (toBlock cfg') ss
  where
    cfg' = cfgGraph cfg
    exitInst = basicBlockTerminatorInstruction bb
    ss = suc cfg' (instructionUniqueId exitInst)

basicBlockPredecessorEdges :: CFG -> BasicBlock -> [CFGEdge]
basicBlockPredecessorEdges cfg bb =
  map edgeLabel $ linn (cfgGraph cfg) (instructionUniqueId startInst)
  where
    startInst : _ = basicBlockInstructions bb

basicBlockSuccessorEdges :: CFG -> BasicBlock -> [CFGEdge]
basicBlockSuccessorEdges cfg bb =
  map edgeLabel $ lout (cfgGraph cfg) (instructionUniqueId exitInst)
  where
    exitInst = basicBlockTerminatorInstruction bb

basicBlockLabeledSuccessors :: CFG -> BasicBlock -> [(BasicBlock, CFGEdge)]
basicBlockLabeledSuccessors cfg bb =
  map (\(n, l) -> (toBlock cfg' n, l)) ss
  where
    cfg' = cfgGraph cfg
    exitInst = basicBlockTerminatorInstruction bb
    ss = lsuc cfg' (instructionUniqueId exitInst)

basicBlockLabeledPredecessors :: CFG -> BasicBlock -> [(BasicBlock, CFGEdge)]
basicBlockLabeledPredecessors cfg bb =
  map (\(n, l) -> (toBlock cfg' n, l)) ps
  where
    cfg' = cfgGraph cfg
    startInst : _ = basicBlockInstructions bb
    ps = lpre cfg' (instructionUniqueId startInst)

-- | An instruction is reachable if its basic block has predecessors
-- *OR* (if there are no predecessors) it is the first basic block.
instructionReachable :: CFG -> Instruction -> Bool
instructionReachable cfg i =
  case null (basicBlockPredecessors cfg bb) of
    True -> bb == firstBlock
    False -> True
  where
    Just bb = instructionBasicBlock i
    f = basicBlockFunction bb
    firstBlock : _ = functionBody f


-- Visualization

cfgGraphvizParams :: GraphvizParams n Instruction CFGEdge BasicBlock Instruction
cfgGraphvizParams =
  nonClusteredParams { fmtNode = \(_,l) -> [toLabel (toValue l)]
                     , fmtEdge = formatEdge
                     , clusterID = Int . basicBlockUniqueId
                     , fmtCluster = formatCluster
                     , clusterBy = nodeCluster
                     }
  where
    nodeCluster l@(_, i) =
      let Just bb = instructionBasicBlock i
      in C bb (N l)
    formatCluster bb = [GraphAttrs [toLabel (show (basicBlockName bb))]]
    formatEdge (_, _, l) =
      let lbl = toLabel l
      in case l of
        TrueEdge _ -> [lbl, color ForestGreen]
        FalseEdge _ -> [lbl, color Crimson]
        EqualityEdge _ _ -> [lbl, color DeepSkyBlue]
        IndirectEdge _ -> [lbl, color Indigo, style dashed]
        UnwindEdge _ -> [lbl, color Tomato4, style dotted]
        _ -> [lbl]

cfgGraphvizRepr :: CFG -> DotGraph NodeType
cfgGraphvizRepr cfg = graphElemsToDot cfgGraphvizParams ns es
  where
    g = cfgGraph cfg
    ns = map toNodeTuple (labNodes g)
    es = map toEdgeTuple (labEdges g)
