module Data.LLVM.CFG ( CFG
                     , EdgeCondition(..)
                     , makeCFG
                     ) where

import Data.List (foldl')
import Data.Graph.Inductive
import Data.GraphViz
import Data.Map ((!))
import qualified Data.Map as M

import Data.LLVM.Private.Printers ( )
import Data.LLVM.Private.ReferentialTypes

import Debug.Trace

debug = flip trace

type CFG = Gr Value EdgeCondition

data EdgeCondition = UnconditionalEdge
                   | DefaultEdge
                   | TrueEdge Value
                   | FalseEdge Value
                   | EqualityEdge Value Value
                   | IndirectEdge Value
                   deriving (Ord, Eq)

instance Show EdgeCondition where
  show UnconditionalEdge = ""
  show DefaultEdge = "<default>"
  show (TrueEdge v) = {- show v ++ -}" is true"
  show (FalseEdge v) = {- show v ++ -} " is false"
  show (EqualityEdge v1 v2) = "is" -- concat [ show v1, " is ", show v2 ]
  show (IndirectEdge v) = show v ++ " (indirect)"

-- | Each instruction in the function body is a node in the graph.
-- Branching instructions induce edges.  This form of the CFG is
-- fine-grained in that each instruction has its own CFG node.  This
-- is simpler to analyze, generally.
--
-- The other function, makeCompactCFG, has a basic-block-granularity
-- CFG that can be easier to visualize.
makeCFG :: Value -> CFG
makeCFG func = mkGraph (cfgNodes `debug` ("nnodes = " ++ show cfgNodes)) $ concat (cfgEdges `debug` ("nedges: " ++ show (take 4 cfgEdges)))
  where body = functionBody $ valueContent func
        allInstructions = concatMap (\(Value { valueContent = BasicBlock is }) -> is) body
        (nodeCount, nodeIDs) = foldl' labelInstruction (0, M.empty) allInstructions
        labelInstruction (idx, m) val = (idx+1, M.insert val idx m)
        (cfgNodes, cfgEdges) = foldl' buildGraphBlock ([], []) (body `debug` ("Blocks: " ++ show (length body)))

        instIdent :: Value -> Int
        instIdent v = nodeIDs ! v
        jumpTargetId :: Value -> Int
        jumpTargetId Value { valueContent = BasicBlock (t:_) } = instIdent (t `debug` ("Target for jump: " ++ show (instIdent t)))
        jumpTargetId v = error $ "Value is not a basic block: " ++ show v

        caseEdge thisNodeId cond (val, dest) =
          (thisNodeId, jumpTargetId dest, EqualityEdge cond val)
        indirectEdge thisNodeId addr target =
          (thisNodeId, jumpTargetId target, IndirectEdge addr)
        buildGraphBlock acc Value { valueContent = BasicBlock allInsts@(_:insts) } =
          (foldl' buildGraphInst acc instsAndSuccs) `debug` ("Insts and succs: " ++ show instsAndSuccs)
          where instsAndSuccs = if null insts
                                then terminator
                                else offsetPairs ++ terminator
                offsetPairs = zip allInsts $ map Just insts
                terminator = [(last allInsts, Nothing)]
        buildGraphBlock _ v = error $ "Not a BasicBlock: " ++ show v
        buildGraphInst acc (v@Value { valueContent = c }, Nothing) =
          (nodeAcc', edgeAcc') `debug` ("Built edges for terminator (" ++ show theseEdges ++ ")")
          where (nodeAcc, edgeAcc) = acc
                nodeAcc' = thisNode : nodeAcc
                edgeAcc' = theseEdges : edgeAcc
                thisNodeId = instIdent v
                thisNode = (thisNodeId, v) `debug` ("Trying to build terminator inst edges: " ++ show v)
                -- Note: branch targets are all basic blocks.  The
                -- lookup function handles grabbing the first real
                -- instruction from the basic block.
                theseEdges = case c `debug` ("Switching on " ++ show v) of
                  -- Returns have no intraprocedural edges
                  RetInst _ -> []
                  -- Unwinds also have no intraprocedural edges
                  UnwindInst -> []
                  -- A single target (no label needed)
                  UnconditionalBranchInst tgt ->
                    [ (thisNodeId, jumpTargetId tgt, UnconditionalEdge) ]
                  -- Two edges (cond is true, cond is false)
                  BranchInst { branchCondition = cond
                             , branchTrueTarget = tTarget
                             , branchFalseTarget = fTarget
                             } ->
                    [ (thisNodeId, jumpTargetId tTarget `debug` ("true edge "), UnconditionalEdge) -- TrueEdge cond)
                    , (thisNodeId, jumpTargetId fTarget `debug` "false edge", UnconditionalEdge) -- FalseEdge cond)
                    ]
                  SwitchInst { switchValue = cond
                             , switchDefaultTarget = defTarget
                             , switchCases = cases
                             } ->
                    ( thisNodeId
                    , jumpTargetId defTarget
                    , DefaultEdge) : map (caseEdge thisNodeId cond) cases
                  IndirectBranchInst { indirectBranchAddress = addr
                                     , indirectBranchTargets = targets
                                     } ->
                    map (indirectEdge thisNodeId addr) targets
                  _ -> error ("Last instruction in a block should be a jump: " ++ show v)
        buildGraphInst acc (v@Value { valueContent = c }, Just successor) =
          (nodeAcc', edgeAcc') `debug` ("Built edges for " ++ show v)
          where (nodeAcc, edgeAcc) = acc
                nodeAcc' = thisNode : nodeAcc
                edgeAcc' = theseEdges : edgeAcc
                thisNodeId = instIdent v
                thisNode = (thisNodeId, v) `debug` ("A node: " ++ show v)
                theseEdges = case c of
                  Function {} -> error "Functions should not be in the CFG"
                  GlobalDeclaration {} -> error "Globals should not be in the CFG"
                  GlobalAlias {} -> error "Global aliases should not be in the CFG"
                  ExternalValue -> error "External values should not be in the CFG"
                  ExternalFunction _ -> error "External functions should not be in the CFG"
                  BasicBlock _ -> error "Basic blocks should not be in the CFG"
                  Argument _ -> error "Arguments should not be in the CFG"
                  _ -> [(thisNodeId, instIdent successor, UnconditionalEdge)]