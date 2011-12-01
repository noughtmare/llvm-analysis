-- | This module implements the compositional pointer/escape analysis
-- described by Whaley and Rinard (http://doi.acm.org/10.1145/320384.320400).
--
-- This version is adapted to the LLVM IR (originally for Java).
--
-- Each program variable has a VariableNode to enable lookups easily
-- during the analysis (the ID in the graph is the ID of the LLVM IR
-- object).  Each VariableNode has a corresponding location that it
-- represents (either an internal node or an external node).  The
-- types of each node correspond to those in the bitcode.  The
-- location node for a VariableNode has an ID that is the negated ID
-- of the corresponding name.
--
-- Memoize the representative field GEP for each operation by caching
-- the deduced value in the EscapeGraph structure.
--
-- Add a sequence number to the EscapeGraph and increment it whenever
-- edges are added or removed.  This should make graph equality tests
-- much faster.
module Data.LLVM.Analysis.Escape (
  -- * Types
  EscapeResult,
  EscapeGraph(..),
  EscapeNode(..),
  EscapeEdge(..),
  PTEGraph,
  -- * Functions
  runEscapeAnalysis,
  escapeGraphAtLocation,
  pointsTo,
  -- * Debugging
  viewEscapeGraph
  ) where

import Algebra.Lattice
import Data.Graph.Inductive hiding ( Gr )
import Data.GraphViz
import Data.List ( foldl', mapAccumR )
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Set ( Set, (\\) )
import qualified Data.Set as S

import Data.LLVM
import Data.LLVM.CFG
import Data.LLVM.Analysis.Dataflow
import Data.LLVM.Internal.PatriciaTree

-- | The types of nodes in the graph
data EscapeNode = VariableNode !Value
                | OParameterNode !Value
                | OGlobalNode !Value
                | OReturnNode !Value
                | INode !Value -- Allocas and allocators
                | IVirtual !Value
                deriving (Eq, Ord)

-- | Edges labels for the points-to escape graph.  These differentiate
-- between internal and external edges.
data EscapeEdge = IEdge (Maybe Int)
                | OEdge (Maybe Int)
                deriving (Eq, Ord)

-- | A type synonym for the underlying points-to escape graph
type PTEGraph = Gr EscapeNode EscapeEdge

-- | The escape graph that is constructed for each program point.
-- They should all share considerable structure.
data EscapeGraph = EG { escapeGraph :: PTEGraph
                      , escapeCalleeMap :: Map Node (Set Instruction)
                      , escapeReturns :: Set Node
                      }

instance Eq EscapeGraph where
  eg1 == eg2 = escapeReturns eg1 == escapeReturns eg2 &&
               escapeCalleeMap eg1 == escapeCalleeMap eg2 &&
               (escapeGraph eg1 `equal` escapeGraph eg2)

instance MeetSemiLattice EscapeGraph where
  meet eg1 eg2 = EG { escapeGraph = g'
                    , escapeCalleeMap = ecm
                    , escapeReturns = er
                    }
    where
      ecm = M.unionWith S.union (escapeCalleeMap eg1) (escapeCalleeMap eg2)
      er = escapeReturns eg1 `S.union` escapeReturns eg2
      e1 = S.fromList $ labEdges (escapeGraph eg1) -- FIXME: Need to
                                                   -- merge nodes too
                                                   -- now that we add
                                                   -- new virtual
                                                   -- nodes
      e2 = S.fromList $ labEdges (escapeGraph eg2)
      newEs = S.toList $ e2 \\ e1
      -- Insert new edges from eg2 into eg1
      g' = insEdges newEs (escapeGraph eg1)

instance BoundedMeetSemiLattice EscapeGraph where
  top = EG { escapeGraph = mkGraph [] []
           , escapeCalleeMap = M.empty
           , escapeReturns = S.empty
           }

instance DataflowAnalysis EscapeGraph where
  transfer = escapeTransfer

-- | An opaque result type for the analysis.  Use
-- @escapeGraphAtLocation@ to access it.
newtype EscapeResult = ER (Map Function (Instruction -> EscapeGraph))

-- | An accessor to retrieve the @EscapeGraph@ for any program point.
escapeGraphAtLocation :: EscapeResult -> Instruction -> EscapeGraph
escapeGraphAtLocation (ER er) i = mapping i
  where
    Just bb = instructionBasicBlock i
    f = basicBlockFunction bb
    mapping = M.findWithDefault (error "No escape result for function") f er

-- | Run the Whaley-Rinard escape analysis on a Module.  This returns
-- an opaque result that can be accessed via @escapeGraphAtLocation@.
runEscapeAnalysis :: Module -> EscapeResult
runEscapeAnalysis m = ER $! M.fromList mapping
  where
    funcLookups = map (uncurry forwardDataflow) statesAndCFGs
    mapping = zip fs funcLookups

    fs = moduleDefinedFunctions m
    globalGraph = buildBaseGlobalGraph m
    cfgs = map mkCFG fs
    states = map (mkInitialGraph globalGraph) fs
    statesAndCFGs = zip states cfgs

pointsTo :: EscapeGraph -> Value -> Set EscapeNode
pointsTo eg v = S.fromList (map (lab' . context g) succs)
  where
    locid = -valueUniqueId v
    g = escapeGraph eg
    succs = suc g locid

-- Internal stuff

-- | The transfer function to add/remove edges to the points-to escape
-- graph for each instruction.
escapeTransfer :: EscapeGraph -> Instruction -> [CFGEdge] -> EscapeGraph
escapeTransfer eg StoreInst { storeValue = sv, storeAddress = sa } _  =
  updatePTEGraph sv sa eg
escapeTransfer eg RetInst { retInstValue = Just rv } _ =
  let (eg', targets) = targetNodes eg rv
  in eg' { escapeReturns = S.fromList targets }
escapeTransfer eg _ _ = eg

-- | Add/Remove edges from the PTE graph due to a store instruction
--
-- FIXME: Determine the "type" of the assigment
updatePTEGraph :: Value -> Value -> EscapeGraph -> EscapeGraph
updatePTEGraph sv sa eg =
  foldl' genEdges egKilled addrNodes
  where
    -- First, find the possible target nodes in the graph.  These
    -- operations can add virtual nodes, depending on what other nodes
    -- are dereferenced and what they point to.
    (eg', valueNodes) = targetNodes eg sv
    (eg'', addrNodes) = targetNodes eg' sa


    egKilled = killModifiedLocalEdges eg'' addrNodes
    -- | Add edges from addrNode to all of the valueNodes.  If
    -- addrNode is global, do NOT kill its current edges.  If it is
    -- local, kill the current edges.
    genEdges escGr addrNode =
      foldl' (addEdge addrNode) escGr valueNodes

addEdge :: Node -> EscapeGraph -> Node -> EscapeGraph
addEdge addrNode eg valueNode =
  eg { escapeGraph = insEdge (addrNode, valueNode, IEdge Nothing) g }
  where
    g = escapeGraph eg

-- | Given an EscapeGraph @eg@ and a list of location nodes, kill all
-- of the edges from the *local* locations.  Note that this returns a
-- bare PTE graph instead of the wrapped dataflow fact.
killModifiedLocalEdges :: EscapeGraph -> [Node] -> EscapeGraph
killModifiedLocalEdges eg addrNodes = eg { escapeGraph = g' }
  where
    g' = foldl' killLocalEdges (escapeGraph eg) addrNodes

killLocalEdges :: PTEGraph -> Node -> PTEGraph
killLocalEdges escGr n =
  case isGlobalNode escGr n of
    True -> escGr
    False -> delEdges es escGr
  where
    es = map unLabel $ out escGr n
    unLabel (s, d, _) = (s, d)

-- If storing to a global node, do NOT kill the edges from it.  Edges
-- should be killed for stores to locals.  Other than that, add edges
-- from the storeAddress to all of the storeValues.  Apparently loads
-- from local fields that may escape induce an extra Outside edge.

isEscapedNode :: EscapeGraph -> Node -> Bool
isEscapedNode eg n =
  isGlobalNode g n || any (isGlobalNode g) nodesReachableFrom
  where
    g = escapeGraph eg
    nodesReachableFrom = rdfs [n] g

isGlobalNode :: PTEGraph -> Node -> Bool
isGlobalNode g n = case lbl of
  OParameterNode _ -> True
  OGlobalNode _ -> True
  _ -> False
  where
    Just lbl = lab g n

-- | Find the nodes that are pointed to by a Value (following pointer
-- dereferences).
targetNodes :: EscapeGraph -> Value -> (EscapeGraph, [Node])
targetNodes eg val =
  let (g', targets) = targetNodes' val
  in (eg { escapeGraph = g' }, S.toList targets)
  where
    g = escapeGraph eg
    targetNodes' v = case valueContent v of
      -- Return the actual *locations* denoted by variable references.
      ArgumentC a -> (g, S.singleton $ (-argumentUniqueId a))
      GlobalVariableC gv -> (g, S.singleton (-globalVariableUniqueId gv))
      ExternalValueC e -> (g, S.singleton (-externalValueUniqueId e))
      FunctionC f -> (g, S.singleton (-functionUniqueId f))
      ExternalFunctionC e -> (g, S.singleton (-externalFunctionUniqueId e))
      -- The NULL pointer doesn't point to anything
      ConstantC ConstantPointerNull {} -> (g, S.empty)
      -- Now deal with the instructions we might see in a memory
      -- reference.  There are many extras here (beyond just field
      -- sensitivity): select, phi, etc.
      InstructionC AllocaInst {} -> (g, S.singleton (-valueUniqueId v))
      -- Follow chains of loads (dereferences).  If there is no
      -- successor for the current LoadInst, we have a situation like
      -- a global pointer with no points-to target.  In that case, we
      -- need to create a virtual location node based on this load.
      --
      -- NOTE: check to see if this provides consistent behavior if
      -- different virtual nodes are chosen for the same logical
      -- location (e.g., in separate branches of an if statement).
      InstructionC i@LoadInst { loadAddress = la } ->
        let (g', targets) = targetNodes' la
        -- in unionMap (S.fromList . suc g) ns
            (g'', successors) = mapAccumR (augmentingSuc i) g' (S.toList targets)
        in (g'', S.unions successors)
      InstructionC BitcastInst { castedValue = cv } ->
        -- It isn't clear that this is really safe if we want field
        -- sensitivity...  this would probably have to add edges for
        -- all possible types.
        targetNodes' cv

-- | This helper follows "pointers" in the points-to-escape graph by
-- one step, effectively dereferencing a pointer.  This is basically
-- just chasing the successors of the input node.
--
-- In some cases, though, a successor might not exist where the
-- dereference chain indicates that there should be one.  This means
-- that no points-to links/locations were set up in the local scope
-- for the dereference.  This can easily happen with struct field
-- accesses and references to global pointers.
--
-- In these unfortunate cases, the successor operation inserts
-- *virtual* nodes (and edges) to stand in for these unknown
-- locations.
augmentingSuc :: Instruction -> PTEGraph -> Node -> (PTEGraph, Set Node)
augmentingSuc i g tgt = case suc g tgt of
  [] -> addVirtual i g tgt
  sucs -> (g, S.fromList sucs)

-- | A small helper to add a new virtual node (based on a load
-- instruction) and an edge from @tgt@ to the virtual instruction:
--
-- > addVirtual loadInst g tgt
--
-- It returns the modified graph and the singleton set containing the
-- new Node.
addVirtual :: Instruction -> PTEGraph -> Node -> (PTEGraph, Set Node)
addVirtual i g tgt = (g'', S.singleton iid)
  where
    iid = instructionUniqueId i
    g' = insNode (iid, IVirtual (Value i)) g
    g'' = insEdge (tgt, iid, IEdge Nothing) g'

-- FIXME: Also need to identify new objects returned by allocators.
-- This is kind of nice because we don't need explicit information
-- about this library - only dependencies.  The escape analysis will
-- essentially identify allocators for us.
--
-- FIXME: Add field nodes - when showing/comparing field nodes, use
-- the dotted field access notation.  Field nodes should be
-- represented by the first GetElementPtrInst node for each field (of
-- each object).

-- | Build the initial EscapeGraph <O_0, I_0, e_0, r_0> for the given
-- Function.  This adds local edges to the base global graph
-- (hopefully sharing some structure).
mkInitialGraph :: PTEGraph -> Function -> EscapeGraph
mkInitialGraph globalGraph f =
  EG { escapeGraph = g, escapeCalleeMap = M.empty, escapeReturns = S.empty }
  where
    g = insEdges (insideEdges ++ paramEdges) $ insNodes nods globalGraph
    nods = concat [ paramNodes, returnNodes, insideNodes {-, fieldNodes -} ]
    insts = concatMap basicBlockInstructions (functionBody f)
    paramNodes = concatMap (mkVarCtxt OParameterNode . Value) (functionParameters f)
    paramEdges = map mkIEdge (functionParameters f)
    internalNodes = filter isInternal insts
    insideNodes = concatMap (mkVarCtxt INode . Value) internalNodes
    insideEdges = map mkIEdge internalNodes
    returnNodes = map (mkCtxt OReturnNode . Value) $ filter isNonVoidCall insts

mkCtxt :: (Value -> EscapeNode) -> Value -> LNode EscapeNode
mkCtxt ctor v = (valueUniqueId v, ctor v)

mkVarCtxt :: (Value -> EscapeNode) -> Value -> [LNode EscapeNode]
mkVarCtxt ctor v = [(valueUniqueId v, VariableNode v), (-(valueUniqueId v), ctor v)]

mkIEdge :: IsValue a => a -> LEdge EscapeEdge
mkIEdge v = (valueUniqueId v, -valueUniqueId v, IEdge Nothing)

isNonVoidCall :: Instruction -> Bool
isNonVoidCall inst = case inst of
  CallInst { instructionType = TypeVoid } -> False
  CallInst {} -> True
  InvokeInst { instructionType = TypeVoid } -> False
  InvokeInst {} -> True
  _ -> False

isInternal :: Instruction -> Bool
isInternal inst = case inst of
  AllocaInst {} -> True
  _ -> False

-- | Construct the base graph that contains all of the global nodes in
-- the program.  The hope is that by having a common base graph, some
-- of the common structure can be shared.
--
-- FIXME: Add edges induced by global initializers - actually that
-- might be a bad idea since those edges may not actually exist when a
-- local function is analyzed.  The on-demand virtual node
-- construction should make them unnecessary anyway.
buildBaseGlobalGraph :: Module -> PTEGraph
buildBaseGlobalGraph m = mkGraph nodes0 edges0
  where
    globals = map Value $ moduleGlobalVariables m
    externs = map Value $ moduleExternalValues m
    efuncs = map Value $ moduleExternalFunctions m
    dfuncs = map Value $ moduleDefinedFunctions m
    globalVals = concat [ globals, externs, efuncs, dfuncs ]
    nodes0 = concatMap mkNod globalVals
    edges0 = map mkInitEdge globalVals
    mkNod v = [(-(valueUniqueId v), OGlobalNode v), (valueUniqueId v, VariableNode v)]
    mkInitEdge v = (valueUniqueId v, -valueUniqueId v, OEdge Nothing)

-- Debugging and visualization stuff

escapeParams :: Labellable a => a -> GraphvizParams n EscapeNode EscapeEdge () EscapeNode
escapeParams funcName =
  nonClusteredParams { fmtNode = formatEscapeNode
                     , fmtEdge = formatEscapeEdge
                     , globalAttributes = graphTitle
                     }
  where
    graphTitle = [GraphAttrs [toLabel funcName]]
    formatEscapeNode (_,l) = case l of
      VariableNode v ->
        let Just vname = valueName v
        in [toLabel (show vname), shape PlainText]
      OParameterNode _ -> [toLabel "p", shape Circle]
      OGlobalNode _ -> [toLabel "g", shape Circle]
      OReturnNode _ -> [toLabel "ret", shape Triangle]
      INode _ -> [toLabel "", shape BoxShape]
      IVirtual _ -> [toLabel "v", shape BoxShape, color Brown]
    formatEscapeEdge (_,_,l) = case l of
      IEdge Nothing -> []
      OEdge Nothing -> [style dotted, color Crimson]

viewEscapeGraph :: EscapeResult -> Function -> IO ()
viewEscapeGraph e f = do
  let dg = graphToDot (escapeParams fname) exitGraph
  _ <- runGraphvizCanvas' dg Gtk
  return ()
  where
    fname = show (functionName f)
    exitFact = escapeGraphAtLocation e (functionExitInstruction f)
    exitGraph = escapeGraph exitFact