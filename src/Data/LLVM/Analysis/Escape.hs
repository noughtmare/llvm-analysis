{-# LANGUAGE ViewPatterns, BangPatterns, FlexibleInstances, MultiParamTypeClasses #-}
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
  AccessType(Array, Field),
  PTEGraph,
  -- * Functions
  runEscapeAnalysis,
  escapeGraphAtLocation,
  localPointsTo,
  valueEscaped,
  valueProperlyEscaped,
  valueWillEscape,
  valueInGraph,
  followEscapeEdge,
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
import Data.Hashable
import Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS

import Data.LLVM
import Data.LLVM.CFG
import Data.LLVM.CallGraph
import Data.LLVM.Analysis.CallGraphSCCTraversal
import Data.LLVM.Analysis.Dataflow
import Data.LLVM.Internal.PatriciaTree

-- | The types of nodes in the graph
data EscapeNode = VariableNode { escapeNodeValue :: !Value }
                | OParameterNode { escapeNodeValue :: !Value }
                | OGlobalNode { escapeNodeValue :: !Value }
                | OReturnNode { escapeNodeValue :: !Value }
                | INode { escapeNodeValue :: !Value } -- Allocas and allocators
                | IVirtual { escapeNodeValue :: !Value }
                deriving (Eq, Ord)

data AccessType = Direct
                | Array
                | Field !Int !Type
                deriving (Eq, Ord)

-- | Edges labels for the points-to escape graph.  These differentiate
-- between internal and external edges.
data EscapeEdge = IEdge !AccessType
                | OEdge !AccessType
                deriving (Eq, Ord)

-- | A type synonym for the underlying points-to escape graph
type PTEGraph = Gr EscapeNode EscapeEdge

-- | The escape graph that is constructed for each program point.
-- They should all share considerable structure.
data EscapeGraph = EG { escapeGraph :: !PTEGraph
                      , escapeCalleeMap :: !(Map Node (Set Instruction))
                      , escapeReturns :: !(Set Node)
                      }

instance Hashable EscapeEdge where
  hash (IEdge at) = 3 `combine` hash at
  hash (OEdge at) = 7 `combine` hash at

instance Hashable AccessType where
  hash Direct = 11
  hash Array = 13
  hash (Field i t) = 17 `combine` hash i `combine` hash t

instance Hashable EscapeNode where
  hash (VariableNode v) = 3 `combine` hash v
  hash (OParameterNode v) = 5 `combine` hash v
  hash (OGlobalNode v) = 7 `combine` hash v
  hash (OReturnNode v) = 11 `combine` hash v
  hash (INode v) = 13 `combine` hash v
  hash (IVirtual v) = 17 `combine` hash v

-- | Internal graph equality test that doesn't require sorting lists.
-- It could be less efficient, but it is at least strict enough.
geq :: (Eq a, Eq b, Hashable a, Hashable b, Graph gr1, Graph gr2)
       => gr1 a b -> gr2 a b -> Bool
geq !g1 !g2 = ns1 == ns2 && es1 == es2
  where
    ns1 = HS.fromList (labNodes g1)
    ns2 = HS.fromList (labNodes g2)
    es1 = HS.fromList (labEdges g1)
    es2 = HS.fromList (labEdges g2)

instance Eq EscapeGraph where
  (==) !eg1 !eg2 = escapeReturns eg1 == escapeReturns eg2 &&
               escapeCalleeMap eg1 == escapeCalleeMap eg2 &&
               (escapeGraph eg1 `geq` escapeGraph eg2)

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

instance DataflowAnalysis EscapeGraph EscapeData where
  transfer = escapeTransfer

-- | This is a module-internal datatype to represent information that
-- is constant throughout the analysis of a single function.  This
-- saves us from having to waste extra space in the dataflow fact,
-- since the dataflow analysis engine can just hand it off in constant
-- space.
data EscapeData = EscapeData { externalP :: ExternalFunction -> Int -> Bool
                             , escapeSummary :: Map Function (HashMap Instruction EscapeGraph)
                             }

-- | An opaque result type for the analysis.  Use
-- @escapeGraphAtLocation@ to access it.
newtype EscapeResult = ER (Map Function (HashMap Instruction EscapeGraph))
                     deriving (Eq)

-- | An accessor to retrieve the @EscapeGraph@ for any program point.
escapeGraphAtLocation :: EscapeResult -> Instruction -> EscapeGraph
escapeGraphAtLocation (ER er) i = case HM.lookup i funcMapping of
  Nothing -> error ("No escape result for instruction " ++ show i)
  Just eg -> eg
  where
    Just bb = instructionBasicBlock i
    f = basicBlockFunction bb
    funcMapping = M.findWithDefault (error "No escape result for function") f er

-- | Run the Whaley-Rinard escape analysis on a Module.  This returns
-- an opaque result that can be accessed via @escapeGraphAtLocation@.
--
-- This variant conservatively assumes that any parameter passed to an
-- external function escapes.
runEscapeAnalysis :: Module -> CallGraph -> EscapeResult
runEscapeAnalysis m cg = runEscapeAnalysis' m cg (\_ _ -> True)

-- | A variant of @runEscapeAnalysis@ that accepts a function to
-- provide escape information about arguments for external functions.
--
-- > runEscapeAnalysis' externP m
--
-- The function @externP@ will be called for each argument of each
-- external function.  The @externP ef ix@ should return @True@ if the
-- @ix@th argument of @ef@ causes the argument to escape.
runEscapeAnalysis' :: Module -> CallGraph -> (ExternalFunction -> Int -> Bool) -> EscapeResult
runEscapeAnalysis' m cg externP = moduleSummary
  where
    globalGraph = buildBaseGlobalGraph m

    moduleSummary = callGraphSCCTraversal cg summarizeFunction (ER M.empty)
    summarizeFunction f (ER summ) =
      let s0 = mkInitialGraph globalGraph f
          ed = EscapeData externP summ
          lookupFunc = forwardDataflow ed s0 f
      in ER $ M.insert f lookupFunc summ

-- | Provide local points-to information for a value @v@:
--
-- > localPointsTo eg v
--
-- This information is flow sensitive (there is an EscapeGraph for
-- each program point).  The returned set of nodes reflect the things
-- that the value can point to.
--
-- The set will be empty if the value is not a location (alloca,
-- argument, newly allocated storage, or global) or if it does not
-- point to anything yet.
--
-- This information does not include edges between globals or from
-- globals that are not established locally to the function call.  For
-- information at that level, use one of the global PointsTo analyses.
localPointsTo :: EscapeGraph -> Value -> Set EscapeNode
localPointsTo eg v = S.fromList (map (lab' . context g) succs)
  where
    locid = valueUniqueId v
    g = escapeGraph eg
    succs = suc g locid

-- | Determine whether or not the value has a representation in the
-- escape graph.
valueInGraph :: EscapeGraph -> Value -> Bool
valueInGraph eg v = gelem (valueUniqueId v) g
  where
    g = escapeGraph eg

-- | The value escaped from the current context because it is
-- reachable from an outside node.
valueEscaped :: EscapeGraph -> Value -> Bool
valueEscaped eg v = isGlobalNode g n || valueProperlyEscaped eg v
  where
    n = valueUniqueId v
    g = escapeGraph eg

-- | The value escaped from the current context because it is
-- reachable from an ouside node *besides itself*.  This is analagous
-- to the subset vs. proper subset distinction.
--
-- This is most useful to determine when one argument escapes by being
-- assigned into another.
valueProperlyEscaped :: EscapeGraph -> Value -> Bool
valueProperlyEscaped eg v = nodeProperlyEscaped (escapeGraph eg) (valueUniqueId v)

-- | The value will escape from the current context when the function
-- returns (i.e., through the return value).
valueWillEscape :: EscapeGraph -> Value -> Bool
valueWillEscape eg v = S.member n escapingNodes
  where
    n = valueUniqueId v
    g = escapeGraph eg
    erList = S.toList (escapeReturns eg)
    escapingNodes = escapeReturns eg `S.union` S.fromList (dfs erList g)

-- | From the base value @v@, follow the edge for the provided
-- @accessType@.  AccessTypes describe either array accesses or field
-- accesses.  There should only be one edge for each access type.
--
-- This function returns the Value at the indicated node (a
-- GetElementPtrInst).
--
-- > followEscapeEdge eg v accessType
followEscapeEdge :: EscapeGraph -> Value -> AccessType -> Maybe Value
followEscapeEdge eg v at =
  case targetSucs of
    [] -> Nothing
    [ts] -> Just $ (escapeNodeValue . lab' . context g . fst) ts
  where
    g = escapeGraph eg
    ss = lsuc g (valueUniqueId v)
    targetSucs = filter ((\x -> x==IEdge at || x==OEdge at) . snd) ss

-- Internal stuff

nodeEscaped :: PTEGraph -> Node -> Bool
nodeEscaped escGr n = isGlobalNode escGr n || nodeProperlyEscaped escGr n

nodeProperlyEscaped :: PTEGraph -> Node -> Bool
nodeProperlyEscaped escGr n = any (isGlobalNode g) nodesReachableFrom
  where
    -- Remove the variable node corresponding to this node so that we
    -- don't say that it is escaping because its own variable node
    -- points to it.
    (_, g) = match (-n) escGr
    nodesReachableFrom = filter (/= n) $ rdfs [n] g

-- | The transfer function to add/remove edges to the points-to escape
-- graph for each instruction.
escapeTransfer :: EscapeData
                  -> EscapeGraph
                  -> Instruction
                  -> [CFGEdge]
                  -> EscapeGraph
escapeTransfer _ eg StoreInst { storeValue = sv, storeAddress = sa } _
  | isPointerType sv = updatePTEGraph sv sa eg
  | otherwise = eg
escapeTransfer _ eg RetInst { retInstValue = Just rv } _
  | isPointerType rv = let (eg', targets) = targetNodes eg rv
                       in eg' { escapeReturns = S.fromList targets }
  | otherwise = eg
escapeTransfer _ eg _ _ = eg

-- | Add/Remove edges from the PTE graph due to a store instruction
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
  eg { escapeGraph = insEdge (addrNode, valueNode, IEdge Direct) g }
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
  case nodeEscaped escGr n || isNotSingularNode escGr n of
    True -> escGr
    False -> delEdges es escGr
  where
    es = map unLabel $ out escGr n
    unLabel (s, d, _) = (s, d)

-- | Determine whether or not a node is singular (e.g., represents a
-- single value).  Nodes that were obtained by an array access are not
-- singular.  Values returned by a function call in a loop are not
-- singular (they are summary values).
--
-- Non-singular values cannot be updated strongly.
--
-- FIXME: This is a stub for now and should be filled in.
isNotSingularNode _ _ = False

-- If storing to a global node, do NOT kill the edges from it.  Edges
-- should be killed for stores to locals.  Other than that, add edges
-- from the storeAddress to all of the storeValues.  Apparently loads
-- from local fields that may escape induce an extra Outside edge.


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
    targetNodes' v = case valueContent' v of
      -- Return the actual *locations* denoted by variable references.
      ArgumentC a -> (g, S.singleton $ (argumentUniqueId a))
      GlobalVariableC gv -> (g, S.singleton (globalVariableUniqueId gv))
      ExternalValueC e -> (g, S.singleton (externalValueUniqueId e))
      FunctionC f -> (g, S.singleton (functionUniqueId f))
      ExternalFunctionC e -> (g, S.singleton (externalFunctionUniqueId e))
      -- The NULL pointer doesn't point to anything
      ConstantC ConstantPointerNull {} -> (g, S.empty)
      -- Now deal with the instructions we might see in a memory
      -- reference.  There are many extras here (beyond just field
      -- sensitivity): select, phi, etc.
      InstructionC AllocaInst {} -> (g, S.singleton (valueUniqueId v))
      InstructionC LoadInst { loadAddress =
        (valueContent' -> InstructionC i@GetElementPtrInst { getElementPtrValue = base
                                                           , getElementPtrIndices = idxs
                                                           }) } ->
        gepInstTargets i base idxs
      InstructionC LoadInst { loadAddress =
        (valueContent' -> ConstantC ConstantValue { constantInstruction =
          i@GetElementPtrInst { getElementPtrValue = base
                              , getElementPtrIndices = idxs
                              } }) } ->
        gepInstTargets i base idxs

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
            (g'', successors) = mapAccumR (augmentingSuc i) g' (S.toList targets)
        in (g'', S.unions successors)
      InstructionC i@CallInst { } -> case gelem (valueUniqueId i) g of
        False -> error "Escape analysis: result of void return used"
        True -> (g, S.singleton (valueUniqueId i))
      -- It is also possible to store into the result of a GEP
      -- instruction (without a load), so add a case to handle
      -- un-loaded GEPs.
      InstructionC i@GetElementPtrInst { getElementPtrValue = base
                                       , getElementPtrIndices = idxs
                                       } ->
        gepInstTargets i base idxs
      ConstantC ConstantValue { constantInstruction =
       i@GetElementPtrInst { getElementPtrValue = base
                           , getElementPtrIndices = idxs
                           } } ->
        gepInstTargets i base idxs

      _ -> error $ "Escape Analysis unmatched: " ++ show v

    gepInstTargets :: Instruction -> Value -> [Value] -> (PTEGraph, Set Node)
    gepInstTargets i base idxs =
      case idxs of
        [] -> error "Escape analysis: GEP with no indexes"
        [_] ->
          let (g', targets) = targetNodes' base
              (g'', successors) = mapAccumR (augmentingArraySuc i) g' (S.toList targets)
          in (g'', S.unions successors)
        -- For this to be a simple field access, the array indexing
        -- offset must be zero and the field index must be some
        -- constant.
        (valueContent -> ConstantC ConstantInt { constantIntValue = 0}) :
          (valueContent -> ConstantC ConstantInt { constantIntValue = fieldNo }) : _ ->
            let (g', targets) = targetNodes' base
                baseIsEscaped = valueEscaped eg base
                accumF = augmentingFieldSuc (fromIntegral fieldNo) (getBaseType base) i baseIsEscaped
                (g'', successors) = mapAccumR accumF g' (S.toList targets)
            in (g'', S.unions successors)
        -- Otherwise this is something really fancy and we can just
        -- treat it as an array
        _ ->
          let (g', targets) = targetNodes' base
              (g'', successors) = mapAccumR (augmentingArraySuc i) g' (S.toList targets)
          in (g'', S.unions successors)


getBaseType :: Value -> Type
getBaseType v = case valueType v of
  TypePointer t _ -> t
  _ -> error $ "Array base value has illegal type: " ++ show v

augmentingFieldSuc :: Int -> Type -> Instruction -> Bool -> PTEGraph -> Node -> (PTEGraph, Set Node)
augmentingFieldSuc ix ty i baseEscaped g tgt = case fieldSucs of
  -- FIXME: There are some cases where this should be an OEdge!  If
  -- the base object of the field access is escaped, this should be an
  -- OEdge
  [] -> addVirtual (edgeCon (Field ix ty)) i g tgt
  _ -> (g, S.fromList fieldSucs)
  where
    edgeCon = if baseEscaped then OEdge else IEdge
    fieldSucs = map fst $ filter (isFieldSuc ix baseEscaped) $ lsuc g tgt

augmentingArraySuc :: Instruction -> PTEGraph -> Node -> (PTEGraph, Set Node)
augmentingArraySuc i g tgt = case arraySucs of
  [] -> addVirtual (IEdge Array) i g tgt
  _ -> (g, S.fromList arraySucs)
  where
    arraySucs = map fst $ filter isArraySuc $ lsuc g tgt

-- FIXME: Can't kill edges if dealing with an array or escaped node

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
augmentingSuc i g tgt = case directSucs of
  [] -> addVirtual (IEdge Direct) i g tgt
  _ -> (g, S.fromList directSucs)
  where
    directSucs = map fst $ filter isDirectSuc $ lsuc g tgt

isDirectSuc :: (Node, EscapeEdge) -> Bool
isDirectSuc (_, IEdge Direct) = True
isDirectSuc (_, OEdge Direct) = True
isDirectSuc _ = False

isArraySuc :: (Node, EscapeEdge) -> Bool
isArraySuc (_, IEdge Array) = True
isArraySuc (_, OEdge Array) = True
isArraySuc _ = False

-- | When checking field successors, also match on the edge type.  If
-- the base node is escaped, we need to ensure we have an OEdge here
-- (if not, we make one in the caller).  If the base does escape, the
-- boolean flag here should match anyway...
isFieldSuc :: Int -> Bool -> (Node, EscapeEdge) -> Bool
isFieldSuc ix False (_, IEdge (Field fieldNo _)) = ix == fieldNo
isFieldSuc ix _ (_, OEdge (Field fieldNo _)) = ix == fieldNo
isFieldSuc _ _ _ = False

-- | A small helper to add a new virtual node (based on a load
-- instruction) and an edge from @tgt@ to the virtual instruction:
--
-- > addVirtual edgeLabel loadInst g tgt
--
-- It returns the modified graph and the singleton set containing the
-- new Node.
addVirtual :: EscapeEdge -> Instruction -> PTEGraph -> Node -> (PTEGraph, Set Node)
addVirtual elbl i g tgt = (g'', S.singleton iid)
  where
    iid = instructionUniqueId i
    g' = insNode (iid, IVirtual (Value i)) g
    g'' = insEdge (tgt, iid, elbl) g'

-- | Build the initial EscapeGraph <O_0, I_0, e_0, r_0> for the given
-- Function.  This adds local edges to the base global graph
-- (hopefully sharing some structure).
mkInitialGraph :: PTEGraph -> Function -> EscapeGraph
mkInitialGraph globalGraph f =
  EG { escapeGraph = g, escapeCalleeMap = M.empty, escapeReturns = S.empty }
  where
    g = insEdges (insideEdges ++ paramEdges) $ insNodes nods globalGraph
    nods = concat [ paramNodes, returnNodes, insideNodes ]
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
mkVarCtxt ctor v = [(-valueUniqueId v, VariableNode v), (valueUniqueId v, ctor v)]

mkIEdge :: IsValue a => a -> LEdge EscapeEdge
mkIEdge v = (-valueUniqueId v, valueUniqueId v, IEdge Direct)

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
    mkNod v = [(valueUniqueId v, OGlobalNode v), (-valueUniqueId v, VariableNode v)]
    mkInitEdge v = (-valueUniqueId v, valueUniqueId v, OEdge Direct)

isPointerType :: Value -> Bool
isPointerType = isPointer' . valueType
  where
    isPointer' t = case t of
      TypePointer _ _ -> True
      _ -> False

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
      IEdge Direct -> []
      IEdge Array -> [toLabel "[*]"]
      IEdge (Field ix t) -> fieldAccessToLabel ix t []
      OEdge Direct -> [style dotted, color Crimson]
      OEdge Array -> [toLabel "[*]", style dotted, color Crimson]
      OEdge (Field ix t) -> fieldAccessToLabel ix t [style dotted, color Crimson]

fieldAccessToLabel :: Int -> Type -> [Attribute] -> [Attribute]
fieldAccessToLabel ix t initSet = case t of
  TypeStruct (Just n) _ _ ->
    let accessStr = concat [ n, ".", show ix ]
    in toLabel accessStr : initSet
  TypeStruct Nothing _ _ ->
    let accessStr = "<anon>." ++ show ix
    in toLabel accessStr : initSet

viewEscapeGraph :: EscapeResult -> Function -> IO ()
viewEscapeGraph e f = do
  let dg = graphToDot (escapeParams fname) exitGraph
  _ <- runGraphvizCanvas' dg Gtk
  return ()
  where
    fname = show (functionName f)
    exitFact = escapeGraphAtLocation e (functionExitInstruction f)
    exitGraph = escapeGraph exitFact