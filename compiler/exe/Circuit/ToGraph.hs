{-# LANGUAGE RecordWildCards #-}

{- | Circuit to Graph Reduction lowering.

This module lowers linearized Circuit IR to Alloy MIR that uses the
soma_graph_* C runtime for HVM-style graph reduction.

Instead of generating direct computation code, this generates:
1. Graph initialization (soma_graph_init)
2. Graph node construction (soma_graph_num, soma_graph_add, etc.)
3. Function registration for CALL nodes
4. Graph reduction trigger (soma_graph_reduce_parallel)

The graph reduction runtime handles parallelism automatically through
wavefront parallel reduction with work stealing.
-}
module Circuit.ToGraph (
    lowerCircuitToGraph,
) where

import Alloy.Build
import qualified Circuit.Ir as C
import Control.Monad (forM, forM_)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Typing.Types (Type (..), intType)

-- | Environment for graph lowering
data GraphEnv = GraphEnv
    { geNodeIds :: Map C.Name String -- Circuit name -> Alloy name holding node index
    , geFuncIds :: Map String Int -- function name -> func_id for CALL nodes
    , geNextFuncId :: Int
    }

emptyGraphEnv :: GraphEnv
emptyGraphEnv = GraphEnv Map.empty Map.empty 0

-- | Look up node ID for a name
lookupNode :: C.Name -> GraphEnv -> Maybe String
lookupNode name = Map.lookup name . geNodeIds

-- | Extend environment with a node binding
extendNode :: C.Name -> String -> GraphEnv -> GraphEnv
extendNode name nodeId env = env{geNodeIds = Map.insert name nodeId (geNodeIds env)}

-- | Register a function and get its func_id
registerFunc :: String -> GraphEnv -> (Int, GraphEnv)
registerFunc name env =
    case Map.lookup name (geFuncIds env) of
        Just fid -> (fid, env)
        Nothing ->
            let fid = geNextFuncId env
            in (fid, env{geFuncIds = Map.insert name fid (geFuncIds env), geNextFuncId = fid + 1})

-- | Lower a Circuit module to an Alloy module using graph reduction
lowerCircuitToGraph :: C.CModule -> AlloyModule
lowerCircuitToGraph cmod =
    let (_, alloyMod) = runAlloyBuilder (C.cmName cmod) [] $ do
            -- Generate main function that:
            -- 1. Initializes graph runtime
            -- 2. Registers all functions
            -- 3. Builds graph for main expression
            -- 4. Reduces graph
            -- 5. Returns result
            lowerToGraphMain cmod
    in alloyMod

-- | Generate the main entry point for graph reduction
lowerToGraphMain :: C.CModule -> AlloyBuilder ()
lowerToGraphMain cmod = do
    -- Find the main function
    let mainFuncs = filter (\f -> C.cfName f == "main") (C.cmFunctions cmod)
        otherFuncs = filter (\f -> C.cfName f /= "main") (C.cmFunctions cmod)

    case mainFuncs of
        [] -> error "Circuit.ToGraph: no main function found"
        (mainFunc : _) -> do
            -- Generate wrapper functions for each non-main function
            -- These will be called by the graph reducer
            forM_ otherFuncs lowerFunctionForGraph

            -- Generate the main function
            beginFunction "main" [] intType

            entryBlock <- freshBlockName
            beginBlock entryBlock []

            -- Initialize graph runtime with 4 workers
            emitEffect (EffGraphInit 4)

            -- Register all functions with the runtime
            -- For now, we'll handle this during graph construction
            let env0 = emptyGraphEnv

            -- Build the graph for the main function body
            resultNode <- lowerTermToGraph env0 (C.cfBody mainFunc)

            -- Reduce the graph and get result
            resultVal <- emitLetTmp intType (OpGraphReduce (OpVar resultNode))

            -- Shutdown graph runtime
            emitEffect EffGraphShutdown

            terminate (ARet (Just (OpVar resultVal)))
            endFunction

{- | Lower a function to be callable from graph reduction
These functions get registered with the runtime and called via CALL nodes
-}
lowerFunctionForGraph :: C.CFunction -> AlloyBuilder ()
lowerFunctionForGraph cfun@C.CFunction{..} = do
    -- Generate a normal function that can be called by the graph reducer
    -- The graph reducer will extract arguments from ports and call this
    beginFunction cfName cfParams cfReturnType

    entryBlock <- freshBlockName
    beginBlock entryBlock []

    -- Initialize environment with parameters
    let env0 =
            GraphEnv
                { geNodeIds = Map.empty
                , geFuncIds = Map.empty
                , geNextFuncId = 0
                }

    -- For now, lower the body as graph construction
    -- The reducer calls this and expects a node index back
    result <- lowerTermToGraph env0 cfBody

    -- Return the node index
    terminate (ARet (Just (OpVar result)))
    endFunction

{- | Lower a Circuit term to graph construction calls
Returns the name of the variable holding the root node index
-}
lowerTermToGraph :: GraphEnv -> C.CTerm -> AlloyBuilder String
lowerTermToGraph env term = case term of
    -- Integer literals become NUM nodes
    C.CInt n -> do
        nodeId <- emitLetTmp intType (OpGraphNum (OpConst (CInt n)))
        pure nodeId

    -- Variables: look up the node they're bound to
    C.CVar name _ ->
        case lookupNode name env of
            Just nodeId -> pure nodeId
            Nothing -> error $ "Circuit.ToGraph: unbound variable: " ++ name
    -- Let bindings: build graph for value, bind node ID
    C.CLet name _ty val body -> do
        valNode <- lowerTermToGraph env val
        let env' = extendNode name valNode env
        lowerTermToGraph env' body

    -- Binary operations become operator nodes
    C.CBinOp op a b -> do
        aNode <- lowerTermToGraph env a
        bNode <- lowerTermToGraph env b
        let nodeOp = case op of
                C.OpAdd -> OpGraphAdd (OpVar aNode) (OpVar bNode)
                C.OpSub -> OpGraphSub (OpVar aNode) (OpVar bNode)
                C.OpMul -> OpGraphMul (OpVar aNode) (OpVar bNode)
                _ -> error $ "Circuit.ToGraph: unsupported binary op: " ++ show op
        nodeId <- emitLetTmp intType nodeOp
        pure nodeId

    -- Function calls become CALL nodes
    C.CApp fun arg _resultTy -> do
        -- Collect all arguments
        let (f, args) = collectArgs term
        case f of
            C.CRef fName _ -> do
                argNodes <- mapM (lowerTermToGraph env) args
                nodeId <- emitLetTmp intType (OpGraphCall fName (map OpVar argNodes))
                pure nodeId
            C.CVar fName _ ->
                case lookupNode fName env of
                    Nothing -> do
                        -- Global function
                        argNodes <- mapM (lowerTermToGraph env) args
                        nodeId <- emitLetTmp intType (OpGraphCall fName (map OpVar argNodes))
                        pure nodeId
                    Just _ ->
                        -- Higher-order function - not yet supported in graph mode
                        error "Circuit.ToGraph: higher-order functions not yet supported in graph mode"
            _ -> error "Circuit.ToGraph: unsupported function application"

    -- Function references - these should be registered
    C.CRef name _ -> do
        -- For now, treat as a thunk that will be called
        error $ "Circuit.ToGraph: bare function reference not supported: " ++ name

    -- Booleans - encode as integers for now
    C.CBool b -> do
        let n = if b then 1 else 0
        nodeId <- emitLetTmp intType (OpGraphNum (OpConst (CInt n)))
        pure nodeId

    -- Strings - not yet supported
    C.CStr _ ->
        error "Circuit.ToGraph: strings not yet supported in graph mode"
    -- Erasure - unit value, encode as 0
    C.CEra -> do
        nodeId <- emitLetTmp intType (OpGraphNum (OpConst (CInt 0)))
        pure nodeId

    -- Comparison operations - reduce to 0 or 1
    C.CCmpOp op a b -> do
        -- For graph reduction, we need to implement comparisons as graph nodes
        -- For now, fall back to eager evaluation
        aNode <- lowerTermToGraph env a
        bNode <- lowerTermToGraph env b
        -- Create a comparison node (needs runtime support)
        -- For now, just return a dummy
        error $ "Circuit.ToGraph: comparison ops not yet supported: " ++ show op

    -- Unary operations
    C.CUnaryOp op a -> do
        aNode <- lowerTermToGraph env a
        case op of
            C.OpNeg -> do
                -- Negate: 0 - a
                zeroNode <- emitLetTmp intType (OpGraphNum (OpConst (CInt 0)))
                nodeId <- emitLetTmp intType (OpGraphSub (OpVar zeroNode) (OpVar aNode))
                pure nodeId
            C.OpNot ->
                error "Circuit.ToGraph: logical not not yet supported in graph mode"

    -- Lambdas (closures) - not yet supported
    C.CLam{} ->
        error "Circuit.ToGraph: lambdas not yet supported in graph mode"
    -- Closures - not yet supported
    C.CClosure{} ->
        error "Circuit.ToGraph: closures not yet supported in graph mode"
    -- Superpositions: {l1 l2} creates a SUP node
    C.CSup label left right _ty -> do
        leftNode <- lowerTermToGraph env left
        rightNode <- lowerTermToGraph env right
        nodeId <- emitLetTmp intType (OpGraphSup label (OpVar leftNode) (OpVar rightNode))
        pure nodeId

    -- Duplications: let !x &L = val in body
    -- Creates a DUP node pointing at val, binds x to the DUP node index
    C.CDup name _valTy label val body -> do
        valNode <- lowerTermToGraph env val
        dupNode <- emitLetTmp intType (OpGraphDup label (OpVar valNode))
        -- Bind the dup node so projections can find it
        let env' = extendNode name dupNode env
        lowerTermToGraph env' body

    -- Dup projections: access copy 0 or 1 from a DUP node
    -- In graph reduction, projections are handled by the DUP-SUP interactions
    -- The dup node index IS the projection - reducer returns correct copy
    C.CDp0 name _ty ->
        case lookupNode name env of
            Just nodeId -> pure nodeId
            Nothing -> error $ "Circuit.ToGraph: unbound dup variable: " ++ name
    C.CDp1 name _ty ->
        case lookupNode name env of
            Just nodeId -> pure nodeId
            Nothing -> error $ "Circuit.ToGraph: unbound dup variable: " ++ name
    -- Tagged values (constructors) - not yet supported
    C.CTag{} ->
        error "Circuit.ToGraph: tagged values not yet supported in graph mode"
    -- Case expressions - not yet supported
    C.CCase{} ->
        error "Circuit.ToGraph: case expressions not yet supported in graph mode"
    -- Closure env access
    C.CClosureGetEnv{} ->
        error "Circuit.ToGraph: closure env access not supported in graph mode"
    -- Field projection
    C.CProject{} ->
        error "Circuit.ToGraph: field projection not yet supported in graph mode"
    -- Panic
    C.CPanic msg _ -> do
        error $ "Circuit.ToGraph: panic in graph mode: " ++ msg
  where
    -- Helper to collect function and arguments from nested CApp
    collectArgs :: C.CTerm -> (C.CTerm, [C.CTerm])
    collectArgs (C.CApp f x _) =
        let (fun, args) = collectArgs f
        in (fun, args ++ [x])
    collectArgs other = (other, [])
