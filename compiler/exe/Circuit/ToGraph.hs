{-# LANGUAGE RecordWildCards #-}

{- | Circuit to Graph Reduction lowering.

This module lowers NON-LINEARIZED Circuit IR to Alloy MIR that uses the
INET C runtime for parallel graph reduction.

== PURE GRAPH MODEL ==

Functions return graph nodes (Terms), NOT reduced values. The runtime
reduces the graph lazily with work-stealing parallelism.

Key principles:
1. Function calls become REF nodes (inet_ref) - NOT direct calls
2. The runtime calls registered functions when it encounters REF nodes
3. All computation is represented as graph nodes
4. Only the final result is reduced to a value

== NO LINEARIZATION ==

Unlike standard mode, graph mode does NOT use the linearization pass.
Variables can be used multiple times - the runtime handles duplication
lazily via graph reduction rules.

For integer arguments, we reduce once and use the native value directly.
This is efficient because:
- Native arithmetic is faster than graph operations
- We only wrap in inet_num() when building graph nodes for recursive calls
- This matches what HVM and test_inet.c do
-}
module Circuit.ToGraph (
    lowerCircuitToGraph,
) where

import Alloy.Build
import qualified Circuit.Ir as C
import Control.Monad (forM, forM_)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Typing.Types (Kind (..), TyConstructor (..), Type (..), intType)

-- | Term type for graph operations (64-bit)
termType :: Type
termType = TConstructor (TypeConstructor "Long" KindStar)

-- | Environment for graph lowering
data GraphEnv = GraphEnv
    { geBindings :: Map C.Name String
    -- ^ Circuit name -> Alloy variable name (holding native Int value)
    }

emptyGraphEnv :: GraphEnv
emptyGraphEnv = GraphEnv Map.empty

-- | Look up a binding
lookupBinding :: C.Name -> GraphEnv -> Maybe String
lookupBinding name = Map.lookup name . geBindings

-- | Extend environment with a binding
extendBinding :: C.Name -> String -> GraphEnv -> GraphEnv
extendBinding name varName env =
    env{geBindings = Map.insert name varName (geBindings env)}

-- | Lower a Circuit module to an Alloy module using graph reduction
lowerCircuitToGraph :: C.CModule -> AlloyModule
lowerCircuitToGraph cmod =
    let (_, alloyMod) = runAlloyBuilder (C.cmName cmod) [] $ do
            lowerToGraphMain cmod
    in alloyMod

-- | Generate the main entry point and all functions for graph reduction
lowerToGraphMain :: C.CModule -> AlloyBuilder ()
lowerToGraphMain cmod = do
    let mainFuncs = filter (\f -> C.cfName f == "main") (C.cmFunctions cmod)
        otherFuncs = filter (\f -> C.cfName f /= "main") (C.cmFunctions cmod)

    case mainFuncs of
        [] -> error "Circuit.ToGraph: no main function found"
        (mainFunc : _) -> do
            -- Generate graph-building functions for each non-main function
            forM_ otherFuncs lowerFunctionForGraph

            -- Generate the main function
            beginFunction "main" [] intType

            entryBlock <- freshBlockName
            beginBlock entryBlock []

            -- NOTE: The C runtime's main() in soma_inet.c handles inet_init/free.
            -- We only need to register functions and build/reduce the graph.

            -- Register all functions with the runtime
            forM_ otherFuncs $ \f -> do
                let fname = C.cfName f
                    arity = length (C.cfParams f)
                emitEffect (EffGraphRegisterFunc fname arity (OpVar fname))

            -- Build the graph for the main function body
            resultNode <- lowerTermToGraph emptyGraphEnv (C.cfBody mainFunc)

            -- Reduce the graph and get result
            resultVal <- emitLetTmp intType (OpGraphReduce (OpVar resultNode))

            terminate (ARet (Just (OpVar resultVal)))
            endFunction

{- | Lower a function to be callable from graph reduction.

The function receives (net, tm, arg) and returns a Term.
The runtime calls these functions as INetFunc: (INet*, ThreadMem*, Term) -> Term

CRITICAL: We use OpGraphExtractNum to get the native int from arg.
The runtime has ALREADY reduced the arg to a NUM before calling us.
We must NOT call inet_reduce internally - that causes nested parallel reductions!
-}
lowerFunctionForGraph :: C.CFunction -> AlloyBuilder ()
lowerFunctionForGraph C.CFunction{..} = do
    -- Function signature: (net: ptr, tm: ptr, arg: Term) -> Term
    -- This matches the INetFunc typedef in soma_inet.h
    let ptrType = TConstructor (TypeConstructor "Ptr" KindStar)
    beginFunction cfName [("net", ptrType), ("tm", ptrType), ("arg", termType)] termType

    entryBlock <- freshBlockName
    beginBlock entryBlock []

    -- Extract the integer from the arg term (which should be a NUM)
    -- The runtime ensures args are reduced before calling functions.
    -- We use OpGraphExtractNum (not OpGraphReduce!) to avoid nested parallel reductions.
    argVal <- emitLetTmp intType (OpGraphExtractNum (OpVar "arg"))

    -- Bind the parameter to the native value (Int, not Term)
    let env = case cfParams of
            ((pname, _) : _) -> extendBinding pname argVal emptyGraphEnv
            [] -> emptyGraphEnv

    -- Lower the body - this returns a graph node (Term)
    result <- lowerTermToGraph env cfBody

    -- Return the term (graph node) - NOT reduced!
    terminate (ARet (Just (OpVar result)))
    endFunction

{- | Lower a Circuit term to graph construction.

CRITICAL: Graph functions must NOT call inet_reduce internally!
They receive a native int (from OpGraphExtractNum) and return a graph node.
The runtime handles all reduction via redexes.

Variables are bound to native Int values.
When building graph nodes, wrap native values with inet_num() (OpGraphNum).

For efficiency, simple arithmetic on native values is computed natively
rather than building graph nodes. This matches the HVM/test_inet.c pattern.

Returns the name of the variable holding the graph node (Term).
-}
lowerTermToGraph :: GraphEnv -> C.CTerm -> AlloyBuilder String
lowerTermToGraph env term = case term of
    -- Integer literals become NUM nodes
    C.CInt n -> do
        emitLetTmp termType (OpGraphNum (OpConst (CInt n)))

    -- Variables: wrap native value in inet_num to create graph node
    C.CVar name _ ->
        case lookupBinding name env of
            Just varName -> do
                -- Native value -> wrap in graph node
                emitLetTmp termType (OpGraphNum (OpVar varName))
            Nothing -> error $ "Circuit.ToGraph: unbound variable: " ++ name
    -- Let bindings
    C.CLet name _ty val body -> do
        -- Build graph for val
        valNode <- lowerTermToGraph env val
        -- NOTE: We DON'T reduce here! Instead we extend with the graph node
        -- and let the runtime reduce lazily. But for native arithmetic,
        -- we need the actual value...
        -- For now, let bindings in graph functions need special handling.
        -- If the binding is used in arithmetic, we need to reduce.
        -- This is a compromise - true laziness would need more work.
        nativeVal <- emitLetTmp intType (OpGraphReduce (OpVar valNode))
        let env' = extendBinding name nativeVal env
        lowerTermToGraph env' body

    -- Binary operations: compute natively when operands are simple (vars/literals)
    -- This is critical for fib-like patterns where we do (n - 1), (n - 2)
    -- and pass results to recursive calls.
    C.CBinOp op a b -> do
        -- Try to get native values for operands
        maNative <- tryGetNative env a
        mbNative <- tryGetNative env b
        case (maNative, mbNative) of
            (Just aNative, Just bNative) -> do
                -- Both operands are native - compute natively, wrap result
                let binOp = case op of
                        C.OpAdd -> IAdd
                        C.OpSub -> ISub
                        C.OpMul -> IMul
                        _ -> ISub -- TODO: handle other ops
                nativeResult <- emitLetTmp intType (OpBin binOp (OpVar aNative) (OpVar bNative))
                emitLetTmp termType (OpGraphNum (OpVar nativeResult))
            _ -> do
                -- Fall back to building graph nodes
                aNode <- lowerTermToGraph env a
                bNode <- lowerTermToGraph env b
                let nodeOp = case op of
                        C.OpAdd -> OpGraphAdd (OpVar aNode) (OpVar bNode)
                        C.OpSub -> OpGraphSub (OpVar aNode) (OpVar bNode)
                        C.OpMul -> OpGraphMul (OpVar aNode) (OpVar bNode)
                        C.OpDiv -> OpGraphSub (OpVar aNode) (OpVar bNode) -- TODO: OpGraphDiv
                        C.OpMod -> OpGraphSub (OpVar aNode) (OpVar bNode) -- TODO: OpGraphMod
                        _ -> error $ "Circuit.ToGraph: unsupported binary op: " ++ show op
                emitLetTmp termType nodeOp

    -- Function applications become REF nodes
    -- CRITICAL: Do NOT reduce the argument here!
    -- Just build the REF node with the arg graph, let runtime reduce.
    C.CApp fun arg _resultTy -> do
        let (f, args) = collectArgs term
        case f of
            C.CRef fName _ -> do
                case args of
                    [singleArg] -> do
                        -- Build graph for arg - this is already a Term (graph node)
                        argNode <- lowerTermToGraph env singleArg
                        -- Pass the graph node directly to REF - NO REDUCE!
                        -- The runtime will reduce args before calling the function
                        emitLetTmp termType (OpGraphRef fName (OpVar argNode))
                    _ -> error $ "Circuit.ToGraph: multi-arg function calls not yet supported: " ++ fName
            C.CVar fName _ ->
                case lookupBinding fName env of
                    Nothing -> do
                        -- Global function reference
                        case args of
                            [singleArg] -> do
                                argNode <- lowerTermToGraph env singleArg
                                -- NO REDUCE - just pass the graph node
                                emitLetTmp termType (OpGraphRef fName (OpVar argNode))
                            _ -> error $ "Circuit.ToGraph: multi-arg calls not supported: " ++ fName
                    Just _funNode -> do
                        -- Higher-order function (variable holds function)
                        -- For now, error - would need APP node
                        error "Circuit.ToGraph: higher-order functions not yet supported"
            _ -> error "Circuit.ToGraph: complex function expressions not supported"

    -- Function references (bare, not applied)
    C.CRef _name _ ->
        error "Circuit.ToGraph: bare function reference - use in application context"
    -- Booleans - encode as integers
    C.CBool b -> do
        let n = if b then 1 else 0
        emitLetTmp termType (OpGraphNum (OpConst (CInt n)))

    -- Erasure - ERA node (shouldn't appear without linearization, but handle it)
    C.CEra -> do
        emitLetTmp termType OpGraphEra

    -- Superposition (shouldn't appear without linearization)
    C.CSup _label _left _right _ty ->
        error "Circuit.ToGraph: SUP nodes should not appear without linearization"
    -- Duplication (shouldn't appear without linearization)
    C.CDup _name _valTy _label _val _body ->
        error "Circuit.ToGraph: DUP nodes should not appear without linearization"
    -- Dup projections (shouldn't appear without linearization)
    C.CDp0 _name _ty ->
        error "Circuit.ToGraph: CDp0 should not appear without linearization"
    C.CDp1 _name _ty ->
        error "Circuit.ToGraph: CDp1 should not appear without linearization"
    -- Lambda: create LAM node
    C.CLam paramName _paramTy body -> do
        -- Allocate a slot for the variable
        varSlot <- emitLetTmp termType (OpGraphNum (OpConst (CInt 0)))
        let env' = extendBinding paramName varSlot env
        bodyNode <- lowerTermToGraph env' body
        emitLetTmp termType (OpGraphLam (OpVar varSlot) (OpVar bodyNode))

    -- Case expressions on integers
    C.CCase scrut arms mDefault _resultTy -> do
        -- Get native int for switching
        -- If scrutinee is a variable, we already have the native int
        -- Otherwise we'd need to reduce a graph node (but this shouldn't happen
        -- in well-formed graph code for fib-like patterns)
        scrutVal <- case scrut of
            C.CVar name _ ->
                case lookupBinding name env of
                    Just varName -> pure varName -- Already a native int
                    Nothing -> error $ "Circuit.ToGraph: unbound scrutinee: " ++ name
            C.CInt n -> do
                -- Literal - just use it directly for the switch
                emitLetTmp intType (OpBin IAdd (OpConst (CInt n)) (OpConst (CInt 0)))
            _ -> do
                -- Complex scrutinee - build graph and reduce
                -- This is less efficient but handles general cases
                scrutNode <- lowerTermToGraph env scrut
                emitLetTmp intType (OpGraphReduce (OpVar scrutNode))

        caseResultBlock <- freshBlockName
        armBlocks <- forM arms $ \_ -> freshBlockName
        defaultBlock <- case mDefault of
            Just _ -> freshBlockName
            Nothing -> case armBlocks of
                (b : _) -> pure b
                [] -> freshBlockName

        let cases = zip [tag | (tag, _, _) <- arms] armBlocks

        terminate (ASwitch (OpVar scrutVal) cases (Just defaultBlock))

        forM_ (zip armBlocks arms) $ \(blockName, (_tag, bindings, body)) -> do
            beginBlock blockName []
            -- Bind pattern variables to the scrutinee value
            -- For integer patterns, the value is the scrutinee itself
            let env' = foldr (\(n, _) e -> extendBinding n scrutVal e) env bindings
            result <- lowerTermToGraph env' body
            terminate (ABr caseResultBlock [(OpVar result)])

        case mDefault of
            Just defBody -> do
                beginBlock defaultBlock []
                result <- lowerTermToGraph env defBody
                terminate (ABr caseResultBlock [(OpVar result)])
            Nothing -> pure ()

        beginBlock caseResultBlock [("case_result_val", termType)]
        pure "case_result_val"

    -- Tagged values (ADT constructors)
    C.CTag tag fields _ty -> do
        case fields of
            [] -> emitLetTmp termType (OpGraphNum (OpConst (CInt tag)))
            _ -> error "Circuit.ToGraph: constructors with fields not yet supported"

    -- Comparison operations
    C.CCmpOp op a b -> do
        aNode <- lowerTermToGraph env a
        bNode <- lowerTermToGraph env b
        aVal <- emitLetTmp intType (OpGraphReduce (OpVar aNode))
        bVal <- emitLetTmp intType (OpGraphReduce (OpVar bNode))
        let cmpOp = case op of
                C.OpEq -> CEq
                C.OpNe -> CNe
                C.OpLt -> CSlt
                C.OpLe -> CSle
                C.OpGt -> CSgt
                C.OpGe -> CSge
        boolResult <- emitLetTmp intType (OpCmp cmpOp (OpVar aVal) (OpVar bVal))
        intResult <- emitLetTmp intType (OpBin IAdd (OpVar boolResult) (OpConst (CInt 0)))
        emitLetTmp termType (OpGraphNum (OpVar intResult))

    -- Unary operations
    C.CUnaryOp op a -> do
        aNode <- lowerTermToGraph env a
        case op of
            C.OpNeg -> do
                zeroNode <- emitLetTmp termType (OpGraphNum (OpConst (CInt 0)))
                emitLetTmp termType (OpGraphSub (OpVar zeroNode) (OpVar aNode))
            C.OpNot -> do
                aVal <- emitLetTmp intType (OpGraphReduce (OpVar aNode))
                notVal <- emitLetTmp intType (OpCmp CEq (OpVar aVal) (OpConst (CInt 0)))
                intVal <- emitLetTmp intType (OpBin IAdd (OpVar notVal) (OpConst (CInt 0)))
                emitLetTmp termType (OpGraphNum (OpVar intVal))

    -- Closures with captured environment
    C.CClosure liftedName capturedVars _ty -> do
        if null capturedVars
            then emitLetTmp termType (OpGraphNum (OpConst (CInt 0)))
            else error $ "Circuit.ToGraph: closures with captures not yet supported: " ++ liftedName

    -- Unsupported constructs
    C.CClosureGetEnv _ _ _ ->
        error "Circuit.ToGraph: closure env access not yet supported in graph mode"
    C.CProject _ _ _ ->
        error "Circuit.ToGraph: field projection not yet supported in graph mode"
    C.CStr _ ->
        error "Circuit.ToGraph: strings not yet supported in graph mode"
    C.CPanic msg _ ->
        error $ "Circuit.ToGraph: panic: " ++ msg

{- | Try to get a native int value for a term without building graph nodes.
Returns Just varName if the term is a simple var/literal, Nothing otherwise.
-}
tryGetNative :: GraphEnv -> C.CTerm -> AlloyBuilder (Maybe String)
tryGetNative env term = case term of
    C.CVar name _ ->
        case lookupBinding name env of
            Just varName -> pure (Just varName)
            Nothing -> pure Nothing
    C.CInt n -> do
        -- Emit a constant as a native int
        tmp <- emitLetTmp intType (OpBin IAdd (OpConst (CInt n)) (OpConst (CInt 0)))
        pure (Just tmp)
    _ -> pure Nothing

-- | Helper to collect function and arguments from nested CApp
collectArgs :: C.CTerm -> (C.CTerm, [C.CTerm])
collectArgs (C.CApp f x _) =
    let (fun, args) = collectArgs f
    in (fun, args ++ [x])
collectArgs other = (other, [])
