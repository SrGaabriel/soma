{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

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
import Control.Monad (foldM, forM, forM_)
import Data.List (isPrefixOf)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Typing.Types (Kind (..), TyConstructor (..), Type (..), boolType, intType)

-- | Term type for graph operations (64-bit)
termType :: Type
termType = TConstructor (TypeConstructor "Long" KindStar)

-- | Environment for graph lowering
data GraphEnv = GraphEnv
    { geBindings :: Map C.Name String
    -- ^ Circuit name -> Alloy variable name (holding native Int value or Term)
    , geFuncIndices :: Map C.Name Int
    -- ^ Function name -> runtime function index
    , geIsTermBinding :: Map C.Name Bool
    -- ^ Whether the binding holds a Term (graph node) vs native Int
    }

emptyGraphEnv :: GraphEnv
emptyGraphEnv = GraphEnv Map.empty Map.empty Map.empty

-- | Look up a binding
lookupBinding :: C.Name -> GraphEnv -> Maybe String
lookupBinding name = Map.lookup name . geBindings

-- | Check if a binding holds a Term (vs native Int)
isTermBinding :: C.Name -> GraphEnv -> Bool
isTermBinding name env = Map.findWithDefault False name (geIsTermBinding env)

-- | Extend environment with a native Int binding
extendBinding :: C.Name -> String -> GraphEnv -> GraphEnv
extendBinding name varName env =
    env{geBindings = Map.insert name varName (geBindings env)}

-- | Extend environment with a Term binding (graph node)
extendTermBinding :: C.Name -> String -> GraphEnv -> GraphEnv
extendTermBinding name varName env =
    env
        { geBindings = Map.insert name varName (geBindings env)
        , geIsTermBinding = Map.insert name True (geIsTermBinding env)
        }

-- | Look up function index
lookupFuncIndex :: C.Name -> GraphEnv -> Maybe Int
lookupFuncIndex name = Map.lookup name . geFuncIndices

-- | Lower a Circuit module to an Alloy module using graph reduction
lowerCircuitToGraph :: C.CModule -> AlloyModule
lowerCircuitToGraph cmod =
    let (_, alloyMod) = runAlloyBuilder (C.cmName cmod) [] $ lowerToGraphMain cmod
    in alloyMod

-- | Generate the main entry point and all functions for graph reduction
lowerToGraphMain :: C.CModule -> AlloyBuilder ()
lowerToGraphMain cmod = do
    let mainFuncs = filter (\f -> C.cfName f == "main") (C.cmFunctions cmod)
        otherFuncs = filter (\f -> C.cfName f /= "main") (C.cmFunctions cmod)

        -- Build function index map (function name -> index)
        funcIndexMap = Map.fromList $ zip (map C.cfName otherFuncs) [0 ..]

    case mainFuncs of
        [] -> error "Circuit.ToGraph: no main function found"
        (mainFunc : _) -> do
            -- Generate graph-building functions for each non-main function
            forM_ otherFuncs $ \f -> lowerFunctionForGraph funcIndexMap f

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

            -- Build the graph for the main function body with function indices
            let env = emptyGraphEnv{geFuncIndices = funcIndexMap}
            resultNode <- lowerTermToGraph env (C.cfBody mainFunc)

            -- Reduce the graph and get result
            resultVal <- emitLetTmp intType (OpGraphReduce (OpVar resultNode))

            terminate (ARet (Just (OpVar resultVal)))
            endFunction

{- | Lower a function to be callable from graph reduction.

The function receives (net, tm, arg) and returns a Term.
The runtime calls these functions as INetFunc: (INet*, ThreadMem*, Term) -> Term

For regular functions: arg is a NUM, we extract the int value.
For closure functions: arg is a CLO, we extract env values from it.

CRITICAL: We use OpGraphExtractNum to get the native int from arg.
The runtime has ALREADY reduced the arg to a NUM before calling us.
We must NOT call inet_reduce internally - that causes nested parallel reductions!
-}
lowerFunctionForGraph :: Map C.Name Int -> C.CFunction -> AlloyBuilder ()
lowerFunctionForGraph funcIndexMap C.CFunction{..} = do
    -- Function signature: (net: ptr, tm: ptr, arg: Term) -> Term
    -- This matches the INetFunc typedef in soma_inet.h
    let ptrType = TConstructor (TypeConstructor "Ptr" KindStar)
    beginFunction cfName [("net", ptrType), ("tm", ptrType), ("arg", termType)] termType

    entryBlock <- freshBlockName
    beginBlock entryBlock []

    -- Check if this is a closure function (first param is closure_self)
    let isClosureFunc = case cfParams of
            ((pname, _) : _) -> pname == "closure_self"
            [] -> False

    env <-
        if isClosureFunc
            then do
                -- For closure functions, arg is the closure itself (CLO term)
                -- containing [captured_vars..., applied_arg]
                -- We bind closure_self to the raw term for CClosureGetEnv to use
                let baseEnv =
                        extendTermBinding "closure_self" "arg"
                            $ emptyGraphEnv{geFuncIndices = funcIndexMap}
                -- The second parameter (e.g., 'y') is the applied argument
                -- It's stored as the LAST element in the closure's env
                -- Count captured vars by finding max CClosureGetEnv index in body
                let numCaptured = countCapturedVars cfBody
                case cfParams of
                    [_, (argName, _)] -> do
                        -- Extract the applied arg from the last env slot
                        -- It's a Term (graph node), need to reduce to get native int
                        argTerm <- emitLetTmp termType (OpGraphClosureGetEnv (OpVar "arg") numCaptured)
                        argVal <- emitLetTmp intType (OpGraphExtractNum (OpVar argTerm))
                        pure $ extendBinding argName argVal baseEnv
                    _ -> pure baseEnv
            else do
                -- For regular functions, the arg is the FIRST parameter.
                -- Multi-arg functions are curried: f(a,b,c) becomes a closure
                -- that captures earlier args. But at the Circuit level, all params
                -- are listed. We need to bind ALL params from the closure's env.
                --
                -- If there's only 1 param: arg is the value directly
                -- If there are N params: arg is a closure with [param0..paramN-2, paramN-1]
                let baseEnv = emptyGraphEnv{geFuncIndices = funcIndexMap}
                case cfParams of
                    [] -> pure baseEnv
                    [(pname, _)] -> do
                        -- Single param: extract directly from arg
                        argVal <- emitLetTmp intType (OpGraphExtractNum (OpVar "arg"))
                        pure $ extendBinding pname argVal baseEnv
                    params -> do
                        -- Multi-param: arg is a closure containing all params
                        -- Layout: [param0, param1, ..., paramN-1]
                        let numParams = length params
                        foldM
                            ( \e (idx, (pname, _)) -> do
                                paramTerm <- emitLetTmp termType (OpGraphClosureGetEnv (OpVar "arg") idx)
                                paramVal <- emitLetTmp intType (OpGraphExtractNum (OpVar paramTerm))
                                pure $ extendBinding pname paramVal e
                            )
                            baseEnv
                            (zip [0 .. numParams - 1] params)

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
lowerTermToGraph env = \case
    -- Integer literals become NUM nodes
    C.CInt n -> emitLetTmp termType (OpGraphNum (OpConst (CInt n)))
    -- Variables: check if term binding (closure) or native value
    C.CVar name _ ->
        if isTermBinding name env
            then do
                -- Term binding (closure) - return as-is, no wrapping
                case lookupBinding name env of
                    Just varName -> pure varName
                    Nothing -> error $ "Circuit.ToGraph: term binding not found: " ++ name
            else case lookupBinding name env of
                Just varName -> do
                    -- Native value -> wrap in graph node
                    emitLetTmp termType (OpGraphNum (OpVar varName))
                Nothing -> error $ "Circuit.ToGraph: unbound variable: " ++ name
    -- Let bindings
    C.CLet name _ty val body -> do
        -- Build graph for val
        valNode <- lowerTermToGraph env val
        -- CRITICAL: In graph mode, NEVER call inet_reduce internally!
        -- All values stay as graph Terms. The runtime reduces lazily.
        -- This is essential for parallel correctness - nested inet_reduce
        -- corrupts global parallel state.
        let env' = extendTermBinding name valNode env
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
                        C.OpDiv -> IDiv
                        C.OpMod -> IMod
                        u -> error $ "Circuit.ToGraph: unsupported binary op in graph mode: " ++ show u
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
                        C.OpDiv -> OpGraphDiv (OpVar aNode) (OpVar bNode)
                        C.OpMod -> OpGraphMod (OpVar aNode) (OpVar bNode)
                        u -> error $ "Circuit.ToGraph: unsupported binary op in graph mode: " ++ show u
                emitLetTmp termType nodeOp

    -- Function applications become REF or APP nodes
    -- CRITICAL: Do NOT reduce the argument here!
    -- Just build the node, let runtime reduce.
    term@(C.CApp _fun _arg _resultTy) -> do
        let (f, args) = collectArgs term
        case f of
            C.CRef fName _ -> do
                case lookupFuncIndex fName env of
                    Nothing -> error $ "Circuit.ToGraph: function not registered: " ++ fName
                    Just funcIdx -> case args of
                        [singleArg] -> do
                            -- Single arg: build graph and pass directly to REF
                            argNode <- lowerTermToGraph env singleArg
                            emitLetTmp termType (OpGraphRef fName funcIdx (OpVar argNode))
                        multiArgs -> do
                            -- Multi-arg: bundle all args into a closure, pass to REF
                            -- The function will extract args from the closure's env
                            argNodes <- mapM (lowerTermToGraph env) multiArgs
                            let argOps = map OpVar argNodes
                            -- Create a closure containing all args
                            argsClosure <- emitLetTmp termType (OpGraphClosure funcIdx 0 argOps)
                            emitLetTmp termType (OpGraphRef fName funcIdx (OpVar argsClosure))
            C.CVar fName _ ->
                case lookupBinding fName env of
                    Nothing -> do
                        -- Check if this is a closure function (lambda$N pattern)
                        -- Closure functions take (closure_self, arg) - 2 args
                        if "lambda$" `isPrefixOf` fName && length args == 2
                            then do
                                -- Closure function call: lambda$N closure arg
                                -- The closure already contains the function reference
                                -- Just create APP(closure, arg) - runtime handles APP-CLO
                                let [closureArg, actualArg] = args
                                closureNode <- lowerTermToGraph env closureArg
                                argNode <- lowerTermToGraph env actualArg
                                emitLetTmp termType (OpGraphClosureApp (OpVar closureNode) (OpVar argNode))
                            else case lookupFuncIndex fName env of
                                Nothing -> error $ "Circuit.ToGraph: function not registered: " ++ fName
                                Just funcIdx -> case args of
                                    [singleArg] -> do
                                        argNode <- lowerTermToGraph env singleArg
                                        -- NO REDUCE - just pass the graph node
                                        emitLetTmp termType (OpGraphRef fName funcIdx (OpVar argNode))
                                    multiArgs -> do
                                        -- Multi-arg: bundle all args into a closure, pass to REF
                                        -- Same as CRef case for recursive calls
                                        argNodes <- mapM (lowerTermToGraph env) multiArgs
                                        let argOps = map OpVar argNodes
                                        argsClosure <- emitLetTmp termType (OpGraphClosure funcIdx 0 argOps)
                                        emitLetTmp termType (OpGraphRef fName funcIdx (OpVar argsClosure))
                    Just funNode -> do
                        -- Higher-order function (variable holds closure)
                        -- Create APP(closure, arg)
                        case args of
                            [singleArg] -> do
                                argNode <- lowerTermToGraph env singleArg
                                emitLetTmp termType (OpGraphClosureApp (OpVar funNode) (OpVar argNode))
                            _ -> error "Circuit.ToGraph: multi-arg higher-order calls not supported"
            _ -> error "Circuit.ToGraph: complex function expressions not supported"

    -- Function references (bare, not applied)
    C.CRef _name _ ->
        error "Circuit.ToGraph: bare function reference - use in application context"
    -- Booleans - encode as integers
    C.CBool b -> do
        let n = if b then 1 else 0
        emitLetTmp termType (OpGraphNum (OpConst (CInt n)))

    -- Erasure - ERA node (shouldn't appear without linearization, but handle it)
    C.CEra -> emitLetTmp termType OpGraphEra
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
        armBlocks <- forM arms $ const freshBlockName
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
            terminate (ABr caseResultBlock [OpVar result])

        case mDefault of
            Just defBody -> do
                beginBlock defaultBlock []
                result <- lowerTermToGraph env defBody
                terminate (ABr caseResultBlock [OpVar result])
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
        -- Try to get native values for comparison (avoid graph_reduce inside graph functions!)
        maNative <- tryGetNative env a
        mbNative <- tryGetNative env b
        let cmpOp = case op of
                C.OpEq -> CEq
                C.OpNe -> CNe
                C.OpLt -> CSlt
                C.OpLe -> CSle
                C.OpGt -> CSgt
                C.OpGe -> CSge
        (aVal, bVal) <- case (maNative, mbNative) of
            (Just aNative, Just bNative) ->
                -- Both are native - compare directly
                pure (aNative, bNative)
            (Just aNative, Nothing) -> do
                -- a is native, b needs extraction from graph
                bNode <- lowerTermToGraph env b
                bExtracted <- emitLetTmp intType (OpGraphExtractNum (OpVar bNode))
                pure (aNative, bExtracted)
            (Nothing, Just bNative) -> do
                -- b is native, a needs extraction from graph
                aNode <- lowerTermToGraph env a
                aExtracted <- emitLetTmp intType (OpGraphExtractNum (OpVar aNode))
                pure (aExtracted, bNative)
            (Nothing, Nothing) -> do
                -- Both need extraction - build graph nodes and extract
                aNode <- lowerTermToGraph env a
                bNode <- lowerTermToGraph env b
                aExtracted <- emitLetTmp intType (OpGraphExtractNum (OpVar aNode))
                bExtracted <- emitLetTmp intType (OpGraphExtractNum (OpVar bNode))
                pure (aExtracted, bExtracted)
        boolResult <- emitLetTmp boolType (OpCmp cmpOp (OpVar aVal) (OpVar bVal))
        -- Convert bool to int: select between 1 and 0
        -- NOTE: Return native int, not graph node! Case expressions need native ints for switching.
        emitLetTmp intType (OpSelect (OpVar boolResult) (OpConst (CInt 1)) (OpConst (CInt 0)))

    -- Unary operations
    C.CUnaryOp op a -> do
        aNode <- lowerTermToGraph env a
        case op of
            C.OpNeg -> do
                zeroNode <- emitLetTmp termType (OpGraphNum (OpConst (CInt 0)))
                emitLetTmp termType (OpGraphSub (OpVar zeroNode) (OpVar aNode))
            C.OpNot -> do
                aVal <- emitLetTmp intType (OpGraphReduce (OpVar aNode))
                notVal <- emitLetTmp boolType (OpCmp CEq (OpVar aVal) (OpConst (CInt 0)))
                -- Convert bool to int: select between 1 and 0
                intVal <- emitLetTmp intType (OpSelect (OpVar notVal) (OpConst (CInt 1)) (OpConst (CInt 0)))
                emitLetTmp termType (OpGraphNum (OpVar intVal))

    -- Closures with captured environment
    C.CClosure liftedName capturedVars _ty -> do
        -- Look up the function index for the lifted function
        case lookupFuncIndex liftedName env of
            Nothing -> error $ "Circuit.ToGraph: unknown lifted function: " ++ liftedName
            Just funcIdx -> do
                if null capturedVars
                    then do
                        -- No captures - create closure with empty env, arity 1
                        emitLetTmp termType (OpGraphClosure funcIdx 1 [])
                    else do
                        -- Build graph nodes for each captured variable
                        envNodes <- forM capturedVars $ \(varName, _varTy) -> do
                            case lookupBinding varName env of
                                Nothing -> error $ "Circuit.ToGraph: unbound captured var: " ++ varName
                                Just boundName -> do
                                    if isTermBinding varName env
                                        then pure (OpVar boundName) -- Already a Term
                                        else do
                                            -- Native int -> wrap in graph node
                                            node <- emitLetTmp termType (OpGraphNum (OpVar boundName))
                                            pure (OpVar node)
                        -- Create closure with captured environment, arity 1
                        -- (closure functions take one more arg after the captured env is applied)
                        emitLetTmp termType (OpGraphClosure funcIdx 1 envNodes)

    -- Extract captured variable from closure's environment
    C.CClosureGetEnv closureExpr idx _ty -> do
        -- Get the closure term
        closureVar <- case closureExpr of
            C.CVar name _ ->
                case lookupBinding name env of
                    Just varName -> pure varName
                    Nothing -> error $ "Circuit.ToGraph: unbound closure: " ++ name
            _ -> error "Circuit.ToGraph: CClosureGetEnv expects a variable"
        -- Extract env value at index - this reads from the closure's env array
        -- The result is a Term (graph node)
        emitLetTmp termType (OpGraphClosureGetEnv (OpVar closureVar) idx)
    C.CProject{} ->
        error "Circuit.ToGraph: field projection not yet supported in graph mode"
    C.CStr _ ->
        error "Circuit.ToGraph: strings not yet supported in graph mode"
    C.CPanic msg _ ->
        error $ "Circuit.ToGraph: panic: " ++ msg
    C.CFork{} ->
        error "Circuit.ToGraph: forking not supported in graph mode"
    C.CJoin{} ->
        error "Circuit.ToGraph: joining not supported in graph mode"

{- | Try to get a native int value for a term without building graph nodes.
Returns Just varName if the term is a simple var/literal, Nothing otherwise.
-}
tryGetNative :: GraphEnv -> C.CTerm -> AlloyBuilder (Maybe String)
tryGetNative env term = case term of
    C.CVar name _ ->
        -- Only return native value if it's NOT a term binding
        -- Term bindings hold graph Terms, not native ints
        if isTermBinding name env
            then pure Nothing
            else case lookupBinding name env of
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

{- | Count the number of captured variables in a closure function body.
This finds the maximum index used in CClosureGetEnv + 1.
-}
countCapturedVars :: C.CTerm -> Int
countCapturedVars = go 0
  where
    go acc term = case term of
        C.CClosureGetEnv _ idx _ -> max acc (idx + 1)
        C.CLet _ _ val body -> go (go acc val) body
        C.CApp f x _ -> go (go acc f) x
        C.CBinOp _ a b -> go (go acc a) b
        C.CCmpOp _ a b -> go (go acc a) b
        C.CUnaryOp _ a -> go acc a
        C.CLam _ _ body -> go acc body
        C.CCase scrut arms mdef _ ->
            let acc' = go acc scrut
                acc'' = foldl (\a (_, _, body) -> go a body) acc' arms
            in maybe acc'' (go acc'') mdef
        C.CClosure _ caps _ -> foldl (\a (_, _) -> a) acc caps
        C.CProject e _ _ -> go acc e
        C.CSup _ l r _ -> go (go acc l) r
        C.CDup _ _ _ v b -> go (go acc v) b
        _ -> acc
