{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

{- | Circuit to Linearized Graph Reduction lowering.

This module lowers LINEARIZED Circuit IR to Alloy MIR that uses the
INET C runtime for parallel graph reduction.

1. Every variable is used exactly once (affine)
2. DUP/ERA nodes are explicit in the IR
3. The compiler has already decided where duplication happens

This enables compile-time optimizations:
- DUP on primitive types (Int, Bool) can be elided (just copy the value)
- The exact duplication structure is known at compile time
- No runtime sharing detection needed

== PURE GRAPH MODEL ==

Functions return graph nodes (Terms), NOT reduced values. The runtime
reduces the graph lazily with work-stealing parallelism.

Key principles:
1. Function calls become REF nodes (inet_ref) - NOT direct calls
2. The runtime calls registered functions when it encounters REF nodes
3. All computation is represented as graph nodes
4. Only the final result is reduced to a value
5. DUP/SUP nodes are explicit from linearization
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

-- | Check if a type is a primitive (can be copied without DUP node)
isPrimitiveType :: Type -> Bool
isPrimitiveType (TConstructor tc) =
    tcName tc `elem` ["Int", "Bool", "Byte", "Char", "Unit", "Long"]
isPrimitiveType _ = False

-- | Environment for linearized graph lowering
data LGraphEnv = LGraphEnv
    { lgeBindings :: Map C.Name String
    -- ^ Circuit name -> Alloy variable name (holding native Int value or Term)
    , lgeFuncIndices :: Map C.Name Int
    -- ^ Function name -> runtime function index
    , lgeIsTermBinding :: Map C.Name Bool
    -- ^ Whether the binding holds a Term (graph node) vs native Int
    , lgeDupProjections :: Map C.Name (String, String)
    -- ^ DUP name -> (proj0 var, proj1 var) for accessing projected values
    , lgeDupNodes :: Map C.Name String
    {- ^ DUP name -> Alloy var holding the DUP node (for non-primitive DUP)
    Used by CDp0/CDp1 to emit OpGraphDupGetProj0/1
    -}
    }

emptyLGraphEnv :: LGraphEnv
emptyLGraphEnv = LGraphEnv Map.empty Map.empty Map.empty Map.empty Map.empty

-- | Look up a binding
lookupBinding :: C.Name -> LGraphEnv -> Maybe String
lookupBinding name = Map.lookup name . lgeBindings

-- | Check if a binding holds a Term (vs native Int)
isTermBinding :: C.Name -> LGraphEnv -> Bool
isTermBinding name env = Map.findWithDefault False name (lgeIsTermBinding env)

-- | Extend environment with a native Int binding
extendBinding :: C.Name -> String -> LGraphEnv -> LGraphEnv
extendBinding name varName env =
    env{lgeBindings = Map.insert name varName (lgeBindings env)}

-- | Extend environment with a Term binding (graph node)
extendTermBinding :: C.Name -> String -> LGraphEnv -> LGraphEnv
extendTermBinding name varName env =
    env
        { lgeBindings = Map.insert name varName (lgeBindings env)
        , lgeIsTermBinding = Map.insert name True (lgeIsTermBinding env)
        }

-- | Look up function index
lookupFuncIndex :: C.Name -> LGraphEnv -> Maybe Int
lookupFuncIndex name = Map.lookup name . lgeFuncIndices

-- | Record DUP projections
recordDupProj :: C.Name -> String -> String -> LGraphEnv -> LGraphEnv
recordDupProj name proj0 proj1 env =
    env{lgeDupProjections = Map.insert name (proj0, proj1) (lgeDupProjections env)}

-- | Record a DUP node for non-primitive duplication
recordDupNode :: C.Name -> String -> LGraphEnv -> LGraphEnv
recordDupNode name dupVar env =
    env{lgeDupNodes = Map.insert name dupVar (lgeDupNodes env)}

-- | Look up a DUP node
lookupDupNode :: C.Name -> LGraphEnv -> Maybe String
lookupDupNode name = Map.lookup name . lgeDupNodes

-- | Lower a Circuit module to an Alloy module using linearized graph reduction
lowerCircuitToGraph :: C.CModule -> AlloyModule
lowerCircuitToGraph cmod =
    let (_, alloyMod) = runAlloyBuilder (C.cmName cmod) [] $ lowerToLGraphMain cmod
    in alloyMod

-- | Generate the main entry point and all functions for linearized graph reduction
lowerToLGraphMain :: C.CModule -> AlloyBuilder ()
lowerToLGraphMain cmod = do
    let mainFuncs = filter (\f -> C.cfName f == "main") (C.cmFunctions cmod)
        otherFuncs = filter (\f -> C.cfName f /= "main") (C.cmFunctions cmod)

        -- Build function index map (function name -> index)
        funcIndexMap = Map.fromList $ zip (map C.cfName otherFuncs) [0 ..]

    case mainFuncs of
        [] -> error "Circuit.ToGraph: no main function found"
        (mainFunc : _) -> do
            -- Generate graph-building functions for each non-main function
            forM_ otherFuncs $ \f -> lowerFunctionForLGraph funcIndexMap f

            -- Generate the main function
            beginFunction "main" [] intType

            entryBlock <- freshBlockName
            beginBlock entryBlock []

            -- Register all functions with the runtime
            forM_ otherFuncs $ \f -> do
                let fname = C.cfName f
                    arity = length (C.cfParams f)
                emitEffect (EffGraphRegisterFunc fname arity (OpVar fname))

            -- Build the graph for the main function body with function indices
            let env = emptyLGraphEnv{lgeFuncIndices = funcIndexMap}
            resultNode <- lowerTermToLGraph env (C.cfBody mainFunc)

            -- Reduce the graph and get result
            resultVal <- emitLetTmp intType (OpGraphReduce (OpVar resultNode))

            terminate (ARet (Just (OpVar resultVal)))
            endFunction

{- | Lower a function to be callable from linearized graph reduction.

Similar to ToGraph.hs but handles linearized Circuit IR with explicit DUP nodes.
-}
lowerFunctionForLGraph :: Map C.Name Int -> C.CFunction -> AlloyBuilder ()
lowerFunctionForLGraph funcIndexMap C.CFunction{..} = do
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
                let baseEnv =
                        extendTermBinding "closure_self" "arg"
                            $ emptyLGraphEnv{lgeFuncIndices = funcIndexMap}
                let numCaptured = countCapturedVars cfBody
                case cfParams of
                    [_, (argName, _)] -> do
                        argTerm <- emitLetTmp termType (OpGraphClosureGetEnv (OpVar "arg") numCaptured)
                        argVal <- emitLetTmp intType (OpGraphExtractNum (OpVar argTerm))
                        pure $ extendBinding argName argVal baseEnv
                    _ -> pure baseEnv
            else do
                let baseEnv = emptyLGraphEnv{lgeFuncIndices = funcIndexMap}
                case cfParams of
                    [] -> pure baseEnv
                    [(pname, pty)] ->
                        -- For ADT parameters, bind as Term; for primitives, extract int
                        if isPrimitiveType pty
                            then do
                                argVal <- emitLetTmp intType (OpGraphExtractNum (OpVar "arg"))
                                pure $ extendBinding pname argVal baseEnv
                            else
                                -- ADT parameter: bind the Term directly
                                pure $ extendTermBinding pname "arg" baseEnv
                    params -> do
                        let numParams = length params
                        foldM
                            ( \e (idx, (pname, pty)) -> do
                                paramTerm <- emitLetTmp termType (OpGraphClosureGetEnv (OpVar "arg") idx)
                                if isPrimitiveType pty
                                    then do
                                        paramVal <- emitLetTmp intType (OpGraphExtractNum (OpVar paramTerm))
                                        pure $ extendBinding pname paramVal e
                                    else
                                        -- ADT parameter: bind the Term directly
                                        pure $ extendTermBinding pname paramTerm e
                            )
                            baseEnv
                            (zip [0 .. numParams - 1] params)

    -- Lower the body - this returns a graph node (Term)
    result <- lowerTermToLGraph env cfBody

    -- Return the term (graph node) - NOT reduced!
    terminate (ARet (Just (OpVar result)))
    endFunction

{- | Lower a linearized Circuit term to graph construction.

CRITICAL DIFFERENCE FROM ToGraph.hs:
- Handles CDup, CDp0, CDp1 nodes from linearization
- Can optimize DUP for primitive types (no graph DUP node needed)
- Uses explicit duplication structure from the compiler

Returns the name of the variable holding the graph node (Term).
-}
lowerTermToLGraph :: LGraphEnv -> C.CTerm -> AlloyBuilder String
lowerTermToLGraph env = \case
    -- Integer literals become NUM nodes
    C.CInt n -> emitLetTmp termType (OpGraphNum (OpConst (CInt n)))
    -- Variables: check if term binding (closure) or native value
    C.CVar name _ ->
        if isTermBinding name env
            then do
                case lookupBinding name env of
                    Just varName -> pure varName
                    Nothing -> error $ "Circuit.ToGraph: term binding not found: " ++ name
            else case lookupBinding name env of
                Just varName -> do
                    emitLetTmp termType (OpGraphNum (OpVar varName))
                Nothing -> error $ "Circuit.ToGraph: unbound variable: " ++ name
    -- Let bindings
    C.CLet name _ty val body -> do
        valNode <- lowerTermToLGraph env val
        let env' = extendTermBinding name valNode env
        lowerTermToLGraph env' body

    -- Binary operations: compute natively when operands are simple
    C.CBinOp op a b -> do
        maNative <- tryGetNative env a
        mbNative <- tryGetNative env b
        case (maNative, mbNative) of
            (Just aNative, Just bNative) -> do
                let binOp = case op of
                        C.OpAdd -> IAdd
                        C.OpSub -> ISub
                        C.OpMul -> IMul
                        C.OpDiv -> IDiv
                        C.OpMod -> IMod
                        u -> error $ "Circuit.ToGraph: unsupported binary op: " ++ show u
                nativeResult <- emitLetTmp intType (OpBin binOp (OpVar aNative) (OpVar bNative))
                emitLetTmp termType (OpGraphNum (OpVar nativeResult))
            _ -> do
                aNode <- lowerTermToLGraph env a
                bNode <- lowerTermToLGraph env b
                let nodeOp = case op of
                        C.OpAdd -> OpGraphAdd (OpVar aNode) (OpVar bNode)
                        C.OpSub -> OpGraphSub (OpVar aNode) (OpVar bNode)
                        C.OpMul -> OpGraphMul (OpVar aNode) (OpVar bNode)
                        C.OpDiv -> OpGraphDiv (OpVar aNode) (OpVar bNode)
                        C.OpMod -> OpGraphMod (OpVar aNode) (OpVar bNode)
                        u -> error $ "Circuit.ToGraph: unsupported binary op: " ++ show u
                emitLetTmp termType nodeOp

    -- Duplication node (from linearization)
    -- KEY OPTIMIZATION: For primitive types, we keep the native value directly
    -- without creating a DUP graph node. This is critical for performance!
    C.CDup name valTy label val body -> do
        if isPrimitiveType valTy
            then do
                -- Primitive type: try to get native value directly
                -- Don't lower to graph node - keep as native int for efficient ops
                mNative <- tryGetNative env val
                case mNative of
                    Just nativeVal -> do
                        -- Keep as native binding for both projections
                        let env' =
                                recordDupProj name nativeVal nativeVal
                                    $ extendBinding (name ++ ".0") nativeVal
                                    $ extendBinding (name ++ ".1") nativeVal env
                        lowerTermToLGraph env' body
                    Nothing -> do
                        -- Value is a Term - extract the native value
                        valNode <- lowerTermToLGraph env val
                        nativeVal <- emitLetTmp intType (OpGraphExtractNum (OpVar valNode))
                        let env' =
                                recordDupProj name nativeVal nativeVal
                                    $ extendBinding (name ++ ".0") nativeVal
                                    $ extendBinding (name ++ ".1") nativeVal env
                        lowerTermToLGraph env' body
            else do
                -- Non-primitive type: create actual DUP graph node
                -- The DUP node will be resolved during graph reduction
                valNode <- lowerTermToLGraph env val
                dupNode <- emitLetTmp termType (OpGraphDup label (OpVar valNode))
                -- Record the DUP node so CDp0/CDp1 can emit projection ops
                let env' = recordDupNode name dupNode env
                lowerTermToLGraph env' body

    -- First projection from DUP
    -- For non-primitive DUP, emit OpGraphDupGetProj0 to get the projected value
    C.CDp0 name ty ->
        -- First check if this is a non-primitive DUP (recorded in lgeDupNodes)
        case lookupDupNode name env of
            Just dupVar ->
                -- Non-primitive DUP: emit projection operation
                emitLetTmp termType (OpGraphDupGetProj0 (OpVar dupVar))
            Nothing ->
                -- Primitive DUP or direct binding
                case lookupBinding (name ++ ".0") env of
                    Just varName ->
                        if isTermBinding (name ++ ".0") env
                            then pure varName -- Already a Term
                            else
                                -- Native value - wrap in graph_num for graph context
                                if isPrimitiveType ty
                                    then emitLetTmp termType (OpGraphNum (OpVar varName))
                                    else pure varName
                    Nothing -> error $ "Circuit.ToLGraph: unbound projection: " ++ name ++ ".0"
    -- Second projection from DUP
    -- For non-primitive DUP, emit OpGraphDupGetProj1 to get the projected value
    C.CDp1 name ty ->
        -- First check if this is a non-primitive DUP (recorded in lgeDupNodes)
        case lookupDupNode name env of
            Just dupVar ->
                -- Non-primitive DUP: emit projection operation
                emitLetTmp termType (OpGraphDupGetProj1 (OpVar dupVar))
            Nothing ->
                -- Primitive DUP or direct binding
                case lookupBinding (name ++ ".1") env of
                    Just varName ->
                        if isTermBinding (name ++ ".1") env
                            then pure varName -- Already a Term
                            else
                                -- Native value - wrap in graph_num for graph context
                                if isPrimitiveType ty
                                    then emitLetTmp termType (OpGraphNum (OpVar varName))
                                    else pure varName
                    Nothing -> error $ "Circuit.ToGraph: unbound projection: " ++ name ++ ".1"
    -- Superposition node (from linearization)
    C.CSup label left right _ty -> do
        leftNode <- lowerTermToLGraph env left
        rightNode <- lowerTermToLGraph env right
        emitLetTmp termType (OpGraphSup label (OpVar leftNode) (OpVar rightNode))

    -- Erasure node
    C.CEra -> emitLetTmp termType OpGraphEra
    -- Function applications become REF or APP nodes
    term@(C.CApp _fun _arg _resultTy) -> do
        let (f, args) = collectArgs term
        case f of
            C.CRef fName _ -> do
                case lookupFuncIndex fName env of
                    Nothing -> error $ "Circuit.ToGraph: function not registered: " ++ fName
                    Just funcIdx -> case args of
                        [singleArg] -> do
                            argNode <- lowerTermToLGraph env singleArg
                            emitLetTmp termType (OpGraphRef fName funcIdx (OpVar argNode))
                        multiArgs -> do
                            argNodes <- mapM (lowerTermToLGraph env) multiArgs
                            let argOps = map OpVar argNodes
                            argsClosure <- emitLetTmp termType (OpGraphClosure funcIdx 0 argOps)
                            emitLetTmp termType (OpGraphRef fName funcIdx (OpVar argsClosure))
            C.CVar fName _ ->
                case lookupBinding fName env of
                    Nothing -> do
                        if "lambda$" `isPrefixOf` fName && length args == 2
                            then do
                                let [closureArg, actualArg] = args
                                closureNode <- lowerTermToLGraph env closureArg
                                argNode <- lowerTermToLGraph env actualArg
                                emitLetTmp termType (OpGraphClosureApp (OpVar closureNode) (OpVar argNode))
                            else case lookupFuncIndex fName env of
                                Nothing -> error $ "Circuit.ToGraph: function not registered: " ++ fName
                                Just funcIdx -> case args of
                                    [singleArg] -> do
                                        argNode <- lowerTermToLGraph env singleArg
                                        emitLetTmp termType (OpGraphRef fName funcIdx (OpVar argNode))
                                    multiArgs -> do
                                        argNodes <- mapM (lowerTermToLGraph env) multiArgs
                                        let argOps = map OpVar argNodes
                                        argsClosure <- emitLetTmp termType (OpGraphClosure funcIdx 0 argOps)
                                        emitLetTmp termType (OpGraphRef fName funcIdx (OpVar argsClosure))
                    Just funNode -> do
                        case args of
                            [singleArg] -> do
                                argNode <- lowerTermToLGraph env singleArg
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

    -- Lambda: create LAM node
    C.CLam paramName _paramTy body -> do
        varSlot <- emitLetTmp termType (OpGraphNum (OpConst (CInt 0)))
        let env' = extendBinding paramName varSlot env
        bodyNode <- lowerTermToLGraph env' body
        emitLetTmp termType (OpGraphLam (OpVar varSlot) (OpVar bodyNode))

    -- Case expressions on integers
    C.CCase scrut arms mDefault _resultTy -> do
        -- CRITICAL: We must NOT call OpGraphReduce inside graph functions!
        -- Use OpGraphExtractNum to get native int from a Term (assumes already reduced)
        -- or use the native value directly if available
        --
        -- For ADT pattern matching:
        -- 1. scrutNode is the full CON(tag, payload) term
        -- 2. scrutVal is the extracted tag (native int) for switching
        -- 3. Pattern variable bindings extract fields from scrutNode
        (scrutNode, scrutVal) <- case scrut of
            C.CVar name _ ->
                case lookupBinding name env of
                    Just varName ->
                        if isTermBinding name env
                            then do
                                tagVal <- emitLetTmp intType (OpGraphExtractNum (OpVar varName))
                                pure (varName, tagVal)
                            else pure (varName, varName) -- Already a native int (no CON structure)
                    Nothing -> error $ "Circuit.ToGraph: unbound scrutinee: " ++ name
            C.CInt n -> do
                tagVal <- emitLetTmp intType (OpBin IAdd (OpConst (CInt n)) (OpConst (CInt 0)))
                pure (tagVal, tagVal) -- Literal int has no CON structure
            C.CDp0 name _ ->
                case lookupBinding (name ++ ".0") env of
                    Just varName ->
                        if isTermBinding (name ++ ".0") env
                            then do
                                tagVal <- emitLetTmp intType (OpGraphExtractNum (OpVar varName))
                                pure (varName, tagVal)
                            else pure (varName, varName) -- Already a native int
                    Nothing -> error $ "Circuit.ToGraph: unbound projection: " ++ name ++ ".0"
            C.CDp1 name _ ->
                case lookupBinding (name ++ ".1") env of
                    Just varName ->
                        if isTermBinding (name ++ ".1") env
                            then do
                                tagVal <- emitLetTmp intType (OpGraphExtractNum (OpVar varName))
                                pure (varName, tagVal)
                            else pure (varName, varName) -- Already a native int
                    Nothing -> error $ "Circuit.ToGraph: unbound projection: " ++ name ++ ".1"
            _ -> do
                -- For complex scrutinees, build the graph node and extract
                -- This should be rare - most scrutinees are variables or projections
                node <- lowerTermToLGraph env scrut
                tagVal <- emitLetTmp intType (OpGraphExtractNum (OpVar node))
                pure (node, tagVal)

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
            -- Extract fields from the scrutinee CON node for pattern variable bindings
            -- CON structure: CON(tag, payload) where payload is:
            --   - Single field: the field directly
            --   - Multi-field: CON(field0, CON(field1, ...))
            env' <-
                if null bindings
                    then pure env
                    else do
                        -- Get the payload (second element of CON)
                        payload <- emitLetTmp termType (OpGraphConGet (OpVar scrutNode) 1)
                        -- Bind each pattern variable to its corresponding field
                        bindPatternVars env payload bindings
            result <- lowerTermToLGraph env' body
            terminate (ABr caseResultBlock [OpVar result])

        case mDefault of
            Just defBody -> do
                beginBlock defaultBlock []
                result <- lowerTermToLGraph env defBody
                terminate (ABr caseResultBlock [OpVar result])
            Nothing -> pure ()

        beginBlock caseResultBlock [("case_result_val", termType)]
        pure "case_result_val"
      where
        -- Bind pattern variables to fields extracted from payload
        -- payload is either:
        --   - Single binding: the field value directly
        --   - Multiple bindings: CON(field0, CON(field1, ...))
        bindPatternVars :: LGraphEnv -> String -> [(C.Name, Type)] -> AlloyBuilder LGraphEnv
        bindPatternVars e _ [] = pure e
        bindPatternVars e payload [(name, _ty)] = do
            -- Single binding: payload IS the field
            pure $ extendTermBinding name payload e
        bindPatternVars e payload bindings = do
            -- Multiple bindings: extract from nested CONs
            -- CON(field0, CON(field1, CON(field2, ...)))
            go e payload bindings
          where
            go env' _ [] = pure env'
            go env' node [(name, _ty)] = do
                -- Last binding: get fst of current CON
                field <- emitLetTmp termType (OpGraphConGet (OpVar node) 0)
                pure $ extendTermBinding name field env'
            go env' node ((name, _ty) : rest) = do
                -- Get fst (current field) and snd (rest of CONs)
                field <- emitLetTmp termType (OpGraphConGet (OpVar node) 0)
                restNode <- emitLetTmp termType (OpGraphConGet (OpVar node) 1)
                let env'' = extendTermBinding name field env'
                go env'' restNode rest

    -- Tagged values (ADT constructors)
    -- Representation: CON(NUM(tag), payload)
    -- - For nullary constructors: just NUM(tag)
    -- - For single-field: CON(NUM(tag), field)
    -- - For multi-field: CON(NUM(tag), CON(field0, CON(field1, ...)))
    C.CTag tag fields _ty -> do
        tagNode <- emitLetTmp termType (OpGraphNum (OpConst (CInt tag)))
        case fields of
            [] ->
                -- Nullary constructor: just the tag as a NUM
                pure tagNode
            [singleField] -> do
                -- Single-field constructor: CON(tag, field)
                fieldNode <- lowerTermToLGraph env singleField
                emitLetTmp termType (OpGraphCon (OpVar tagNode) (OpVar fieldNode))
            _ -> do
                -- Multi-field constructor: CON(tag, CON(field0, CON(field1, ...ERA)))
                -- Build a right-nested list of CON nodes for the fields
                fieldNodes <- mapM (lowerTermToLGraph env) fields
                -- Start with ERA as the terminator
                eraNode <- emitLetTmp termType OpGraphEra
                -- Fold from right: build CON(field_n-1, CON(field_n, ERA))
                -- Use foldM with reversed list to achieve right-fold semantics
                payload <-
                    foldM
                        (\accNode fieldNode -> emitLetTmp termType (OpGraphCon (OpVar fieldNode) (OpVar accNode)))
                        eraNode
                        (reverse fieldNodes)
                -- Wrap with the tag: CON(tag, payload)
                emitLetTmp termType (OpGraphCon (OpVar tagNode) (OpVar payload))

    -- Comparison operations
    C.CCmpOp op a b -> do
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
                pure (aNative, bNative)
            (Just aNative, Nothing) -> do
                bNode <- lowerTermToLGraph env b
                bExtracted <- emitLetTmp intType (OpGraphExtractNum (OpVar bNode))
                pure (aNative, bExtracted)
            (Nothing, Just bNative) -> do
                aNode <- lowerTermToLGraph env a
                aExtracted <- emitLetTmp intType (OpGraphExtractNum (OpVar aNode))
                pure (aExtracted, bNative)
            (Nothing, Nothing) -> do
                aNode <- lowerTermToLGraph env a
                bNode <- lowerTermToLGraph env b
                aExtracted <- emitLetTmp intType (OpGraphExtractNum (OpVar aNode))
                bExtracted <- emitLetTmp intType (OpGraphExtractNum (OpVar bNode))
                pure (aExtracted, bExtracted)
        boolResult <- emitLetTmp boolType (OpCmp cmpOp (OpVar aVal) (OpVar bVal))
        emitLetTmp intType (OpSelect (OpVar boolResult) (OpConst (CInt 1)) (OpConst (CInt 0)))

    -- Unary operations
    C.CUnaryOp op a -> do
        aNode <- lowerTermToLGraph env a
        case op of
            C.OpNeg -> do
                zeroNode <- emitLetTmp termType (OpGraphNum (OpConst (CInt 0)))
                emitLetTmp termType (OpGraphSub (OpVar zeroNode) (OpVar aNode))
            C.OpNot -> do
                aVal <- emitLetTmp intType (OpGraphReduce (OpVar aNode))
                notVal <- emitLetTmp boolType (OpCmp CEq (OpVar aVal) (OpConst (CInt 0)))
                intVal <- emitLetTmp intType (OpSelect (OpVar notVal) (OpConst (CInt 1)) (OpConst (CInt 0)))
                emitLetTmp termType (OpGraphNum (OpVar intVal))

    -- Closures with captured environment
    C.CClosure liftedName capturedVars _ty -> do
        case lookupFuncIndex liftedName env of
            Nothing -> error $ "Circuit.ToGraph: unknown lifted function: " ++ liftedName
            Just funcIdx -> do
                if null capturedVars
                    then do
                        emitLetTmp termType (OpGraphClosure funcIdx 1 [])
                    else do
                        envNodes <- forM capturedVars $ \(varName, _varTy) -> do
                            case lookupBinding varName env of
                                Nothing -> error $ "Circuit.ToGraph: unbound captured var: " ++ varName
                                Just boundName -> do
                                    if isTermBinding varName env
                                        then pure (OpVar boundName)
                                        else do
                                            node <- emitLetTmp termType (OpGraphNum (OpVar boundName))
                                            pure (OpVar node)
                        emitLetTmp termType (OpGraphClosure funcIdx 1 envNodes)

    -- Extract captured variable from closure's environment
    C.CClosureGetEnv closureExpr idx _ty -> do
        closureVar <- case closureExpr of
            C.CVar name _ ->
                case lookupBinding name env of
                    Just varName -> pure varName
                    Nothing -> error $ "Circuit.ToGraph: unbound closure: " ++ name
            _ -> error "Circuit.ToGraph: CClosureGetEnv expects a variable"
        emitLetTmp termType (OpGraphClosureGetEnv (OpVar closureVar) idx)
    -- Field projection from tagged values
    -- Our tagged value representation is: CON(NUM(tag), payload)
    -- - Single-field: CON(tag, field) -> payload is the field directly
    -- - Multi-field: CON(tag, CON(field0, CON(field1, ...))) -> need to traverse
    --
    -- OpGraphConGet(term, 0) = fst (the tag)
    -- OpGraphConGet(term, 1) = snd (the payload)
    C.CProject expr idx _ty -> do
        -- Lower the expression to a graph term (should be a CON node)
        exprNode <- lowerTermToLGraph env expr
        -- Get the payload (second element of the CON: CON(tag, payload))
        payload <- emitLetTmp termType (OpGraphConGet (OpVar exprNode) 1)
        -- For field index 0, the payload IS the field (single-field case)
        -- or the first element of the nested CON (multi-field case)
        if idx == 0
            then do
                -- For single-field constructors, payload is directly the field
                -- For multi-field, payload is CON(field0, rest), so get field0
                -- We handle both cases: if it's a CON, get first; if not, it's the value
                -- In practice, the Circuit IR knows the structure, so we just return payload
                -- for idx=0 in single-field case, or traverse for multi-field
                pure payload
            else do
                -- Multi-field: need to traverse the nested CONs
                -- payload = CON(field0, CON(field1, CON(field2, ...)))
                -- To get field N, we do: get(get(get(payload, 1), 1), ..., 0)
                -- i.e., follow 'snd' links N times, then get 'fst'
                traverseCons payload idx
      where
        -- Traverse N levels of nested CON nodes and get the field
        -- CON(field0, CON(field1, CON(field2, ...)))
        -- To get field at index n: follow 'snd' n times, then get 'fst'
        traverseCons :: String -> Int -> AlloyBuilder String
        traverseCons node 0 = do
            -- Get the first element (the field at this level)
            emitLetTmp termType (OpGraphConGet (OpVar node) 0)
        traverseCons node n = do
            -- Get the second element (the rest of the list)
            rest <- emitLetTmp termType (OpGraphConGet (OpVar node) 1)
            traverseCons rest (n - 1)

    -- String literals
    -- In graph mode, strings are represented as pointers to C string constants
    -- We encode the string pointer as a NUM node (pointer cast to integer)
    -- The LLVM codegen will handle ptrtoint conversion in OpGraphNum
    C.CStr s -> do
        -- Create a NUM node containing the string pointer
        -- OpConst (CString s) produces a pointer to the C string constant
        -- OpGraphNum will convert the pointer to i64 via ptrtoint in LLVM codegen
        emitLetTmp termType (OpGraphNum (OpConst (CString s)))
    C.CPanic msg _ ->
        error $ "Circuit.ToGraph: panic: " ++ msg
    C.CFork{} ->
        error "Circuit.ToGraph: forking not supported in lgraph mode"
    C.CJoin{} ->
        error "Circuit.ToGraph: joining not supported in lgraph mode"

{- | Try to get a native int value for a term without building graph nodes.
Returns Just varName if the term is a simple var/literal or DUP projection, Nothing otherwise.
-}
tryGetNative :: LGraphEnv -> C.CTerm -> AlloyBuilder (Maybe String)
tryGetNative env term = case term of
    C.CVar name _ ->
        if isTermBinding name env
            then pure Nothing
            else case lookupBinding name env of
                Just varName -> pure (Just varName)
                Nothing -> pure Nothing
    C.CInt n -> do
        tmp <- emitLetTmp intType (OpBin IAdd (OpConst (CInt n)) (OpConst (CInt 0)))
        pure (Just tmp)
    -- Handle DUP projections - check if they're native bindings
    C.CDp0 name _ ->
        if isTermBinding (name ++ ".0") env
            then pure Nothing
            else case lookupBinding (name ++ ".0") env of
                Just varName -> pure (Just varName)
                Nothing -> pure Nothing
    C.CDp1 name _ ->
        if isTermBinding (name ++ ".1") env
            then pure Nothing
            else case lookupBinding (name ++ ".1") env of
                Just varName -> pure (Just varName)
                Nothing -> pure Nothing
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
