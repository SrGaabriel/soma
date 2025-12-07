{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

{- |

This module implements automatic fork-join parallelization for the Circuit IR.
It analyzes the linearized IR (which is already a dependency graph due to
single-use property) and inserts CFork/CJoin nodes for independent computations.

The key insight: after linearization, every value is used exactly once,
so the data flow forms a DAG. Independent nodes in this DAG can run in parallel.

Algorithm:
1. For let bindings: Extract consecutive bindings, build dependency graph,
   topologically sort into parallel "levels", insert CFork/CJoin
2. For any expression: Identify independent subexpressions (e.g., both sides
   of a binary operator with function calls), extract them into temporary
   bindings, wrap with CFork/CJoin
-}
module Circuit.Parallel (
    parallelizeModule,
    parallelizeFunction,
    parallelize,

    -- * Configuration
    ParallelConfig (..),
    defaultParallelConfig,

    -- * Analysis (exported for testing)
    DepGraph,
    buildDepGraph,
    topoLevels,
    estimateWork,
) where

import Circuit.Ir
import Control.Monad (foldM, forM)
import Control.Monad.State
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Project.Name (Name (..), LocalId (..), LocalPrefix (..))
import Typing.Types (Type (..))

-- | Configuration for parallelization
data ParallelConfig = ParallelConfig
    { pcWorkThreshold :: !Int
    -- ^ Minimum estimated work to consider forking (default: 50)
    , pcMinParallelBindings :: !Int
    -- ^ Minimum number of independent bindings to parallelize (default: 2)
    , pcEnabled :: !Bool
    -- ^ Whether parallelization is enabled
    }
    deriving (Show, Eq)

defaultParallelConfig :: ParallelConfig
defaultParallelConfig =
    ParallelConfig
        { pcWorkThreshold = 100
        , pcMinParallelBindings = 2
        , pcEnabled = True
        }

-- | Dependency graph: maps binding name to its dependencies (other bindings it references)
type DepGraph = Map Name (Set Name)

-- | A binding with its metadata
data BindingInfo = BindingInfo
    { biName :: !Name
    , biType :: !Type
    , biExpr :: !CTerm
    , biDeps :: !(Set Name) -- Dependencies on other bindings
    , biWork :: !Int -- Estimated work
    }
    deriving (Show)

-- | Parallelize all functions in a module
parallelizeModule :: ParallelConfig -> CModule -> CModule
parallelizeModule config cmod =
    cmod
        { cmFunctions = map (parallelizeFunction config) (cmFunctions cmod)
        }

-- | Parallelize a single function
parallelizeFunction :: ParallelConfig -> CFunction -> CFunction
parallelizeFunction config cfun =
    cfun
        { cfBody = parallelize config (map fst $ cfParams cfun) (cfBody cfun)
        }

{- | Main parallelization function
Takes the set of parameter names (which are not bindings) and the term
-}
parallelize :: ParallelConfig -> [Name] -> CTerm -> CTerm
parallelize config params term
    | not (pcEnabled config) = term
    | otherwise = evalState (parallelizeTerm config (Set.fromList params) term) 0

-- | State monad for generating fresh names
type ParM = State Int

freshTaskName :: Name -> ParM Name
freshTaskName _base = do
    n <- get
    put (n + 1)
    return $ NLocal (LocalId LPTemp n)

freshTempName :: String -> ParM Name
freshTempName _prefix = do
    n <- get
    put (n + 1)
    return $ NLocal (LocalId LPTemp n)

-- | A reference to a variable, distinguishing dup projections
data VarRef
    = VarPlain !Name -- Regular variable reference
    | VarDp0 !Name -- First projection of a dup (x₀)
    | VarDp1 !Name -- Second projection of a dup (x₁)
    deriving (Show, Eq, Ord)

{- | Get all variable references in a term, distinguishing dup projections
This is more precise than freeVars because CDp0 "x" and CDp1 "x" are
considered different references (they're independent after duplication)

Note: Function-typed variables (TArrow) are excluded because calling the same
pure function from two places doesn't create a data dependency - the calls
are independent operations.
-}
varRefs :: CTerm -> Set VarRef
varRefs = go Set.empty
  where
    go bound term = case term of
        CVar n ty ->
            -- Exclude function-typed variables - they're pure functions that can be
            -- safely called from parallel branches without creating dependencies
            case ty of
                TArrow _ _ -> Set.empty
                _ -> if Set.member n bound then Set.empty else Set.singleton (VarPlain n)
        CLam n _ body -> go (Set.insert n bound) body
        CApp f x _ -> go bound f <> go bound x
        CLet n _ val body -> go bound val <> go (Set.insert n bound) body
        CSup _ a b _ -> go bound a <> go bound b
        CDup n _ _ val body -> go bound val <> go (Set.insert n bound) body
        CDp0 n _ -> if Set.member n bound then Set.empty else Set.singleton (VarDp0 n)
        CDp1 n _ -> if Set.member n bound then Set.empty else Set.singleton (VarDp1 n)
        CEra -> Set.empty
        CErase val body -> go bound val <> go bound body
        CRef _ _ -> Set.empty
        CInt _ -> Set.empty
        CBool _ -> Set.empty
        CStr _ -> Set.empty
        CTag _ fields _ -> mconcat (map (go bound) fields)
        CCase scrut arms def _ ->
            go bound scrut
                <> mconcat [go (foldr (Set.insert . fst) bound ns) body | (_, ns, body) <- arms]
                <> maybe Set.empty (go bound) def
        CBinOp _ a b -> go bound a <> go bound b
        CCmpOp _ a b -> go bound a <> go bound b
        CUnaryOp _ a -> go bound a
        CClosure _ captured _ ->
            Set.fromList [VarPlain n | (n, _) <- captured, not (Set.member n bound)]
        CClosureGetEnv closure _ _ -> go bound closure
        CProject expr _ _ -> go bound expr
        CPanic _ _ -> Set.empty
        CFork n _ comp body -> go bound comp <> go (Set.insert n bound) body
        CJoin n _ -> if Set.member n bound then Set.empty else Set.singleton (VarPlain n)

{- | Check if two terms have independent variable references
Two terms are independent if they don't share any variable references.
Crucially, CDp0 "x" and CDp1 "x" are considered DIFFERENT references,
so terms using opposite projections of the same dup are independent.
-}
areIndependent :: CTerm -> CTerm -> Bool
areIndependent t1 t2 =
    let refs1 = varRefs t1
        refs2 = varRefs t2
    in Set.null (refs1 `Set.intersection` refs2)

{- | Try to extract parallelizable subexpressions from a term.
Returns Nothing if the term doesn't have parallelizable independent children,
or Just a transformed term with the subexpressions extracted into fork/join bindings.
-}
tryExtractParallel :: ParallelConfig -> Set Name -> CTerm -> ParM (Maybe CTerm)
tryExtractParallel config params term = case term of
    -- Binary operators: if both sides are expensive and independent, parallelize
    CBinOp op a b -> tryExtractBinaryOp config params (CBinOp op) a b (getTermType term)
    CCmpOp op a b -> tryExtractBinaryOp config params (CCmpOp op) a b (getTermType term)
    -- Application: check if we have (f a) where both f and a are expensive
    -- This handles cases like (expensive1 x) (expensive2 y) -> though rare
    CApp f x ty -> tryExtractBinaryOp config params (\f' x' -> CApp f' x' ty) f x ty
    -- Superposition: both branches can be parallelized if independent
    CSup l a b ty -> tryExtractBinaryOp config params (\a' b' -> CSup l a' b' ty) a b ty
    -- Tag constructor: multiple fields can be parallelized if independent
    CTag t fields ty -> tryExtractMultiple config params fields $ \fields' -> CTag t fields' ty
    _ -> return Nothing

-- | Try to extract two independent expensive subexpressions into parallel bindings
tryExtractBinaryOp ::
    ParallelConfig ->
    Set Name ->
    (CTerm -> CTerm -> CTerm) -> -- Reconstruct the expression
    CTerm -> -- Left subexpr
    CTerm -> -- Right subexpr
    Type -> -- Result type (for reference)
    ParM (Maybe CTerm)
tryExtractBinaryOp config params reconstruct left right _resultTy = do
    let leftWork = estimateWork left
        rightWork = estimateWork right
        leftExpensive = leftWork >= pcWorkThreshold config
        rightExpensive = rightWork >= pcWorkThreshold config
        independent = areIndependent left right
    -- Only parallelize if BOTH are expensive and they're independent
    if leftExpensive && rightExpensive && independent
        then do
            -- Generate fresh names for the extracted bindings
            leftName <- freshTempName "par_left"
            rightName <- freshTempName "par_right"
            leftTask <- freshTaskName leftName
            rightTask <- freshTaskName rightName

            let leftTy = getTermType left
                rightTy = getTermType right

            -- Recursively parallelize the subexpressions
            left' <- parallelizeTerm config params left
            right' <- parallelizeTerm config params right

            -- Build: CFork leftTask (left')
            --          (CFork rightTask (right')
            --            (CLet leftName (CJoin leftTask)
            --              (CLet rightName (CJoin rightTask)
            --                (reconstruct (CVar leftName) (CVar rightName)))))
            let innerExpr = reconstruct (CVar leftName leftTy) (CVar rightName rightTy)
                withJoins =
                    CLet rightName rightTy (CJoin rightTask rightTy)
                        $ CLet leftName leftTy (CJoin leftTask leftTy) innerExpr
                withForks =
                    CFork leftTask leftTy left'
                        $ CFork rightTask rightTy right' withJoins

            return $ Just withForks
        else
            return Nothing

-- | Try to extract multiple independent expensive subexpressions (e.g., tag fields)
tryExtractMultiple ::
    ParallelConfig ->
    Set Name ->
    [CTerm] -> -- Subexpressions
    ([CTerm] -> CTerm) -> -- Reconstruct with new subexprs
    ParM (Maybe CTerm)
tryExtractMultiple config params subexprs reconstruct = do
    -- Find which subexpressions are expensive
    let withWork = [(expr, estimateWork expr) | expr <- subexprs]
        expensive = [(expr, work) | (expr, work) <- withWork, work >= pcWorkThreshold config]

    -- Need at least 2 expensive subexpressions to parallelize
    if length expensive < 2
        then return Nothing
        else do
            -- Check pairwise independence of expensive subexpressions
            let expensiveExprs = map fst expensive
                allPairsIndependent =
                    all
                        (uncurry areIndependent)
                        [(e1, e2) | (e1 : rest) <- [expensiveExprs], e2 <- rest]

            if not allPairsIndependent
                then return Nothing
                else do
                    -- Extract all expensive subexpressions into fork/join bindings
                    -- Non-expensive ones are kept inline

                    -- Generate names and tasks for expensive subexprs
                    namesAndTasks <- forM (zip [(0 :: Int) ..] subexprs) $ \(i, expr) ->
                        if estimateWork expr >= pcWorkThreshold config
                            then do
                                name <- freshTempName ("par_field_" ++ show i)
                                task <- freshTaskName name
                                return (expr, Just (name, task, getTermType expr))
                            else return (expr, Nothing)

                    -- Parallelize subexpressions
                    parallelizedExprs <- forM namesAndTasks $ \(expr, _) ->
                        parallelizeTerm config params expr

                    let namesAndTasksWithPar = zip parallelizedExprs (map snd namesAndTasks)

                    -- Build the reconstructed expression using vars for extracted, inline for others
                    let newSubexprs =
                            [ case mInfo of
                                Just (name, _, ty) -> CVar name ty
                                Nothing -> expr
                            | (expr, mInfo) <- namesAndTasksWithPar
                            ]
                        innerExpr = reconstruct newSubexprs

                    -- Build joins (innermost to outermost)
                    let extractedInfos =
                            [ (name, task, ty, parExpr)
                            | (parExpr, Just (name, task, ty)) <- namesAndTasksWithPar
                            ]

                    let withJoins =
                            foldr
                                ( \(name, task, ty, _) acc ->
                                    CLet name ty (CJoin task ty) acc
                                )
                                innerExpr
                                extractedInfos

                    -- Build forks (outermost to innermost)
                    let withForks =
                            foldr
                                ( \(_, task, ty, parExpr) acc ->
                                    CFork task ty parExpr acc
                                )
                                withJoins
                                extractedInfos

                    return $ Just withForks

-- | Parallelize a term, given the set of names that are parameters (not bindings)
parallelizeTerm :: ParallelConfig -> Set Name -> CTerm -> ParM CTerm
parallelizeTerm config params = go
  where
    go term = case term of
        -- The interesting case: let bindings
        CLet name ty expr body -> do
            -- Collect all consecutive let bindings
            let (bindings, finalExpr) = collectBindings term

            -- Only parallelize if we have multiple bindings
            if length bindings < 2
                then do
                    -- Single binding: try to extract parallel subexprs from the expr
                    mExtracted <- tryExtractParallel config params expr
                    case mExtracted of
                        Just extracted -> do
                            -- The extracted term already has the parallelized structure
                            -- We need to wrap the body around it
                            body' <- go body
                            return $ wrapWithBody name ty extracted body'
                        Nothing -> do
                            -- Just recurse into single binding normally
                            expr' <- go expr
                            body' <- go body
                            return $ CLet name ty expr' body'
                else do
                    -- Build dependency graph and parallelize
                    parallelizeBindings config params bindings finalExpr

        -- For other expressions, first try to extract parallel subexprs,
        -- then recurse into children

        CBinOp op a b -> do
            mExtracted <- tryExtractParallel config params term
            case mExtracted of
                Just extracted -> return extracted
                Nothing -> CBinOp op <$> go a <*> go b
        CCmpOp op a b -> do
            mExtracted <- tryExtractParallel config params term
            case mExtracted of
                Just extracted -> return extracted
                Nothing -> CCmpOp op <$> go a <*> go b
        CApp f x ty -> do
            mExtracted <- tryExtractParallel config params term
            case mExtracted of
                Just extracted -> return extracted
                Nothing -> CApp <$> go f <*> go x <*> pure ty
        CSup l a b ty -> do
            mExtracted <- tryExtractParallel config params term
            case mExtracted of
                Just extracted -> return extracted
                Nothing -> CSup l <$> go a <*> go b <*> pure ty
        CTag t fields ty -> do
            mExtracted <- tryExtractParallel config params term
            case mExtracted of
                Just extracted -> return extracted
                Nothing -> CTag t <$> mapM go fields <*> pure ty

        -- Recurse into other subterms
        CLam n ty body -> CLam n ty <$> parallelizeTerm config (Set.insert n params) body
        CDup n ty l val body -> CDup n ty l <$> go val <*> parallelizeTerm config (Set.insert n params) body
        CCase scrut arms mdef ty -> do
            scrut' <- go scrut
            arms' <- forM arms $ \(t, ns, body) -> do
                let params' = foldr (Set.insert . fst) params ns
                body' <- parallelizeTerm config params' body
                return (t, ns, body')
            mdef' <- mapM go mdef
            return $ CCase scrut' arms' mdef' ty
        CUnaryOp op a -> CUnaryOp op <$> go a
        CClosure n caps ty -> return $ CClosure n caps ty
        CClosureGetEnv c i ty -> CClosureGetEnv <$> go c <*> pure i <*> pure ty
        CProject e i ty -> CProject <$> go e <*> pure i <*> pure ty
        CFork n ty comp body -> CFork n ty <$> go comp <*> go body
        -- Erase: recurse into both parts
        CErase val body -> CErase <$> go val <*> go body
        -- Leaves - no recursion needed
        CVar{} -> return term
        CDp0{} -> return term
        CDp1{} -> return term
        CEra -> return term
        CRef{} -> return term
        CInt{} -> return term
        CBool{} -> return term
        CStr{} -> return term
        CPanic{} -> return term
        CJoin{} -> return term

{- | Wrap an extracted parallel computation with a body that uses the result
The extracted term computes some value; we need to bind it to `name` and continue with `body`
-}
wrapWithBody :: Name -> Type -> CTerm -> CTerm -> CTerm
wrapWithBody name ty extracted body = case extracted of
    -- If the extracted term is a fork structure, we need to insert the body at the end
    CFork taskName taskTy comp cont ->
        CFork taskName taskTy comp (wrapWithBody name ty cont body)
    CLet letName letTy letExpr letBody ->
        CLet letName letTy letExpr (wrapWithBody name ty letBody body)
    -- Base case: the final expression that computes the value
    other ->
        CLet name ty other body

-- | Collect consecutive let bindings
collectBindings :: CTerm -> ([(Name, Type, CTerm)], CTerm)
collectBindings (CLet name ty expr body) =
    let (rest, final) = collectBindings body
    in ((name, ty, expr) : rest, final)
collectBindings term = ([], term)

-- | Parallelize a sequence of bindings
parallelizeBindings :: ParallelConfig -> Set Name -> [(Name, Type, CTerm)] -> CTerm -> ParM CTerm
parallelizeBindings config params bindings finalExpr = do
    -- First, try to extract parallel subexpressions from each binding's expression
    parallelizedBindings <- forM bindings $ \(name, ty, expr) -> do
        mExtracted <- tryExtractParallel config params expr
        case mExtracted of
            Just extracted -> return (name, ty, extracted, True)
            Nothing -> do
                expr' <- parallelizeTerm config params expr
                return (name, ty, expr', False)

    -- Rebuild bindings, handling extracted ones specially
    let rebuildWithExtracted [] inner = return inner
        rebuildWithExtracted ((name, ty, expr, wasExtracted) : rest) inner = do
            inner' <- rebuildWithExtracted rest inner
            if wasExtracted
                then return $ wrapWithBody name ty expr inner'
                else return $ CLet name ty expr inner'

    -- Build binding info with dependencies (using original expressions for dependency analysis)
    let bindingNames = Set.fromList [n | (n, _, _, _) <- parallelizedBindings]
        bindingInfos =
            [ mkBindingInfo params bindingNames n ty e
            | (n, ty, e, _) <- parallelizedBindings
            ]

    -- Build dependency graph
    let depGraph = Map.fromList [(biName bi, biDeps bi) | bi <- bindingInfos]

    -- Topologically sort into levels
    let levels = topoLevels depGraph

    -- Check if parallelization is worthwhile
    let worthwhile =
            any
                ( \level ->
                    length level >= pcMinParallelBindings config
                        && any (\n -> maybe 0 biWork (findBinding n bindingInfos) >= pcWorkThreshold config) level
                )
                levels

    if not worthwhile
        then do
            -- Not worth parallelizing, just rebuild sequential lets
            finalExpr' <- parallelizeTerm config (params `Set.union` bindingNames) finalExpr
            rebuildWithExtracted (reverse parallelizedBindings) finalExpr'
        else do
            -- Generate parallel code
            generateParallelCode config params bindingInfos levels finalExpr
  where
    findBinding :: Name -> [BindingInfo] -> Maybe BindingInfo
    findBinding n = foldr (\bi acc -> if biName bi == n then Just bi else acc) Nothing

-- | Create binding info with dependency analysis
mkBindingInfo :: Set Name -> Set Name -> Name -> Type -> CTerm -> BindingInfo
mkBindingInfo _params bindingNames name ty expr =
    let fvs = freeVars expr
        -- Dependencies are free variables that are bindings (not parameters)
        deps = fvs `Set.intersection` bindingNames
        work = estimateWork expr
    in BindingInfo
        { biName = name
        , biType = ty
        , biExpr = expr
        , biDeps = deps
        , biWork = work
        }

-- | Build dependency graph from bindings
buildDepGraph :: [BindingInfo] -> DepGraph
buildDepGraph infos = Map.fromList [(biName bi, biDeps bi) | bi <- infos]

{- | Topologically sort bindings into parallel levels
Each level contains bindings that only depend on previous levels
-}
topoLevels :: DepGraph -> [[Name]]
topoLevels graph = go graph []
  where
    go g acc
        | Map.null g = reverse acc
        | otherwise =
            -- Find all nodes with no remaining dependencies
            let ready = [n | (n, deps) <- Map.toList g, Set.null deps]
            in if null ready
                then reverse acc -- Cycle detected or done
                else
                    let readySet = Set.fromList ready
                        -- Remove ready nodes from graph and from other nodes' deps
                        g' =
                            Map.map (`Set.difference` readySet)
                                $ foldr Map.delete g ready
                    in go g' (ready : acc)

-- | Estimate computational work of an expression
estimateWork :: CTerm -> Int
estimateWork = go
  where
    go = \case
        -- Function calls are expensive, especially recursive ones
        CApp (CRef _ _) _ _ -> 100 -- Direct function reference call
        CApp (CVar _ _) _ _ -> 100 -- Variable holding a function (likely top-level)
        CApp f x _ -> go f + go x + 10
        -- Closures with environment are moderately expensive
        CClosure _ caps _ -> 20 + length caps * 5
        -- Primitives are cheap
        CBinOp _ a b -> go a + go b + 1
        CCmpOp _ a b -> go a + go b + 1
        CUnaryOp _ a -> go a + 1
        -- Control flow
        CCase scrut arms mdef _ ->
            go scrut + maximum (0 : [go body | (_, _, body) <- arms]) + maybe 0 go mdef
        -- Let adds the cost of both parts
        CLet _ _ val body -> go val + go body
        -- Duplication - the value might be computed twice
        CDup _ _ _ val body -> go val * 2 + go body
        -- Projections are cheap
        CDp0{} -> 1
        CDp1{} -> 1
        -- Literals are free
        CInt{} -> 0
        CBool{} -> 0
        CStr{} -> 0
        CVar{} -> 0
        CRef{} -> 0
        CEra -> 0
        CErase val body -> go val + go body
        -- Other constructs
        CLam _ _ body -> go body
        CSup _ a b _ -> go a + go b
        CTag _ fields _ -> sum (map go fields)
        CClosureGetEnv{} -> 1
        CProject{} -> 1
        CPanic{} -> 0
        CFork _ _ comp body -> go comp + go body
        CJoin{} -> 1

-- | Generate parallel code with CFork/CJoin
generateParallelCode :: ParallelConfig -> Set Name -> [BindingInfo] -> [[Name]] -> CTerm -> ParM CTerm
generateParallelCode config params bindingInfos levels finalExpr = do
    -- Process each level
    let infoMap = Map.fromList [(biName bi, bi) | bi <- bindingInfos]

    -- Start from innermost (final expression) and work outward
    finalExpr' <-
        parallelizeTerm
            config
            (params `Set.union` Set.fromList (map biName bindingInfos))
            finalExpr

    -- Build the code from inside out
    foldM (processLevel config infoMap) finalExpr' (reverse levels)

-- | Process one level of parallel bindings
processLevel :: ParallelConfig -> Map Name BindingInfo -> CTerm -> [Name] -> ParM CTerm
processLevel config infoMap innerCode names = do
    let infos = [infoMap Map.! n | n <- names]

    -- If only one binding or work is too low, keep sequential
    if length infos < pcMinParallelBindings config
        || not (any (\bi -> biWork bi >= pcWorkThreshold config) infos)
        then do
            -- Sequential: just wrap with CLet
            return $ foldr (\bi acc -> CLet (biName bi) (biType bi) (biExpr bi) acc) innerCode infos
        else do
            -- Parallel: wrap with CFork then CJoin
            -- First, generate all the forks
            taskNames <- mapM (freshTaskName . biName) infos
            let forkPairs = zip taskNames infos

            -- Build: CFork task1 (expr1) (CFork task2 (expr2) (... (joins and inner)))
            let joinsAndInner =
                    foldr
                        ( \(taskName, bi) acc ->
                            CLet (biName bi) (biType bi) (CJoin taskName (biType bi)) acc
                        )
                        innerCode
                        forkPairs

            -- Wrap with forks (outermost first)
            return
                $ foldr
                    ( \(taskName, bi) acc ->
                        CFork taskName (biType bi) (biExpr bi) acc
                    )
                    joinsAndInner
                    forkPairs
