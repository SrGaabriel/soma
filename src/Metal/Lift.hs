{-# LANGUAGE NamedFieldPuns #-}

module Metal.Lift (
    liftLambdas,
) where

import Control.Monad.State.Strict
import qualified Data.Set as Set

import Metal.Expr
import Metal.Function
import Metal.Metadata
import Metal.Module
import Syntax.Patterns (Pattern (..))
import Typing.Types

type LiftM = State LiftState

data LiftState = LiftState
    { lsNextLambdaId :: Int
    , lsLiftedFunctions :: [MetallicFunction]
    }

emptyLiftState :: LiftState
emptyLiftState =
    LiftState
        { lsNextLambdaId = 0
        , lsLiftedFunctions = []
        }

liftLambdas :: MetallicModule -> MetallicModule
liftLambdas m@MetallicModule{mmFunctions} =
    let (fns', st) = runState (mapM liftFunctionLambdas mmFunctions) emptyLiftState
        allFns = fns' ++ lsLiftedFunctions st
    in m{mmFunctions = allFns}

liftFunctionLambdas :: MetallicFunction -> LiftM MetallicFunction
liftFunctionLambdas fn@MetallicFunction{mfBody} = do
    body' <- liftExprLambdas Set.empty mfBody
    pure fn{mfBody = body'}

liftExprLambdas :: Set.Set String -> MetallicExpr -> LiftM MetallicExpr
liftExprLambdas _ (MVar v ty) = pure (MVar v ty)
liftExprLambdas _ (MLit lit) = pure (MLit lit)
liftExprLambdas bound (MCall callee args ty) = do
    callee' <- liftExprLambdas bound callee
    args' <- mapM (liftExprLambdas bound) args
    pure (MCall callee' args' ty)
liftExprLambdas bound (MTypeApp e tys ty) = do
    e' <- liftExprLambdas bound e
    pure (MTypeApp e' tys ty)
liftExprLambdas bound (MLet name val body ty) = do
    val' <- liftExprLambdas bound val
    body' <- liftExprLambdas (Set.insert name bound) body
    pure (MLet name val' body' ty)
liftExprLambdas bound (MLambda params body ty) = do
    let paramSet = Set.fromList params
        freeVars = computeFreeVars body Set.\\ paramSet Set.\\ bound
        freeVarsList = Set.toList freeVars

    let boundInBody = Set.union paramSet bound
    body' <- liftExprLambdas boundInBody body

    lambdaId <- freshLambdaId
    let liftedName = "lambda$" ++ show lambdaId

    let (paramTypes, retType) = uncurryFunctionType ty
        liftedParams = zip params paramTypes
        liftedFn =
            MetallicFunction
                { mfName = liftedName
                , mfParams = liftedParams
                , mfReturnType = retType
                , mfBody = body'
                , mfMetadata =
                    MetallicFunctionMetadata
                        { fmOriginalName = []
                        , mfmConstraints = []
                        , fmInstanceInfo = Nothing
                        }
                }

    addLiftedFunction liftedFn

    if null freeVarsList
        then pure (MVar liftedName ty)
        else
            error
                $ "Lambda lifting with free variables not yet fully supported. "
                    ++ "Lambda captures: "
                    ++ show freeVarsList
                    ++ ". Ensure lambdas are closed or implement closure construction."
liftExprLambdas bound (MConstruct name tag args ty) = do
    args' <- mapM (liftExprLambdas bound) args
    pure (MConstruct name tag args' ty)
liftExprLambdas bound (MArrayLit elems ty) = do
    elems' <- mapM (liftExprLambdas bound) elems
    pure (MArrayLit elems' ty)
liftExprLambdas bound (MTuple elems ty) = do
    elems' <- mapM (liftExprLambdas bound) elems
    pure (MTuple elems' ty)
liftExprLambdas bound (MCase scrutinees arms mdef ty) = do
    scrutinees' <- mapM (liftExprLambdas bound) scrutinees
    arms' <- mapM (liftArm bound) arms
    mdef' <- mapM (liftExprLambdas bound) mdef
    pure (MCase scrutinees' arms' mdef' ty)
  where
    liftArm :: Set.Set String -> MCaseArm -> LiftM MCaseArm
    liftArm boundVars MCaseArm{mcaPatterns, mcaBody} =
        let binders = concatMap collectBinders mcaPatterns
            boundInArm = Set.union boundVars (Set.fromList binders)
        in do
            body' <- liftExprLambdas boundInArm mcaBody
            pure MCaseArm{mcaPatterns = mcaPatterns, mcaBody = body'}
liftExprLambdas bound (MFieldAccess e idx ty) = do
    e' <- liftExprLambdas bound e

    pure (MFieldAccess e' idx ty)
liftExprLambdas bound (MCompose stmts ty) = do
    (stmts', _) <- liftComposeLambdas bound stmts
    pure (MCompose stmts' ty)
liftExprLambdas _ (MPanic msg ty) = pure (MPanic msg ty)

liftComposeLambdas :: Set.Set String -> [MetallicComposeStmt] -> LiftM ([MetallicComposeStmt], Set.Set String)
liftComposeLambdas bound [] = pure ([], bound)
liftComposeLambdas bound (stmt : rest) =
    case stmt of
        MCBind name e -> do
            e' <- liftExprLambdas bound e
            let bound' = Set.insert name bound
            (rest', bound'') <- liftComposeLambdas bound' rest
            pure (MCBind name e' : rest', bound'')
        MCLet name e -> do
            e' <- liftExprLambdas bound e
            let bound' = Set.insert name bound
            (rest', bound'') <- liftComposeLambdas bound' rest
            pure (MCLet name e' : rest', bound'')
        MCExpr e -> do
            e' <- liftExprLambdas bound e
            (rest', bound'') <- liftComposeLambdas bound rest
            pure (MCExpr e' : rest', bound'')

freshLambdaId :: LiftM Int
freshLambdaId = do
    st <- get
    let i = lsNextLambdaId st
    put st{lsNextLambdaId = i + 1}
    pure i

addLiftedFunction :: MetallicFunction -> LiftM ()
addLiftedFunction fn = modify $ \st -> st{lsLiftedFunctions = fn : lsLiftedFunctions st}

computeFreeVars :: MetallicExpr -> Set.Set String
computeFreeVars (MVar v _) = Set.singleton v
computeFreeVars (MLit _) = Set.empty
computeFreeVars (MCall callee args _) = Set.unions (computeFreeVars callee : map computeFreeVars args)
computeFreeVars (MTypeApp e _ _) = computeFreeVars e
computeFreeVars (MLet name val body _) =
    Set.union (computeFreeVars val) (Set.delete name (computeFreeVars body))
computeFreeVars (MLambda params body _) =
    computeFreeVars body Set.\\ Set.fromList params
computeFreeVars (MConstruct _ _ args _) = Set.unions (map computeFreeVars args)
computeFreeVars (MArrayLit elems _) = Set.unions (map computeFreeVars elems)
computeFreeVars (MTuple elems _) = Set.unions (map computeFreeVars elems)
computeFreeVars (MCase scrutinees arms mdef _) =
    let scrFree = Set.unions (map computeFreeVars scrutinees)
        armsFree = Set.unions [computeFreeVars (mcaBody arm) Set.\\ Set.fromList (concatMap collectBinders (mcaPatterns arm)) | arm <- arms]
        defFree = maybe Set.empty computeFreeVars mdef
    in Set.unions [scrFree, armsFree, defFree]
computeFreeVars (MFieldAccess e _ _) = computeFreeVars e
computeFreeVars (MCompose stmts _) =
    let step (acc, bound) stmt =
            case stmt of
                MCBind name e ->
                    (acc `Set.union` (computeFreeVars e Set.\\ bound), Set.insert name bound)
                MCLet name e ->
                    (acc `Set.union` (computeFreeVars e Set.\\ bound), Set.insert name bound)
                MCExpr e ->
                    (acc `Set.union` (computeFreeVars e Set.\\ bound), bound)
        (fv, _) = foldl step (Set.empty, Set.empty) stmts
    in fv
computeFreeVars (MPanic _ _) = Set.empty

collectBinders :: Pattern -> [String]
collectBinders (PVar v) = [v]
collectBinders PWildcard = []
collectBinders (PLit _) = []
collectBinders (PAs v p) = v : collectBinders p
collectBinders (PConstructor _ ps) = concatMap collectBinders ps
collectBinders (PTuple ps) = concatMap collectBinders ps
collectBinders (PArray ps) = concatMap collectBinders ps

uncurryFunctionType :: Type -> ([Type], Type)
uncurryFunctionType ty = go ty []
  where
    go (TArrow t1 t2) acc = go t2 (acc ++ [t1])
    go t acc = (acc, t)
