{-# LANGUAGE LambdaCase #-}

module Semantic.TreeInference where

import Control.Monad.Error.Class (MonadError (catchError, throwError))
import Control.Monad.RWS (MonadState (get, put))
import qualified Data.Map as Map
import Semantic.Errors (SemanticError (..))
import Semantic.Inference (InferM, InferState (..), Subst, Substitutable (apply), TypeEnv, TypeMap, addGlobalBinding, cleanRunInferM, composeSubst, fresh, unify)
import Syntax.Tree (Expr (..), exprChildren)

import Control.Monad (foldM)
import Typing.Currying (curryFunction, curryParams, getParamTypes)
import Typing.Types (Constraint (..), Kind (..), TyConstructor (TypeConstructor, tcKind), TyVar (tvKind), Type (..), intType, strType)

inferExpr :: TypeEnv -> Expr -> InferM (Subst, Type)
inferExpr _ expr@(ExprNum _ _) = do
    let ty = intType
    recordType expr ty
    return (Map.empty, ty)
inferExpr _ expr@(ExprStr _ _) = do
    let ty = strType
    recordType expr ty
    return (Map.empty, ty)
inferExpr env expr@(ExprVar name _) = do
    case Map.lookup name env of
        Just ty -> do
            recordType expr ty
            return (Map.empty, ty)
        Nothing -> do
            s <- get
            let globals = globalEnv s
            case Map.lookup name globals of
                Just ty -> do
                    recordType expr ty
                    return (Map.empty, ty)
                Nothing -> throwError $ UnboundVariable expr name
inferExpr env expr@(ExprApp fn arg) = do
    (s1, fnType) <- inferExpr env fn
    (s2, argType) <- inferExpr (Map.map (apply s1) env) arg
    let s3 = composeSubst s2 s1
    case fnType of
        TArrow param retType -> do
            s4 <- unify arg param argType
            let s5 = composeSubst s4 s3
            let newRetType = apply s4 retType
            recordType expr newRetType
            pure (s5, newRetType)
        _ -> throwError $ NotAFunction expr fnType
inferExpr env expr@(ExprBinaryOp _ left right) = do
    (s1, leftType) <- inferExpr env left
    (s2, rightType) <- inferExpr (Map.map (apply s1) env) right

    s3 <- unify expr leftType rightType
    let s4 = composeSubst s3 (s2 `composeSubst` s1)
    let resultType = apply s4 leftType
    recordType expr resultType
    pure (s4, resultType)
inferExpr env expr@(ExprLet name value body _) = do
    (s1, valueType) <- inferExpr env value
    let env' = Map.insert name valueType (Map.map (apply s1) env)
    (s2, bodyType) <- inferExpr env' body
    let s3 = composeSubst s2 s1
    recordType expr bodyType
    pure (s3, bodyType)
inferExpr env expr@(ExprLambda names body _) = do
    typeVars <- Prelude.mapM (\_ -> TVar <$> fresh KindStar) names
    let params = zip names typeVars
    let localEnv = Map.union (Map.fromList params) env
    (s, bodyType) <- inferExpr localEnv body
    let lambdaType = curryParams params bodyType
    recordType expr lambdaType
    pure (s, lambdaType)
inferExpr _ expr = throwError $ UntypedExpression expr

collectGlobals :: Expr -> InferM ()
collectGlobals expr@(ExprFunctionDef name params returnType _ _) = do
    let funcType = (curryParams params) returnType
    addGlobalBinding name funcType
    mapM_ collectGlobals (exprChildren expr)
collectGlobals expr@(ExprConstantDef name bindType _ _) = do
    addGlobalBinding name bindType
    mapM_ collectGlobals (exprChildren expr)
collectGlobals expr@(ExprStructDef name generics constructors _) = do
    let kind = foldr KindArrow KindStar (map tvKind generics)
    let baseConstructor = TConstructor $ TypeConstructor name kind

    let structType =
            if null generics
                then baseConstructor
                else foldl TApp baseConstructor (map TVar generics)

    let valueConstructors =
            Prelude.map
                ( \case
                    ExprStructConstructor cName fields _ ->
                        let fieldTypes = map snd fields
                            curried = curryFunction fieldTypes structType
                        in (cName, curried)
                    recv -> error $ "Expected StructConstructorExpr in struct definition but got " ++ show recv
                )
                constructors

    s <- get
    let updatedConstructors =
            Map.union
                (Map.fromList valueConstructors)
                (Map.insert name baseConstructor (constructorsInScope s))
    put s{constructorsInScope = updatedConstructors}

    _ <- mapM (\(vName, typ) -> addGlobalBinding vName typ) valueConstructors

    mapM_ collectGlobals (exprChildren expr)
collectGlobals expr = pure () >> mapM_ collectGlobals (exprChildren expr)

data EnvContext = EnvContext
    { currentEnv :: TypeEnv
    , currentSubst :: Subst
    }

analyzeTree :: Expr -> InferM TypeMap
analyzeTree root = do
    collectGlobals root
    resolveAllUnresolvedTypes root

    s <- traverseTree Map.empty root
    infState <- get
    let finalTypeMap = Map.map (apply s) (inferTypeMap infState)
    return finalTypeMap

traverseTree :: TypeEnv -> Expr -> InferM Subst
traverseTree env expr = evalNode EnvContext{currentEnv = env, currentSubst = Map.empty} expr

evalNode :: EnvContext -> Expr -> InferM Subst
evalNode ctx expr = do
    result <- tryInferExpr (currentEnv ctx) expr

    ctx' <- case result of
        Right (s, _) -> do
            let updatedSubst = composeSubst s (currentSubst ctx)
            let updatedEnv = Map.map (apply s) (currentEnv ctx)
            return ctx{currentEnv = updatedEnv, currentSubst = updatedSubst}
        Left UntypedExpression{} ->
            return ctx
        Left err ->
            throwError err

    childSubst <- case expr of
        ExprLet name value body _ -> do
            valueSubst <- evalNode ctx' value

            valueResult <- tryInferExpr (currentEnv ctx') value

            let bodyCtx = case valueResult of
                    Right (_, valueType) ->
                        ctx'
                            { currentEnv = Map.insert name valueType (currentEnv ctx')
                            , currentSubst = valueSubst
                            }
                    _ -> ctx'{currentSubst = valueSubst}

            evalNode bodyCtx body
        ExprFunctionDef _ params _ body _ -> do
            let paramEnv =
                    Prelude.foldl
                        ( \acc (paramName, paramType) ->
                            Map.insert paramName paramType acc
                        )
                        (currentEnv ctx')
                        params

            evalNode ctx'{currentEnv = paramEnv} body
        ExprLambda names body _ -> do
            case result of
                Right (s, ty) -> do
                    let updatedSubst = composeSubst s (currentSubst ctx)
                    let updatedEnv = Map.map (apply s) (currentEnv ctx)
                    let paramTypes = getParamTypes ty
                    if length paramTypes /= length names
                        then throwError $ ParamLengthMismatch expr
                        else do
                            let paramEnv = Map.fromList (zip names paramTypes)
                            let localEnv = Map.union paramEnv updatedEnv
                            evalNode ctx{currentEnv = localEnv, currentSubst = updatedSubst} body
                Left err -> do
                    throwError err
        _ ->
            foldM
                ( \s child ->
                    evalNode ctx'{currentSubst = s} child
                )
                (currentSubst ctx')
                (exprChildren expr)

    return childSubst

tryInferExpr :: TypeEnv -> Expr -> InferM (Either SemanticError (Subst, Type))
tryInferExpr env expr =
    catchError
        ( do
            (s, t) <- inferExpr env expr
            return (Right (s, t))
        )
        (\err -> return (Left err))

runAnalysis :: Expr -> IO (Either SemanticError TypeMap)
runAnalysis expr = do
    (result, _) <- cleanRunInferM (analyzeTree expr)
    return result

recordType :: Expr -> Type -> InferM ()
recordType expr ty = do
    s <- get
    put s{inferTypeMap = Map.insert expr ty (inferTypeMap s)}
resolveAllUnresolvedTypes :: Expr -> InferM ()
resolveAllUnresolvedTypes = resolveInExpr
  where
    resolveInExpr currentExpr = do
        case currentExpr of
            ExprFunctionDef name params returnType body _ -> do
                resolvedReturnType <- resolveUnresolvedWithEnv currentExpr returnType
                resolvedParams <-
                    mapM
                        ( \(pName, pType) -> do
                            resolvedPType <- resolveUnresolvedWithEnv currentExpr pType
                            return (pName, resolvedPType)
                        )
                        params
                let resolvedFuncType = curryParams resolvedParams resolvedReturnType
                s <- get
                put s{globalEnv = Map.insert name resolvedFuncType (globalEnv s)}
                resolveInExpr body
            ExprConstantDef name bindType value _ -> do
                resolvedBindType <- resolveUnresolvedWithEnv currentExpr bindType
                s <- get
                put s{globalEnv = Map.insert name resolvedBindType (globalEnv s)}
                resolveInExpr value
            ExprStructDef _ _ constructors _ -> do
                mapM_ resolveInExpr constructors
            ExprStructConstructor _ fields _ -> do
                _ <-
                    mapM
                        ( \(fieldName, fieldType) -> do
                            resolvedFieldType <- resolveUnresolvedWithEnv currentExpr fieldType
                            return (fieldName, resolvedFieldType)
                        )
                        fields
                return ()
            _ -> mapM_ resolveInExpr (exprChildren currentExpr)

resolveUnresolvedTypes :: InferM ()
resolveUnresolvedTypes = do
    s <- get
    let typeMap = inferTypeMap s
    let resolvedTypeMap = Map.map resolveUnresolvedInType typeMap
    put s{inferTypeMap = resolvedTypeMap}

resolveUnresolvedInType :: Type -> Type
resolveUnresolvedInType = go
  where
    go ty@(TUnresolved _ _) = ty
    go ty@(TVar _) = ty
    go ty@(TConstructor _) = ty
    go (TApp t1 t2) = TApp (go t1) (go t2)
    go (TArrow t1 t2) = TArrow (go t1) (go t2)
    go (TForall tv t) = TForall tv (go t)
    go (TTuple ts) = TTuple (map go ts)
    go (TConstrained cs t) = TConstrained (map resolveUnresolvedInConstraint cs) (go t)

resolveUnresolvedInConstraint :: Constraint -> Constraint
resolveUnresolvedInConstraint (Constraint t ts) =
    Constraint t (map resolveUnresolvedInType ts)

resolveUnresolvedWithEnv :: Expr -> Type -> InferM Type
resolveUnresolvedWithEnv expr (TApp (TUnresolved name expectedKind) arg) = do
    s <- get
    let constructors = constructorsInScope s
    case Map.lookup name constructors of
        Just (TConstructor tc) -> do
            resolvedArg <- resolveUnresolvedWithEnv expr arg
            return (TApp (TConstructor tc) resolvedArg)
        Just resolvedType -> do
            resolvedArg <- resolveUnresolvedWithEnv expr arg
            return (TApp resolvedType resolvedArg)
        Nothing -> throwError $ UnknownTypeConstructor expr name expectedKind
resolveUnresolvedWithEnv expr ty = go ty
  where
    go (TUnresolved name expectedKind) = do
        s <- get
        let constructors = constructorsInScope s
        case Map.lookup name constructors of
            Just (TConstructor tc) ->
                if tcKind tc == expectedKind
                    then return (TConstructor tc)
                    else throwError $ KindMismatch expr expectedKind (tcKind tc)
            Just resolvedType -> return resolvedType
            Nothing -> throwError $ UnknownTypeConstructor expr name expectedKind
    go (TVar tv) = return (TVar tv)
    go (TConstructor tc) = return (TConstructor tc)
    go (TApp t1 t2) = do
        t1' <- go t1
        t2' <- go t2
        return (TApp t1' t2')
    go (TArrow t1 t2) = do
        t1' <- go t1
        t2' <- go t2
        return (TArrow t1' t2')
    go (TForall tv t) = do
        t' <- go t
        return (TForall tv t')
    go (TTuple ts) = do
        ts' <- mapM go ts
        return (TTuple ts')
    go (TConstrained cs t) = do
        cs' <- mapM (resolveConstraintWithEnv expr) cs
        t' <- go t
        return (TConstrained cs' t')

resolveConstraintWithEnv :: Expr -> Constraint -> InferM Constraint
resolveConstraintWithEnv expr (Constraint t ts) = do
    ts' <- mapM (resolveUnresolvedWithEnv expr) ts
    return (Constraint t ts')
