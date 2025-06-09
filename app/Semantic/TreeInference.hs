{-# LANGUAGE LambdaCase #-}

module Semantic.TreeInference where

import Syntax.Tree (Expr (..), exprChildren)
import Semantic.Inference (TypeEnv, Subst, InferM, InferState (..), addGlobalBinding, TypeMap, composeSubst, Substitutable (apply), cleanRunInferM)
import Semantic.Errors (SemanticError(UntypedExpression, ParamLengthMismatch))
import Control.Monad.Error.Class (MonadError(throwError, catchError))
import Control.Monad.RWS (MonadState(get, put))
import qualified Data.Map as Map

import Typing.Currying (curryParams, curryFunction, getParamTypes)
import Typing.Types (Type(..), Kind (..), TyConstructor (TypeConstructor), TyVar (tvKind), intType)
import Control.Monad (foldM)

inferExpr :: TypeEnv -> Expr -> InferM (Subst, Type)
inferExpr _ expr@(ExprNum _ _) = do
    let ty = intType
    recordType expr ty
    return (Map.empty, ty)
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
    let constructor = TConstructor $ TypeConstructor name kind

    let valueConstructors =
            Prelude.map
                ( \case
                    ExprStructConstructor cName fields _ ->
                        let types = map snd fields
                            curried = curryFunction types constructor
                        in (cName, curried)
                    recv -> error $ "Expected StructConstructorExpr in struct definition but got " ++ show recv
                )
                constructors
    s <- get
    put s{structTypes = Map.union (Map.fromList valueConstructors) (Map.insert name constructor (structTypes s))}
    _ <-
        mapM
            ( \(vName, typ) -> do
                addGlobalBinding vName typ
            )
            valueConstructors
    mapM_ collectGlobals (exprChildren expr)
collectGlobals expr = pure () >> mapM_ collectGlobals (exprChildren expr)

data EnvContext = EnvContext
    { currentEnv :: TypeEnv
    , currentSubst :: Subst
    }

analyzeTree :: Expr -> InferM TypeMap
analyzeTree root = do
    collectGlobals root

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