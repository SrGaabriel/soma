module Analysis.Tree where
import Data.Map as Map
import Control.Monad.State
import Control.Monad.Except
import Parsing.Tree (Expression(..), ExpressionKind(..), exprChildren)
import Analysis.Inference (InferState(..), InferM, TypeMap, TypeEnv, Substitution, composeS, Substitutable (apply), cleanRunInferM, unify, instantiate)
import Parsing.Type (Type(..), StructVariant (StructVariant))
import Analysis.Errors (AnalysisError(..))
import Control.Monad (foldM)

addGlobalBinding :: String -> Type -> InferM ()
addGlobalBinding name ty = do
    s <- get
    let globals = globalEnv s
    put s { globalEnv = Map.insert name ty globals }

recordType :: Expression -> Type -> InferM ()
recordType expr ty = do
    s <- get
    put s { inferTypeMap = Map.insert expr ty (inferTypeMap s) }

inferExpr :: TypeEnv -> Expression -> InferM (Substitution, Type)
inferExpr _ expr@(Expression _ NumberExpr) = do
    let ty = IntType
    recordType expr ty
    pure (Map.empty, ty)

inferExpr _ expr@(Expression _ (BoolExpr _)) = do
    let ty = BoolType
    recordType expr ty
    pure (Map.empty, ty)

inferExpr _ expr@(Expression _ (StringExpr _)) = do
    let ty = StringType
    recordType expr ty
    pure (Map.empty, ty)

inferExpr env expr@(Expression _ (BinaryOpExpr left right _)) = do
    (s1, ty1) <- inferExpr env left
    (s2, ty2) <- inferExpr (Map.map (apply s1) env) right

    s3 <- unify expr ty1 ty2
    let finalSubst = composeS s3 (composeS s2 s1)
    let resultType = apply finalSubst ty1
    recordType expr resultType
    pure (finalSubst, resultType)

inferExpr env expr@(Expression _ (FunctionExpr name params returnType body)) = do
    let funcType = FunctionType (Prelude.map snd (Map.toList params)) returnType
    
    addGlobalBinding name funcType
    
    let localEnv = Prelude.foldl (\acc (paramName, paramType) -> 
                        Map.insert paramName paramType acc) 
                    env (Map.toList params)
    
    (s, bodyType) <- inferExpr localEnv body
    unifySubst <- unify body returnType bodyType
    let finalSubst = composeS unifySubst s

    recordType expr (FunctionType (Prelude.map snd (Map.toList params)) returnType)
    pure (finalSubst, funcType)

inferExpr env expr@(Expression _ (ConstantBindingExpr name bindType body)) = do
    addGlobalBinding name bindType

    let env' = Map.insert name bindType env
    (s, bodyType) <- inferExpr env' body
    unifySubst <- unify body bindType bodyType
    let finalSubst = composeS unifySubst s

    recordType expr bindType
    pure (finalSubst, bindType)
    
inferExpr env expr@(Expression _ (FunctionCallExpr fn arg)) = do
    (s1, fnType) <- inferExpr env fn
    (s2, argType) <- inferExpr (Map.map (apply s1) env) arg
    let s3 = composeS s2 s1
    case fnType of
        FunctionType (param : params) retType -> do
            s4 <- unify arg param argType
            let s5 = composeS s4 s3
            let newRetType = apply s4 retType
            let newFnType = if Prelude.null params then newRetType else FunctionType (Prelude.map (apply s4) params) newRetType
            recordType expr newFnType
            pure (s5, newFnType)
        _ -> throwError $ NotAFunction expr fnType
   
inferExpr env expr@(Expression _ (ValueReferenceExpr name)) = do
    case Map.lookup name env of
        Just ty -> do
            recordType expr ty
            pure (Map.empty, ty)
        Nothing -> do
            s <- get
            let globals = globalEnv s
            case Map.lookup name globals of
                Just ty -> do
                    instantiatedTy <- instantiate ty
                    recordType expr instantiatedTy
                    pure (Map.empty, instantiatedTy)
                Nothing -> throwError $ UnboundVariable expr name

inferExpr env expr@(Expression _ (LetExpr name value body)) = do
    (s1, valueType) <- inferExpr env value
    let env' = Map.insert name valueType (Map.map (apply s1) env)
    (s2, bodyType) <- inferExpr env' body
    let finalSubst = composeS s2 s1
    recordType expr bodyType
    pure (finalSubst, bodyType)

inferExpr env expr@(Expression _ (BlockExpr expressions)) = do
    (subs, tys) <- inferExprs env expressions
    let resultType = last tys
    recordType expr resultType
    pure (subs, resultType)

inferExpr _ expr = throwError $ UntypedExpression expr

replaceGeneric :: Type -> Type -> Type -> Type
replaceGeneric genType@(GenericType generic) newType ty = case ty of
    GenericType g | g == generic -> newType
    FunctionType args ret -> FunctionType (Prelude.map (replaceGeneric genType newType) args) (replaceGeneric genType newType ret)
    StructType name variants (Just gs) | GenericType generic `elem` gs ->
        StructType name (Prelude.map (replaceInVariant genType newType) variants) (Just $ Prelude.map (replaceGeneric genType newType) gs)
    _ -> ty
replaceGeneric _ _ ty = ty

replaceInVariant :: Type -> Type -> StructVariant -> StructVariant
replaceInVariant generic newType (StructVariant vName fields) =
    StructVariant vName (Map.map (replaceGeneric generic newType) fields)

inferExprs :: TypeEnv -> [Expression] -> InferM (Substitution, [Type])
inferExprs _ [] = return (Map.empty, [])
inferExprs env (e:es) = do
    (s1, ty1) <- inferExpr env e
    (s2, tys) <- inferExprs (Map.map (apply s1) env) es
    return (composeS s2 s1, ty1 : tys)

collectGlobals :: Expression -> InferM ()
collectGlobals expr = case exprKind expr of
    FunctionExpr name params returnType _ -> do
        let funcType = FunctionType (Prelude.map snd (Map.toList params)) returnType
        addGlobalBinding name funcType
        
    ConstantBindingExpr name bindType _ -> do
        addGlobalBinding name bindType
    
    StructExpr name constructors generics -> do
        let variants = Prelude.map (\(Expression _ ek) -> case ek of
                    StructConstructorExpr cName fields -> 
                        StructVariant cName (Map.fromList $ Prelude.map (\x -> case x of
                            Expression _ (StructFieldExpr fName ty) -> (fName, ty)
                            _ -> error "Expected StructFieldExpr in struct definition"
                        ) fields)
                    recv -> error $ "Expected StructConstructorExpr in struct definition but got " ++ show recv
                ) constructors

        let structType = StructType name variants (Prelude.map GenericType <$> generics)
        s <- get
        put s { structTypes = Map.insert name structType (structTypes s) }

        _ <- mapM (\(StructVariant vName fields) -> do
                let constructorType = FunctionType (Prelude.map snd (Map.toList fields)) structType
                addGlobalBinding vName constructorType
            ) variants
        pure ()
        
    _ -> pure ()
    
    >> mapM_ collectGlobals (exprChildren (exprKind expr))

analyzeTree :: Expression -> InferM TypeMap
analyzeTree root = do
    collectGlobals root
    
    s <- traverseTree Map.empty root
    infState <- get
    let finalTypeMap = Map.map (apply s) (inferTypeMap infState)
    return finalTypeMap

data EnvContext = EnvContext {
    currentEnv :: TypeEnv,
    currentSubst :: Substitution
}

traverseTree :: TypeEnv -> Expression -> InferM Substitution
traverseTree env expr = evalNode EnvContext { currentEnv = env, currentSubst = Map.empty } expr

evalNode :: EnvContext -> Expression -> InferM Substitution
evalNode ctx expr = do
    result <- tryInferExpr (currentEnv ctx) expr
    
    ctx' <- case result of
        Right (s, _) -> do
            let updatedSubst = composeS s (currentSubst ctx)
            let updatedEnv = Map.map (apply s) (currentEnv ctx)
            return ctx { currentEnv = updatedEnv, currentSubst = updatedSubst }
        Left UntypedExpression {} -> 
            return ctx
        Left err -> 
            throwError err
    
    childSubst <- case exprKind expr of
        LetExpr name value body -> do
            valueSubst <- evalNode ctx' value
            
            valueResult <- tryInferExpr (currentEnv ctx') value
            
            let bodyCtx = case valueResult of
                    Right (_, valueType) -> 
                        ctx' { 
                            currentEnv = Map.insert name valueType (currentEnv ctx'),
                            currentSubst = valueSubst
                        }
                    _ -> ctx' { currentSubst = valueSubst }
            
            evalNode bodyCtx body
            
        FunctionExpr _ params _ body -> do
            let paramEnv = Prelude.foldl (\acc (paramName, paramType) -> 
                              Map.insert paramName paramType acc)
                            (currentEnv ctx') (Map.toList params)
            
            evalNode ctx' { currentEnv = paramEnv } body
            
        _ -> 
            foldM (\s child -> 
                evalNode ctx' { currentSubst = s } child
            ) (currentSubst ctx') (exprChildren (exprKind expr))
    
    return childSubst

tryInferExpr :: TypeEnv -> Expression -> InferM (Either AnalysisError (Substitution, Type))
tryInferExpr env expr = catchError
    (do
        (s, t) <- inferExpr env expr
        return (Right (s, t))
    )
    (\err -> return (Left err))

runAnalysis :: Expression -> IO (Either AnalysisError TypeMap)
runAnalysis expr = do
    (result, _) <- cleanRunInferM (analyzeTree expr)
    return result