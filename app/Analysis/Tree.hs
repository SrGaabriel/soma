module Analysis.Tree where
import Data.Map as Map
import Control.Monad.State
import Control.Monad.Except
import Parsing.Tree (Expression(..), ExpressionKind(..), exprChildren)
import Analysis.Inference (InferState(..), InferM, TypeMap, TypeEnv, Substitution, composeS, Substitutable (apply), cleanRunInferM, unify)
import Parsing.Type (Type(..))
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
inferExpr env expr = case exprKind expr of
    NumberExpr -> do
        let ty = IntType
        recordType expr ty
        pure (Map.empty, ty)
       
    StringExpr _ -> do
        let ty = StringType
        recordType expr ty
        pure (Map.empty, ty)
   
    BinaryOpExpr left right _ -> do
        (s1, ty1) <- inferExpr env left
        (s2, ty2) <- inferExpr (Map.map (apply s1) env) right

        s3 <- unify expr ty1 ty2
        let finalSubst = composeS s3 (composeS s2 s1)
        let resultType = apply finalSubst ty1
        recordType expr resultType
        pure (finalSubst, resultType)

    FunctionExpr name params returnType body -> do
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

    ConstantBindingExpr name bindType body -> do
        addGlobalBinding name bindType

        let env' = Map.insert name bindType env
        (s, bodyType) <- inferExpr env' body
        unifySubst <- unify expr bindType bodyType
        let finalSubst = composeS unifySubst s

        recordType expr bindType
        pure (finalSubst, bindType)
       
    ValueReferenceExpr name -> do
        case Map.lookup name env of
            Just ty -> do
                recordType expr ty
                pure (Map.empty, ty)
            Nothing -> do
                s <- get
                let globals = globalEnv s
                case Map.lookup name globals of
                    Just ty -> do
                        recordType expr ty
                        pure (Map.empty, ty)
                    Nothing -> throwError $ UnboundVariable expr name
    
    _ -> throwError $ UntypedExpression expr

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
        
    _ -> pure ()
    
    >> mapM_ collectGlobals (exprChildren (exprKind expr))

analyzeTree :: Expression -> InferM TypeMap
analyzeTree root = do
    collectGlobals root
    
    s <- traverseExpr Map.empty root
    infState <- get
    let finalTypeMap = Map.map (apply s) (inferTypeMap infState)
    return finalTypeMap

traverseExpr :: TypeEnv -> Expression -> InferM Substitution
traverseExpr env expr = do
    result <- tryInferExpr env expr
    case result of
        Right (s, _) -> do
            let env' = Map.map (apply s) env
            childSubst <- traverseChildren env' expr
            return (composeS childSubst s)

        Left UntypedExpression {} -> traverseChildren env expr
        Left err -> throwError err

traverseChildren :: TypeEnv -> Expression -> InferM Substitution
traverseChildren env expr = do
    let env' = case exprKind expr of
            FunctionExpr _ params _ _ -> 
                Prelude.foldl (\acc (paramName, paramType) -> 
                      Map.insert paramName paramType acc) 
                    env (Map.toList params)
            _ -> env

    let children = exprChildren (exprKind expr)
    foldM (\s child -> do
        let childEnv = Map.map (apply s) env'
        childSubst <- traverseExpr childEnv child
        return (composeS childSubst s)
      ) Map.empty children

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