module Analysis.Tree where
import Data.Map as Map
import Control.Monad.State
import Control.Monad.Except
import Parsing.Tree (Expression(..), ExpressionKind(..), exprChildren)
import Analysis.Inference (InferState(..), InferM, TypeMap, Substitution, composeS, Substitutable (apply), cleanRunInferM)
import Parsing.Type (Type(..))
import Analysis.Errors (AnalysisError(..))
import Control.Monad (foldM)
import qualified Debug.Trace as Debug

type TypeEnv = Map.Map String Type

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
        if ty1 /= ty2
            then throwError $ BinaryOpTypeMismatch expr ty1 ty2
            else do
                let s3 = composeS s2 s1
                recordType expr ty1
                pure (s3, ty1)
   
    FunctionExpr name params returnType body -> do
        let funcType = FunctionType (Prelude.map snd (Map.toList params)) returnType
        let env' = Map.insert name funcType env
        
        let env'' = Prelude.foldl (\acc (paramName, paramType) -> 
                            Debug.trace ("Inserted " ++ paramName) $ 
                            Map.insert paramName paramType acc) 
                        env' (Map.toList params)
        
        Debug.trace ("Final env " ++ show env'') $ pure ()
        
        (s, ty) <- inferExpr env'' body
        recordType expr (FunctionType (Prelude.map snd (Map.toList params)) ty)
        pure (s, funcType)
       
    VariableReferenceExpr name -> 
        case Map.lookup name env of
            Nothing -> Debug.trace ("Environment for lookup: " ++ show env ++ ", looking for: " ++ name) $ 
                       throwError $ UnboundVariable expr name
            Just ty -> do
                recordType expr ty
                pure (Map.empty, ty)
    
    _ -> throwError $ UntypedExpression expr

inferExprs :: TypeEnv -> [Expression] -> InferM (Substitution, [Type])
inferExprs _ [] = return (Map.empty, [])
inferExprs env (e:es) = do
    (s1, ty1) <- inferExpr env e
    (s2, tys) <- inferExprs (Map.map (apply s1) env) es
    return (composeS s2 s1, ty1 : tys)

analyzeTree :: Expression -> InferM TypeMap
analyzeTree root = do
    let env = Map.empty
    s <- traverseExpr env root
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
            
        Left UntypedExpression{} -> traverseChildren env expr
        Left err -> throwError err

traverseChildren :: TypeEnv -> Expression -> InferM Substitution
traverseChildren env expr = do
    let env' = case exprKind expr of
            FunctionExpr name params _ _ -> 
                let funcType = FunctionType (Prelude.map snd (Map.toList params)) IntType
                    envWithFunc = Map.insert name funcType env
                in Prelude.foldl (\acc (paramName, paramType) -> 
                      Map.insert paramName paramType acc) 
                    envWithFunc (Map.toList params)
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