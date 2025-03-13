module Analysis.Tree where

import Data.Map as Map
import Control.Monad.State
import Control.Monad.Except
import Parsing.Tree (Expression(..), ExpressionKind(..), exprChildren)
import Analysis.Inference (TypeScheme(..), InferState(..), InferM (runInfer), concretize, fresh)
import Parsing.Type (Type(..))
import Data.Maybe (fromJust)
import Analysis.Errors (AnalysisError (BinaryOpTypeMismatch))
import Control.Monad (foldM, forM_)

type TypeMap = Map.Map Expression Type

storeType :: Expression -> TypeScheme -> InferM ()
storeType expr t = modify $ \s -> 
    s { inferTypeMap = Map.insert expr t (inferTypeMap s) }

quickInferExpr :: Expression -> InferM (Maybe TypeScheme)
quickInferExpr expr = case exprKind expr of
    NumberExpr -> do
        let t = STypeLiteral IntType
        storeType expr t
        return $ Just t
    StringExpr _ -> do
        let t = STypeLiteral StringType
        storeType expr t
        return $ Just t
    BinaryOpExpr left right _ -> do 
        opLeft <- quickInferExpr left
        _opRight <- quickInferExpr right
        -- todo add constraint for opLeft = opRight
        let opLeft' = fromJust opLeft
        storeType expr opLeft'
        return opLeft
    BlockExpr expressions -> do
        lastExprT <- foldM (\_ express -> quickInferExpr express) Nothing expressions
        forM_ lastExprT (storeType expr)
        return lastExprT
    VariableReferenceExpr _ -> do
        t <- fresh
        storeType expr t
        return $ Just t
    _ -> return Nothing

inferExpr :: Expression -> InferM (Maybe TypeScheme)
inferExpr expr = do
    scheme <- quickInferExpr expr
    case scheme of
        Just t -> return $ Just t
        Nothing -> do
            let children = exprChildren $ exprKind expr
            _childrenTypes <- mapM inferExpr children
            return $ Nothing

runInference :: Expression -> Either AnalysisError TypeMap
runInference expr =
    let initialState = InferState 0 Map.empty
        computation = runInfer (do
            _ <- inferExpr expr
            st <- get
            let typedNodes = Map.mapMaybe concretize (inferTypeMap st)
            return typedNodes)
    in case runState (runExceptT computation) initialState of
        (Left err, _) -> Left err
        (Right typeMap, _) -> Right typeMap