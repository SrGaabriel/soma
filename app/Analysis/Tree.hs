module Analysis.Tree where

import Data.Map as Map
import Control.Monad.State
import Control.Monad.Except
import Parsing.Tree (Expression(..), ExpressionKind(..), getChildren)
import Analysis.Inference (TypeScheme(..), InferState(..), InferM)
import Parsing.Type (Type(IntType))
import Analysis.Errors (AnalysisError(BinaryOpTypeMismatch))

storeType :: Expression -> TypeScheme -> InferM ()
storeType expr t = modify $ \s -> 
    s { inferTypeMap = Map.insert expr t (inferTypeMap s) }

inferExpr :: Expression -> InferM TypeScheme
inferExpr expr = case exprKind expr of
    NumberExpr -> do
        let t = STypeLiteral IntType
        storeType expr t
        return t
    BinaryOpExpr left right _ -> do
        opLeft <- inferExpr left
        opRight <- inferExpr right
        if opLeft /= opRight
            then throwError $ BinaryOpTypeMismatch expr
            else do
                storeType expr opLeft
                return opLeft
    _ -> do
        -- TODO: remove (this is just done to traverse the entire tree instead of stopping on Untyped nodes)
        let children = getChildren $ exprKind expr
        types <- mapM inferExpr children
        let t = case types of
                []     -> SUntyped
                (x:_)  -> x
        storeType expr t
        return t