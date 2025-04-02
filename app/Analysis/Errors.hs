{-# LANGUAGE InstanceSigs #-}

module Analysis.Errors where

import Data.Foldable (maximumBy, minimumBy)
import Data.Ord (comparing)
import Lexing.Lexer (Token (tokenPos, tokenValue))
import Logging.ErrorPrinter (PrintableError (..))
import Parsing.Tree (Expression (exprKind, exprToken), exprChildren)
import Parsing.Type (Type)

data AnalysisError
    = TypeMismatch Expression Type Type
    | ParamLengthMismatch Expression
    | TupleLengthMismatch Expression
    | BinaryOpTypeMismatch Expression Type Type
    | CircularTypeDependency Expression
    | UnboundVariable Expression String
    | UntypedExpression Expression
    | NotAFunction Expression Type
    | UnknownStruct Expression String
    deriving (Show, Eq)

instance PrintableError AnalysisError where
    errorMessage :: AnalysisError -> String
    errorMessage (TypeMismatch _ t1 t2) = "Cannot conciliate types '" ++ show t1 ++ "' and '" ++ show t2 ++ "'"
    errorMessage (ParamLengthMismatch _) = "The function has a different number of arguments than provided"
    errorMessage (TupleLengthMismatch _) = "The tuple has a different number of elements than provided"
    errorMessage (BinaryOpTypeMismatch _ left right) = "Binary operation type mismatch (" ++ show left ++ " and " ++ show right ++ ")"
    errorMessage (CircularTypeDependency _) = "Circular type dependency"
    errorMessage (UnboundVariable _ name) = "Unbound variable '" ++ name ++ "'"
    errorMessage (UntypedExpression expr) = "The expression " ++ show expr ++ " is untyped"
    errorMessage (NotAFunction _ ty) = "The type " ++ show ty ++ " does not support function application"
    errorMessage (UnknownStruct _ name) = "Unknown struct '" ++ name ++ "'"

    errorStart :: AnalysisError -> Int
    errorStart err =
        let expr = getExpression err
            tokens = getAllTokens expr
            minToken = minimumBy (comparing tokenPos) tokens
        in tokenPos minToken

    errorEnd err =
        let expr = getExpression err
            tokens = getAllTokens expr
            maxToken = maximumBy (comparing tokenPos) tokens
        in tokenPos maxToken + length (tokenValue maxToken)

getExpression :: AnalysisError -> Expression
getExpression (TypeMismatch expr _ _) = expr
getExpression (BinaryOpTypeMismatch expr _ _) = expr
getExpression (ParamLengthMismatch expr) = expr
getExpression (TupleLengthMismatch expr) = expr
getExpression (CircularTypeDependency expr) = expr
getExpression (UnboundVariable expr _) = expr
getExpression (UntypedExpression expr) = expr
getExpression (NotAFunction expr _) = expr
getExpression (UnknownStruct expr _) = expr

getAllTokens :: Expression -> [Token]
getAllTokens expr =
    let current = [exprToken expr]
        children = exprChildren (exprKind expr)
        childTokens = concatMap getAllTokens children
    in current ++ childTokens
