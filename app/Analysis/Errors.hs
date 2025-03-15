{-# LANGUAGE InstanceSigs #-}
module Analysis.Errors where
import Parsing.Tree (Expression (exprToken, exprKind), exprChildren)
import Parsing.Type (Type)
import Logging.ErrorPrinter (PrintableError(..))
import Lexing.Lexer (Token(tokenPos, tokenValue))
import Data.Foldable (minimumBy, maximumBy)
import Data.Ord (comparing)

data AnalysisError 
    = UnificationError Expression
    | FunctionArgumentLengthMismatch Expression Expression
    | TupleLengthMismatch Expression Expression
    | BinaryOpTypeMismatch Expression Type Type
    | DifferentStructures Expression Expression
    | CircularTypeDependency Expression
    | UnboundVariable Expression String
    | UntypedExpression Expression

instance PrintableError AnalysisError where
    errorMessage (UnificationError expr) = "Unification error at " ++ show expr
    errorMessage (FunctionArgumentLengthMismatch expr1 expr2) = "Different argument lengths at " ++ show expr1 ++ " and " ++ show expr2
    errorMessage (TupleLengthMismatch expr1 expr2) = "Tuple length mismatch at " ++ show expr1 ++ " and " ++ show expr2
    errorMessage (BinaryOpTypeMismatch _ left right) = "Binary operation type mismatch (" ++ show left ++ " and " ++ show right ++ ")"
    errorMessage (DifferentStructures expr1 expr2) = "Different structures at " ++ show expr1 ++ " and " ++ show expr2
    errorMessage (CircularTypeDependency _) = "Circular type dependency"
    errorMessage (UnboundVariable _ name) = "Unbound variable '" ++ name ++ "'"
    errorMessage (UntypedExpression expr) = "The expression " ++ show expr ++ " is untyped"

    errorStart err =
        let expr = getExpression err
            tokens = exprToken expr : map exprToken (exprChildren (exprKind expr))
            minToken = minimumBy (comparing tokenPos) tokens
        in tokenPos minToken

    errorEnd :: AnalysisError -> Int
    errorEnd err =
        let expr = getExpression err
            tokens = exprToken expr : map exprToken (exprChildren (exprKind expr))
            maxToken = maximumBy (comparing tokenPos) tokens
        in tokenPos maxToken + length (tokenValue maxToken)



getExpression :: AnalysisError -> Expression
getExpression (UnificationError expr) = expr
getExpression (BinaryOpTypeMismatch expr _ _) = expr
getExpression (FunctionArgumentLengthMismatch expr1 _) = expr1
getExpression (TupleLengthMismatch expr1 _) = expr1
getExpression (DifferentStructures expr1 _) = expr1
getExpression (CircularTypeDependency expr) = expr
getExpression (UnboundVariable expr _) = expr
getExpression (UntypedExpression expr) = expr