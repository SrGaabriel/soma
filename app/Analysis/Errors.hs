module Analysis.Errors where
import Parsing.Tree (Expression (exprToken))
import Logging.ErrorPrinter (PrintableError(..))
import Lexing.Lexer (Token(tokenPos))

data AnalysisError 
    = UnificationError Expression
    | DifferentArgumentLengths Expression Expression
    | CannotConcretize Expression
    | BinaryOpTypeMismatch Expression

instance PrintableError AnalysisError where
    errorMessage (UnificationError expr) = "Unification error at " ++ show expr
    errorMessage (DifferentArgumentLengths expr1 expr2) = "Different argument lengths at " ++ show expr1 ++ " and " ++ show expr2
    errorMessage (CannotConcretize expr) = "Cannot concretize at " ++ show expr
    errorMessage (BinaryOpTypeMismatch expr) = "Binary operation type mismatch at " ++ show expr

    errorStart err = tokenPos $ exprToken $ getExpression err
    errorEnd err = tokenPos $ exprToken $ getExpression err -- TODO: use leftmost and rightmost tokens

getExpression :: AnalysisError -> Expression
getExpression (UnificationError expr) = expr
getExpression (BinaryOpTypeMismatch expr) = expr
getExpression (DifferentArgumentLengths expr1 _) = expr1
getExpression (CannotConcretize expr) = expr