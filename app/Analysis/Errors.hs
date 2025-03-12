{-# LANGUAGE InstanceSigs #-}
module Analysis.Errors where
import Parsing.Tree (Expression (exprToken, exprKind), exprChildren)
import Logging.ErrorPrinter (PrintableError(..))
import Lexing.Lexer (Token(tokenPos, tokenValue))
import Data.Foldable (minimumBy, maximumBy)
import Data.Ord (comparing)

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
getExpression (BinaryOpTypeMismatch expr) = expr
getExpression (DifferentArgumentLengths expr1 _) = expr1
getExpression (CannotConcretize expr) = expr