module Parsing.Errors (ParsingError (..), getErrorToken) where

import Lexing.Lexer (Token (..), TokenKind, referenceToken, referenceTokenKind)
import Logging.Errors (PrintableError (..))
import Text.Megaparsec (ShowErrorComponent (showErrorComponent))

data ParsingError
    = UnexpectedToken Token
    | ExpectedDifferentToken
        { expected :: TokenKind
        , received :: Token
        }
    | InvalidTokenForTopLevelDeclaration Token
    | InvalidTokenForType Token
    | ExpectedIndentation Token -- for when a token isn't indented (int is the next newline)
    | ExpectedDifferentIndentation Token Int Int -- for when the indentation is wrong
    | UnseparatedStatements Token -- for when two statements are on the same line
    | InvalidIdentifierFollowup Token
    | FunctionArgumentLengthMismatch Token
    | NotAnExpression Token
    | ExpectedAnExpression Token
    | ExpectedAGenericType Token
    | InvalidGenericsList Token
    | InvalidPattern Token
    | InvalidFunctionBody Token
    | InvalidFunctionName Token
    | EndOfInput
    | Debug
    deriving (Eq, Ord)

instance Show ParsingError where
    show (UnexpectedToken t) = "Unexpected token " ++ referenceToken t
    show (ExpectedDifferentToken tExpected tReceived) = "Expected " ++ referenceTokenKind tExpected ++ " but received " ++ referenceToken tReceived
    show (InvalidTokenForType t) = "The token " ++ referenceToken t ++ " can't be used as a type"
    show (ExpectedIndentation t) = "Expected indentation for " ++ referenceToken t
    show (UnseparatedStatements t) = "Unseparated statements by newline at " ++ referenceToken t
    show (InvalidIdentifierFollowup t) = "Invalid identifier follow-up: " ++ referenceToken t
    show (FunctionArgumentLengthMismatch _) = "The function has more arguments than declared"
    show (InvalidTokenForTopLevelDeclaration t) = "The token " ++ referenceToken t ++ " can't be used as a top-level declaration"
    show (ExpectedDifferentIndentation _ expc recv) = "Expected indentation of " ++ show expc ++ " spaces but received " ++ show recv
    show (NotAnExpression t) = "You can't use " ++ referenceToken t ++ " as an expression"
    show (ExpectedAnExpression _) = "Expected an expression but received an abrupt end"
    show (InvalidGenericsList t) = "Invalid generics list at " ++ referenceToken t
    show (ExpectedAGenericType t) = "Expected a generic type but received " ++ referenceToken t
    show (InvalidPattern t) = "The expression " ++ referenceToken t ++ " is not a valid pattern"
    show (InvalidFunctionBody t) = "The expression " ++ referenceToken t ++ " is not a valid function body"
    show (InvalidFunctionName t) = "The expression " ++ referenceToken t ++ " is not a valid function name"
    show EndOfInput = "End of input"
    show Debug = "Debug"

instance PrintableError ParsingError where
    errorMessage = show

    errorStart EndOfInput = -1 -- todo: remove workaround
    errorStart Debug = -1
    errorStart err = case getErrorToken err of
        Just t -> tokenPos t
        Nothing -> error $ "Unreachable errorStart case reached: " ++ show err

    errorEnd EndOfInput = -1
    errorEnd Debug = -1
    errorEnd err = case getErrorToken err of
        Just t -> tokenPos t + length (tokenValue t)
        Nothing -> error $ "Unreachable errorEnd case reached: " ++ show err

    errorDebugDevDetails = show . getErrorToken

instance ShowErrorComponent ParsingError where
    showErrorComponent = show    

getErrorToken :: ParsingError -> Maybe Token
getErrorToken (UnexpectedToken t) = Just t
getErrorToken (ExpectedDifferentToken _ t) = Just t
getErrorToken (InvalidTokenForType t) = Just t
getErrorToken (ExpectedIndentation t) = Just t
getErrorToken (InvalidIdentifierFollowup t) = Just t
getErrorToken (ExpectedDifferentIndentation t _ _) = Just t
getErrorToken (FunctionArgumentLengthMismatch t) = Just t
getErrorToken (UnseparatedStatements t) = Just t
getErrorToken (InvalidTokenForTopLevelDeclaration t) = Just t
getErrorToken (NotAnExpression t) = Just t
getErrorToken (InvalidPattern t) = Just t
getErrorToken (InvalidGenericsList t) = Just t
getErrorToken (ExpectedAGenericType t) = Just t
getErrorToken (ExpectedAnExpression t) = Just t
getErrorToken (InvalidFunctionBody t) = Just t
getErrorToken (InvalidFunctionName t) = Just t
getErrorToken EndOfInput = Nothing
getErrorToken Debug = Nothing
