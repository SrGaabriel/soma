module Lexing.Lexer (tokenize, tokenizeFile) where

data Token
    = TokenBOF String -- Beginning of file (file path)
    | TokenNumber Int
    | TokenPlus
    | TokenMinus
    | TokenAsterisk
    | TokenSlash
    | TokenLeftParenthesis
    | TokenRightParenthesis
    | TokenWhitespace
    | TokenEgg
    | TokenEOF String
    deriving (Show, Eq)

tokenizeFile :: String -> String -> [Token]
tokenizeFile path content = TokenBOF path : tokenize content ++ [TokenEOF path]

tokenize :: String -> [Token]
tokenize [] = []
tokenize (c:cs)
    | isSpace c = TokenWhitespace : tokenize cs
    | c == '+' = TokenPlus : tokenize cs
    | c == '-' = TokenMinus : tokenize cs
    | c == '*' = TokenAsterisk : tokenize cs
    | c == '/' = TokenSlash : tokenize cs
    | c == '(' = TokenLeftParenthesis : tokenize cs
    | c == ')' = TokenRightParenthesis : tokenize cs
    | isDigit c =
        let (numberToken, rest) = span isDigit (c:cs)
        in TokenNumber (read numberToken) : tokenize rest
    | otherwise = error $ "Unexpected character: " ++ [c]

isDigit :: Char -> Bool
isDigit c = c `elem` ['0'..'9']

isSpace :: Char -> Bool
isSpace c = c == ' ' || c == '\t'