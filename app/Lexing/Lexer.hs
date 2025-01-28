module Lexing.Lexer (tokenize, tokenizeFile) where

data Token
    = TokenBOF String -- Beginning of file (file path)
    | TokenNumber String
    | TokenPlus
    | TokenMinus
    | TokenAsterisk
    | TokenSlash
    | TokenEquals
    | TokenLeftArrow
    | TokenRightArrow
    | TokenNewline Int -- Indentation level
    | TokenLeftParenthesis
    | TokenRightParenthesis
    | TokenIdentifier String
    | TokenLet
    | TokenFn
    | TokenEOF String
    deriving (Show, Eq)

tokenizeFile :: String -> String -> [Token]
tokenizeFile path content = TokenBOF path : tokenize content ++ [TokenEOF path]

tokenize :: String -> [Token]
tokenize [] = []
tokenize (c:cs)
    | isSpace c = tokenize cs
    | c == '+' = TokenPlus : tokenize cs
    | c == '-' = TokenMinus : tokenize cs
    | c == '*' = TokenAsterisk : tokenize cs
    | c == '/' = TokenSlash : tokenize cs
    | c == '=' = TokenEquals : tokenize cs
    | c == '>' = TokenRightArrow : tokenize cs
    | c == '<' = TokenLeftArrow : tokenize cs
    | c == '(' = TokenLeftParenthesis : tokenize cs
    | c == ')' = TokenRightParenthesis : tokenize cs
    | c == '\n' =
        let (spaces, rest) = span (\w -> w == ' ' || w == '\t') cs
            indent = sum (map (\w -> if w == '\t' then 4 else 1) spaces)
        in TokenNewline indent : tokenize rest
    | isDigit c =
        let (numberToken, rest) = span isDigit (c:cs)
        in TokenNumber (numberToken) : tokenize rest
    | isCharacter c =
        let (text, rest) = span isCharacter (c:cs)
        in case text of
            "let" -> TokenLet : tokenize rest
            "fn" -> TokenFn : tokenize rest
            none -> TokenIdentifier none : tokenize rest
    | otherwise = error $ "Unexpected character: " ++ [c]

isDigit :: Char -> Bool
isDigit c = c `elem` ['0'..'9']

isCharacter :: Char -> Bool
isCharacter c = c `elem` ['a'..'z'] || c `elem` ['A'..'Z']

isSpace :: Char -> Bool
isSpace c = c == ' ' || c == '\t'