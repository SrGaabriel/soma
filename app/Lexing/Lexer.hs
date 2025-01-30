module Lexing.Lexer (Token(..), TokenKind(..), tokenize, tokenizeFile) where

data TokenKind
    = TokenBOF String -- Beginning of file (file path)
    | TokenNumber
    | TokenPlus
    | TokenMinus
    | TokenAsterisk
    | TokenSlash
    | TokenEquals
    | TokenLeftArrow
    | TokenRightArrow
    | TokenNewline Int
    | TokenLeftParenthesis
    | TokenRightParenthesis
    | TokenIdentifier
    | TokenLet
    | TokenFn
    | TokenEOF String
    deriving (Show, Eq)

data Token = Token 
    { tokenKind :: TokenKind
    , value :: String 
    } deriving (Show, Eq)

tokenizeFile :: String -> String -> [Token]
tokenizeFile path content = Token (TokenBOF "") path : tokenize content ++ [Token (TokenEOF "") path]

tokenize :: String -> [Token]
tokenize [] = []
tokenize (c:cs)
    | isSpace c = tokenize cs
    | c == '+' = Token TokenPlus "+" : tokenize cs
    | c == '-' = Token TokenMinus "-" : tokenize cs
    | c == '*' = Token TokenAsterisk "*" : tokenize cs
    | c == '/' = Token TokenSlash "/" : tokenize cs
    | c == '=' = Token TokenEquals "=" : tokenize cs
    | c == '>' = Token TokenRightArrow ">" : tokenize cs
    | c == '<' = Token TokenLeftArrow ">" : tokenize cs
    | c == '(' = Token TokenLeftParenthesis "(" : tokenize cs
    | c == ')' = Token TokenRightParenthesis ")" : tokenize cs
    | c == '\n' =
        let (spaces, rest) = span (\w -> w == ' ' || w == '\t') cs
            indent = sum (map (\w -> if w == '\t' then 4 else 1) spaces)
        in Token (TokenNewline indent) "\n" : tokenize rest
    | isDigit c =
        let (numberToken, rest) = span isDigit (c:cs)
        in Token TokenNumber numberToken : tokenize rest
    | isCharacter c =
        let (text, rest) = span isCharacter (c:cs)
            kind = case text of
                "let" -> TokenLet
                "fn"  -> TokenFn
                _     -> TokenIdentifier
        in Token kind text : tokenize rest
    | otherwise = error $ "Unexpected character: " ++ [c]

isDigit :: Char -> Bool
isDigit c = c `elem` ['0'..'9']

isCharacter :: Char -> Bool
isCharacter c = c `elem` ['a'..'z'] || c `elem` ['A'..'Z']

isSpace :: Char -> Bool
isSpace c = c == ' ' || c == '\t'