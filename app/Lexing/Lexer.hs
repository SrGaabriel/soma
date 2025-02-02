module Lexing.Lexer (Token(..), TokenKind(..), tokenize, tokenizeFile) where

data TokenKind
    = TokenBOF
    | TokenNumber
    | TokenPlus
    | TokenMinus
    | TokenAsterisk
    | TokenSlash
    | TokenEquals
    | TokenLeftAngleBracket
    | TokenRightAngleBracket
    | TokenLeftArrow
    | TokenRightArrow
    | TokenColon
    | TokenReturns
    | TokenNewline
    | TokenLeftParenthesis
    | TokenRightParenthesis
    | TokenIdentifier
    | TokenLet
    | TokenFn
    | TokenEOF
    deriving (Show, Eq)

data Token = Token 
    { tokenKind :: TokenKind
    , tokenValue :: String 
    } deriving (Show, Eq)

tokenizeFile :: String -> String -> [Token]
tokenizeFile path content = Token TokenBOF path : tokenize content ++ [Token TokenEOF path]

tokenize :: String -> [Token]
tokenize [] = []
tokenize (c:cs)
    | isSpace c = tokenize cs
    | c == '+' = Token TokenPlus "+" : tokenize cs
    | c == '*' = Token TokenAsterisk "*" : tokenize cs
    | c == '/' = Token TokenSlash "/" : tokenize cs
    | c == '=' = Token TokenEquals "=" : tokenize cs
    | c == '>' = Token TokenRightAngleBracket ">" : tokenize cs
    | c == '<' = Token TokenLeftAngleBracket ">" : tokenize cs
    | c == '(' = Token TokenLeftParenthesis "(" : tokenize cs
    | c == ')' = Token TokenRightParenthesis ")" : tokenize cs
    | c == ':' = case cs of
        ':' : rest -> Token TokenReturns "::" : tokenize rest
        _ -> Token TokenColon ":" : tokenize cs
    | c == '-' = case cs of
        '>' : rest -> Token TokenRightArrow "->" : tokenize rest
        _ -> Token TokenMinus "-" : tokenize cs
    | c == '\n' =
        let (spaces, rest) = span (\w -> w == ' ' || w == '\t') cs
            indent = spaces >>= (\w -> if w == '\t' then "    " else " ") 
        in Token TokenNewline indent : tokenize rest
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