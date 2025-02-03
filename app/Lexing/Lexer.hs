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
    | TokenCase
    | TokenLeftParenthesis
    | TokenRightParenthesis
    | TokenIdentifier
    | TokenPipe
    | TokenLet
    | TokenFn
    | TokenEOF
    deriving (Show, Eq)

data Token = Token 
    { tokenKind :: TokenKind
    , tokenValue :: String
    , tokenPos :: Int
    , tokenIndent :: Int
    } deriving (Show, Eq)

tokenizeFile :: String -> String -> [Token]
tokenizeFile path content = Token TokenBOF path 0 0 : tokenize content 0 0 ++ [Token TokenEOF path (length content) 0]

tokenize :: String -> Int -> Int -> [Token]
tokenize [] _ _ = []
tokenize (c:cs) i indent
    | isSpace c = tokenize cs (i + 1) indent
    | c == '+' = Token TokenPlus "+" i indent : tokenize cs (i + 1) indent
    | c == '*' = Token TokenAsterisk "*" i indent : tokenize cs (i + 1) indent
    | c == '/' = Token TokenSlash "/" i indent : tokenize cs (i + 1) indent
    | c == '=' = Token TokenEquals "=" i indent : tokenize cs (i + 1) indent
    | c == '>' = Token TokenRightAngleBracket ">" i indent : tokenize cs (i + 1) indent
    | c == '<' = Token TokenLeftAngleBracket "<" i indent : tokenize cs (i + 1) indent
    | c == '(' = Token TokenLeftParenthesis "(" i indent : tokenize cs (i + 1) indent
    | c == ')' = Token TokenRightParenthesis ")" i indent : tokenize cs (i + 1) indent
    | c == '|' = Token TokenPipe "|" i indent : tokenize cs (i + 1) indent
    | c == ':' = case cs of
        ':' : rest -> Token TokenReturns "::" i indent : tokenize rest (i + 2) indent
        _ -> Token TokenColon ":" i indent : tokenize cs (i + 1) indent
    | c == '-' = case cs of
        '>' : rest -> Token TokenRightArrow "->" i indent : tokenize rest (i + 2) indent
        _ -> Token TokenMinus "-" i indent : tokenize cs (i + 1) indent
    | c == '\n' =
        let (spaces, rest) = span (\w -> w == ' ' || w == '\t') cs
            indentStr = spaces >>= (\w -> if w == '\t' then "    " else " ")
            newIndent = length spaces
        in Token TokenNewline indentStr i indent : tokenize rest (i + 1 + length spaces) newIndent
    | isDigit c =
        let (numberToken, rest) = span isDigit (c:cs)
        in Token TokenNumber numberToken i indent : tokenize rest (i + length numberToken) indent
    | isCharacter c =
        let (text, rest) = span isCharacter (c:cs)
            kind = case text of
                "let" -> TokenLet
                "fn"  -> TokenFn
                "case" -> TokenCase
                _     -> TokenIdentifier
        in Token kind text i indent : tokenize rest (i + length text) indent
    | otherwise = error $ "Unexpected character: " ++ [c] ++ " at index " ++ show i

isDigit :: Char -> Bool
isDigit c = c `elem` ['0'..'9']

isCharacter :: Char -> Bool
isCharacter c = c `elem` ['a'..'z'] || c `elem` ['A'..'Z']

isSpace :: Char -> Bool
isSpace c = c == ' ' || c == '\t'