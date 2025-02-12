module Lexing.Lexer (Token(..), TokenKind(..), tokenize, tokenizeFile) where

import Lexing.Errors (LexingError(..))

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

tokenizeFile :: String -> String -> Either LexingError [Token]
tokenizeFile path content = do
    tokens <- tokenize content 0 0
    return $ Token TokenBOF path 0 0 : tokens ++ [Token TokenEOF path (length content) 0]

tokenize :: String -> Int -> Int -> Either LexingError [Token]
tokenize [] _ _ = Right []
tokenize (c:cs) i indent
    | isSpace c = tokenize cs (i + 1) indent
    | c == '+' = consToken (Token TokenPlus "+" i indent) (tokenize cs (i + 1) indent)
    | c == '*' = consToken (Token TokenAsterisk "*" i indent) (tokenize cs (i + 1) indent)
    | c == '/' = consToken (Token TokenSlash "/" i indent) (tokenize cs (i + 1) indent)
    | c == '=' = consToken (Token TokenEquals "=" i indent) (tokenize cs (i + 1) indent)
    | c == '>' = consToken (Token TokenRightAngleBracket ">" i indent) (tokenize cs (i + 1) indent)
    | c == '<' = consToken (Token TokenLeftAngleBracket "<" i indent) (tokenize cs (i + 1) indent)
    | c == '(' = consToken (Token TokenLeftParenthesis "(" i indent) (tokenize cs (i + 1) indent)
    | c == ')' = consToken (Token TokenRightParenthesis ")" i indent) (tokenize cs (i + 1) indent)
    | c == '|' = consToken (Token TokenPipe "|" i indent) (tokenize cs (i + 1) indent)
    | c == ':' = case cs of
        ':' : rest -> consToken (Token TokenReturns "::" i indent) (tokenize rest (i + 2) indent)
        _ -> consToken (Token TokenColon ":" i indent) (tokenize cs (i + 1) indent)
    | c == '-' = case cs of
        '>' : rest -> consToken (Token TokenRightArrow "->" i indent) (tokenize rest (i + 2) indent)
        _ -> consToken (Token TokenMinus "-" i indent) (tokenize cs (i + 1) indent)
    | c == '\n' =
        let (spaces, rest) = span (\w -> w == ' ' || w == '\t') cs
            indentStr = spaces >>= (\w -> if w == '\t' then "    " else " ")
            newIndent = length spaces
        in consToken (Token TokenNewline indentStr i indent) (tokenize rest (i + 1 + length spaces) newIndent)
    | isDigit c =
        let (numberToken, rest) = span isDigit (c:cs)
        in consToken (Token TokenNumber numberToken i indent) (tokenize rest (i + length numberToken) indent)
    | isCharacter c =
        let (text, rest) = span isCharacter (c:cs)
            kind = case text of
                "let" -> TokenLet
                "fn"  -> TokenFn
                "case" -> TokenCase
                _     -> TokenIdentifier
        in consToken (Token kind text i indent) (tokenize rest (i + length text) indent)
    | otherwise = Left $ UnexpectedCharacter c i

consToken :: Token -> Either LexingError [Token] -> Either LexingError [Token]
consToken token restTokens = do
    rest <- restTokens
    Right (token : rest)

isDigit :: Char -> Bool
isDigit c = c `elem` ['0'..'9']

isCharacter :: Char -> Bool
isCharacter c = c `elem` ['a'..'z'] || c `elem` ['A'..'Z']

isSpace :: Char -> Bool
isSpace c = c == ' ' || c == '\t'