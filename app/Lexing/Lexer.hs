module Lexing.Lexer (Token(..), TokenKind(..), tokenize, tokenizeFile, referenceToken, referenceTokenKind) where

import Lexing.Errors (LexingError(..))
import Data.Char (ord, generalCategory)
import qualified Data.Char as C

data TokenKind
    = TokenNumber
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
    | TokenDo
    | TokenLeftParenthesis
    | TokenRightParenthesis
    | TokenIdentifier
    | TokenPipe
    | TokenLet
    | TokenIn
    | TokenFn
    | TokenString
    | TokenDollar
    | TokenStruct
    | TokenComma
    | TokenLeftBracket
    | TokenRightBracket
    | TokenTrue
    | TokenFalse
    deriving (Show, Eq, Ord)

data Token = Token 
    { tokenKind :: TokenKind
    , tokenValue :: String
    , tokenPos :: Int
    , tokenIndent :: Int
    } deriving (Show, Eq, Ord)

tokenizeFile :: String -> Either LexingError [Token]
tokenizeFile content = do
    tokens <- tokenize content 0 0
    Right tokens

tokenize :: String -> Int -> Int -> Either LexingError [Token]
tokenize [] _ _ = Right []
tokenize (c:cs) i indent
    | isSpace c = tokenize cs (i + 1) indent
    | c == '+' = consToken (Token TokenPlus "+" i indent) (tokenize cs (i + 1) indent)
    | c == '*' = consToken (Token TokenAsterisk "*" i indent) (tokenize cs (i + 1) indent)
    | c == '=' = consToken (Token TokenEquals "=" i indent) (tokenize cs (i + 1) indent)
    | c == '>' = consToken (Token TokenRightAngleBracket ">" i indent) (tokenize cs (i + 1) indent)
    | c == '<' = consToken (Token TokenLeftAngleBracket "<" i indent) (tokenize cs (i + 1) indent)
    | c == '(' = consToken (Token TokenLeftParenthesis "(" i indent) (tokenize cs (i + 1) indent)
    | c == ')' = consToken (Token TokenRightParenthesis ")" i indent) (tokenize cs (i + 1) indent)
    | c == '|' = consToken (Token TokenPipe "|" i indent) (tokenize cs (i + 1) indent)
    | c == '$' = consToken (Token TokenDollar "$" i indent) (tokenize cs (i + 1) indent)
    | c == '[' = consToken (Token TokenLeftBracket "[" i indent) (tokenize cs (i + 1) indent)
    | c == ']' = consToken (Token TokenRightBracket "]" i indent) (tokenize cs (i + 1) indent)
    | c == ',' = consToken (Token TokenComma "," i indent) (tokenize cs (i + 1) indent)
    | c == ':' = case cs of
        ':' : rest -> consToken (Token TokenReturns "::" i indent) (tokenize rest (i + 2) indent)
        _ -> consToken (Token TokenColon ":" i indent) (tokenize cs (i + 1) indent)
    | c == '-' = case cs of
        '>' : rest -> consToken (Token TokenRightArrow "->" i indent) (tokenize rest (i + 2) indent)
        _ -> consToken (Token TokenMinus "-" i indent) (tokenize cs (i + 1) indent)
    | c == '\n' =
        let (spaces, rest) = span isSpace cs
            indentStr = spaces >>= (\w -> if w == '\t' then "    " else " ")
            newIndent = length spaces
        in consToken (Token TokenNewline indentStr i indent) (tokenize rest (i + 1 + length spaces) newIndent)
    | c == '/' = 
        case cs of
            '/' : rest -> do
                let (comment, rest') = span (/= '\n') rest
                tokenize rest' (i + 2 + length comment) indent
            _ -> consToken (Token TokenSlash "/" i indent) (tokenize cs (i + 1) indent)
    | c == '"' =
        let (text, rest) = span (/= '"') cs
            quotedText = c : text ++ "\""
        in case rest of
            '"' : rest' -> consToken (Token TokenString quotedText i indent) (tokenize rest' (i + length quotedText) indent)
            _ -> Left $ UnexpectedCharacter c i
    | isDigit c =
        let (numberToken, rest) = span isDigit (c:cs)
        in consToken (Token TokenNumber numberToken i indent) (tokenize rest (i + length numberToken) indent)
    | isCharacter c =
        let (text, rest) = span isCharacter (c:cs)
            kind = case text of
                "let" -> TokenLet
                "in"  -> TokenIn
                "fn"  -> TokenFn
                "case" -> TokenCase
                "do" -> TokenDo
                "struct" -> TokenStruct
                "true" -> TokenTrue
                "false" -> TokenFalse
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
isCharacter c = c `elem` ['a'..'z'] || c `elem` ['A'..'Z'] || c == '_' || isEmoji c

isEmoji :: Char -> Bool
isEmoji c
    | generalCategory c `elem` [C.OtherSymbol, C.MathSymbol, C.CurrencySymbol] = True
    | ord c >= 0x1F000 = True  -- Most emojis are above this range
    | otherwise = False

isSpace :: Char -> Bool
isSpace c = c == ' ' || c == '\t'

referenceToken :: Token -> String
referenceToken token = case tokenKind token of
    TokenNumber -> "number '" ++ tokenValue token ++ "'"
    TokenNewline -> "newline"
    TokenIdentifier -> "identifier '" ++ tokenValue token ++ "'"
    TokenString -> "string '" ++ tokenValue token ++ "'"
    _ -> "'" ++ tokenValue token ++ "'"

referenceTokenKind :: TokenKind -> String
referenceTokenKind kind = case kind of
    TokenNumber -> "a number"
    TokenNewline -> "a newline"
    TokenIdentifier -> "an identifier"
    TokenPlus -> "a plus sign"
    TokenMinus -> "a minus sign"
    TokenAsterisk -> "an asterisk"
    TokenDollar -> "a dollar sign"
    TokenSlash -> "a slash"
    TokenEquals -> "an equals sign"
    TokenLeftAngleBracket -> "a left angle bracket"
    TokenRightAngleBracket -> "a right angle bracket"
    TokenLeftArrow -> "a left arrow"
    TokenRightArrow -> "a right arrow"
    TokenColon -> "a colon"
    TokenReturns -> "'returns'"
    TokenCase -> "'case'"
    TokenDo -> "'do'"
    TokenLeftParenthesis -> "a left parenthesis"
    TokenRightParenthesis -> "a right parenthesis"
    TokenPipe -> "a vertical bar"
    TokenLet -> "'let'"
    TokenFn -> "'fn'"
    TokenIn -> "'in'"
    TokenString -> "a string"
    TokenStruct -> "a struct"
    TokenLeftBracket -> "a left bracket"
    TokenRightBracket -> "a right bracket"
    TokenComma -> "a comma"
    TokenTrue -> "'true'"
    TokenFalse -> "'false'"