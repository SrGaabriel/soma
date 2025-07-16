module Lexing.Lexer (Token (..), TokenKind (..), tokenize, tokenizeFile, referenceToken, referenceTokenKind, tokenSpan, spanningTokens) where

import Data.Char (generalCategory)
import qualified Data.Char as C
import Lexing.Errors (LexingError (..))
import Lexing.Position (Span (Span))

data TokenKind
    = TokenNumber
    | TokenLeftAngleBracket
    | TokenRightAngleBracket
    | TokenLeftArrow
    | TokenRightArrow
    | TokenStrongRightArrow
    | TokenColon
    | TokenReturns
    | TokenNewline
    | TokenCase
    | TokenDo
    | TokenDef
    | TokenIntrinsic
    | TokenLeftParen
    | TokenRightParen
    | TokenLowerIdentifier
    | TokenUpperIdentifier
    | TokenVarSymbol
    | TokenPipe
    | TokenEquals
    | TokenLet
    | TokenIn
    | TokenImport
    | TokenString
    | TokenDollar
    | TokenStruct
    | TokenLeftBraces
    | TokenRightBraces
    | TokenData
    | TokenClass
    | TokenWhere
    | TokenInstance
    | TokenComma
    | TokenLeftBracket
    | TokenRightBracket
    | TokenTrue
    | TokenFalse
    | TokenLambda
    | TokenForall
    | TokenUnderscore
    deriving (Show, Eq, Ord)

data Token = Token
    { tokenKind :: TokenKind
    , tokenValue :: String
    , tokenPos :: Int
    , tokenIndent :: Int
    }
    deriving (Show, Eq, Ord)

tokenizeFile :: String -> ([Token], [LexingError])
tokenizeFile content = tokenize content 0 0

tokenize :: String -> Int -> Int -> ([Token], [LexingError])
tokenize [] _ _ = ([], [])
tokenize (c : cs) i indent
    | isSpace c = tokenize cs (i + 1) indent
    | c `elem` "(){}[],λ\\∀_" =
        let kind = case c of
                '(' -> TokenLeftParen
                ')' -> TokenRightParen
                '{' -> TokenLeftBraces
                '}' -> TokenRightBraces
                '[' -> TokenLeftBracket
                ']' -> TokenRightBracket
                ',' -> TokenComma
                'λ' -> TokenLambda
                '\\' -> TokenLambda
                '∀' -> TokenForall
                '_' -> TokenUnderscore
                _ -> error "Impossible case"
        in addToken (Token kind [c] i indent) (tokenize cs (i + 1) indent)
    | c == '-' = case cs of
        '>' : rest -> addToken (Token TokenRightArrow "->" i indent) (tokenize rest (i + 2) indent)
        _ ->
            let (ops, rest) = span isOperatorChar (c : cs)
            in addToken (Token TokenVarSymbol ops i indent) (tokenize rest (i + length ops) indent)
    | c == '=' = case cs of
        '=' : _rest ->
            let (ops, rest) = span isOperatorChar (c : cs)
            in addToken (Token TokenVarSymbol ops i indent) (tokenize rest (i + length ops) indent)
        '>' : rest -> addToken (Token TokenStrongRightArrow "=>" i indent) (tokenize rest (i + 2) indent)
        _ -> addToken (Token TokenEquals "=" i indent) (tokenize cs (i + 1) indent)
    | c == ':' = case cs of
        ':' : rest -> addToken (Token TokenReturns "::" i indent) (tokenize rest (i + 2) indent)
        _ -> addToken (Token TokenColon ":" i indent) (tokenize cs (i + 1) indent)
    | c == '/' = case cs of
        '/' : rest ->
            let (comment, rest') = span (/= '\n') rest
            in tokenize rest' (i + 2 + length comment) indent
        '*' : rest ->
            let (comment, rest') = break (== '*') rest
            in case rest' of
                '*' : '/' : rest'' ->
                    tokenize rest'' (i + 4 + length comment) indent
                _ ->
                    let (restTokens, restErrors) = tokenize rest' (i + 2 + length comment) indent
                    in (restTokens, UnterminatedComment i : restErrors)
        _ ->
            let (ops, rest) = span isOperatorChar (c : cs)
            in addToken (Token TokenVarSymbol ops i indent) (tokenize rest (i + length ops) indent)
    | c == '\n' =
        let (spaces, rest) = span isSpace cs
            indentStr = spaces >>= (\w -> if w == '\t' then "    " else " ")
            newIndent = length spaces
        in addToken (Token TokenNewline indentStr i indent) (tokenize rest (i + 1 + length spaces) newIndent)
    | c == '|' = case cs of
        ' ' : rest -> addToken (Token TokenPipe "|" i indent) (tokenize rest (i + 2) indent)
        _ ->
            let (ops, rest) = span isOperatorChar (c : cs)
            in addToken (Token TokenVarSymbol ops i indent) (tokenize rest (i + length ops) indent)
    | c == '"' =
        if take 2 cs == "\"\""
            then
                let restAfterOpening = drop 2 cs
                    (text, rest) = breakTripleQuote restAfterOpening
                in case rest of
                    '"' : '"' : '"' : rest' ->
                        let quotedText = "\"\"\"" ++ text ++ "\"\"\""
                        in addToken (Token TokenString quotedText i indent) (tokenize rest' (i + length quotedText) indent)
                    _ ->
                        let (restTokens, restErrors) = tokenize rest (i + length ("\"\"\"" ++ text)) indent
                        in (restTokens, UnterminatedString i : restErrors)
            else
                let (text, rest) = span (\x -> x /= '"' && x /= '\n') cs
                in case rest of
                    '"' : rest' ->
                        let quotedText = c : text ++ "\""
                        in addToken (Token TokenString quotedText i indent) (tokenize rest' (i + length quotedText) indent)
                    '\n' : _ ->
                        let (restTokens, restErrors) = tokenize rest (i + length (c : text)) indent
                        in (restTokens, UnterminatedString i : restErrors)
                    _ ->
                        let (restTokens, restErrors) = tokenize rest (i + length (c : text)) indent
                        in (restTokens, UnterminatedString i : restErrors)
    | c == '`' =
        let (text, rest) = span (/= '`') cs
        in case rest of
            '`' : rest' ->
                let quotedText = c : text ++ "`"
                    kind = case text of
                        [] -> TokenLowerIdentifier -- default for empty backticks
                        (x : _) ->
                            if C.isLower x
                                then TokenLowerIdentifier
                                else TokenUpperIdentifier
                in addToken (Token kind quotedText i indent) (tokenize rest' (i + length quotedText) indent)
            _ ->
                let (restTokens, restErrors) = tokenize rest (i + length (c : text)) indent
                in (restTokens, UnterminatedIdentifier i : restErrors)
    | isDigit c =
        let (numberToken, rest) = span isDigit (c : cs)
        in addToken (Token TokenNumber numberToken i indent) (tokenize rest (i + length numberToken) indent)
    | isCharacter c =
        let (text, rest) = span isAlphanumeric (c : cs)
            kind = case text of
                "let" -> TokenLet
                "in" -> TokenIn
                "case" -> TokenCase
                "do" -> TokenDo
                "def" -> TokenDef
                "intrinsic" -> TokenIntrinsic
                "import" -> TokenImport
                "data" -> TokenData
                "struct" -> TokenStruct
                "trait" -> TokenClass -- todo: rename
                "where" -> TokenWhere
                "instance" -> TokenInstance
                "true" -> TokenTrue
                "false" -> TokenFalse
                _ ->
                    if C.isLower c
                        then TokenLowerIdentifier
                        else TokenUpperIdentifier
        in addToken (Token kind text i indent) (tokenize rest (i + length text) indent)
    | isOperatorChar c =
        let (ops, rest) = span isOperatorChar (c : cs)
        in addToken (Token TokenVarSymbol ops i indent) (tokenize rest (i + length ops) indent)
    | otherwise =
        let (restTokens, restErrors) = tokenize cs (i + 1) indent
        in (restTokens, UnexpectedCharacter c i : restErrors)

breakTripleQuote :: String -> (String, String)
breakTripleQuote s = go s ""
  where
    go [] acc = (acc, [])
    go rest@(c1 : c2 : c3 : cs) acc
        | c1 == '"' && c2 == '"' && c3 == '"' = (acc, rest)
        | otherwise = go (c2 : c3 : cs) (acc ++ [c1])
    go [c1, c2] acc = (acc ++ [c1, c2], [])
    go [c1] acc = (acc ++ [c1], [])

addToken :: Token -> ([Token], [LexingError]) -> ([Token], [LexingError])
addToken token (tokens, errors) = (token : tokens, errors)

isDigit :: Char -> Bool
isDigit c = c `elem` ['0' .. '9']

isCharacter :: Char -> Bool
isCharacter c = c `elem` ['a' .. 'z'] || c `elem` ['A' .. 'Z'] || c == '_' || isEmoji c

isAlphanumeric :: Char -> Bool
isAlphanumeric c = isCharacter c || isDigit c

isEmoji :: Char -> Bool
isEmoji c = generalCategory c == C.OtherSymbol

isSpace :: Char -> Bool
isSpace c = c == ' ' || c == '\t'

referenceToken :: Token -> String
referenceToken token = case tokenKind token of
    TokenNumber -> "number '" ++ tokenValue token ++ "'"
    TokenNewline -> "newline"
    TokenLowerIdentifier -> "lower-case identifier '" ++ tokenValue token ++ "'"
    TokenUpperIdentifier -> "upper-case identifier '" ++ tokenValue token ++ "'"
    TokenString -> "string '" ++ tokenValue token ++ "'"
    _ -> "'" ++ tokenValue token ++ "'"

referenceTokenKind :: TokenKind -> String
referenceTokenKind TokenNumber = "a number"
referenceTokenKind TokenNewline = "a newline"
referenceTokenKind TokenLowerIdentifier = "a lower-case identifier"
referenceTokenKind TokenUpperIdentifier = "an upper-case identifier"
referenceTokenKind TokenVarSymbol = "a symbol"
referenceTokenKind TokenDollar = "a dollar sign"
referenceTokenKind TokenLeftAngleBracket = "a left angle bracket"
referenceTokenKind TokenRightAngleBracket = "a right angle bracket"
referenceTokenKind TokenLeftBraces = "a left brace"
referenceTokenKind TokenRightBraces = "a right brace"
referenceTokenKind TokenEquals = "an equals sign"
referenceTokenKind TokenLeftArrow = "a left arrow"
referenceTokenKind TokenRightArrow = "a right arrow"
referenceTokenKind TokenStrongRightArrow = "a double right arrow"
referenceTokenKind TokenColon = "a colon"
referenceTokenKind TokenReturns = "'::'"
referenceTokenKind TokenCase = "'case'"
referenceTokenKind TokenDo = "'do'"
referenceTokenKind TokenDef = "'def'"
referenceTokenKind TokenIntrinsic = "'intrinsic'"
referenceTokenKind TokenImport = "'import'"
referenceTokenKind TokenLeftParen = "a left parenthesis"
referenceTokenKind TokenRightParen = "a right parenthesis"
referenceTokenKind TokenPipe = "a vertical bar"
referenceTokenKind TokenLet = "'let'"
referenceTokenKind TokenIn = "'in'"
referenceTokenKind TokenString = "a string"
referenceTokenKind TokenStruct = "a struct"
referenceTokenKind TokenData = "a data type"
referenceTokenKind TokenLeftBracket = "a left bracket"
referenceTokenKind TokenRightBracket = "a right bracket"
referenceTokenKind TokenComma = "a comma"
referenceTokenKind TokenTrue = "'true'"
referenceTokenKind TokenFalse = "'false'"
referenceTokenKind TokenClass = "'class'"
referenceTokenKind TokenWhere = "'where'"
referenceTokenKind TokenInstance = "'instance'"
referenceTokenKind TokenLambda = "'\\'"
referenceTokenKind TokenForall = "'∀'"
referenceTokenKind TokenUnderscore = "an underscore"

tokenSpan :: Token -> Span
tokenSpan token = Span (tokenPos token) (tokenPos token + length (tokenValue token))

spanningTokens :: Token -> Token -> Span
spanningTokens start end =
    Span (tokenPos start) (tokenPos end + length (tokenValue end))

isOperatorChar :: Char -> Bool
isOperatorChar c = c `elem` "!#$%&*+.-/<=>?@|"
