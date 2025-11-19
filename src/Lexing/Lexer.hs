module Lexing.Lexer (
    Token (..),
    TokenKind (..),
    tokenize,
    tokenizeFile,
    referenceToken,
    referenceTokenKind,
    tokenSpan,
    spanningTokens,
) where

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
    | TokenCase
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
    | TokenString String
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
    | TokenSlash
    | TokenCompose
    | TokenBind
    | TokenIf
    | TokenThen
    | TokenElse
    | TokenLayoutStart
    | TokenLayoutSeparator
    | TokenLayoutEnd
    | TokenEOF -- this token isn't actually produced by the lexer, but it's useful for parser error recovery
    deriving (Show, Eq, Ord)

data Token = Token
    { tokenKind :: TokenKind
    , tokenValue :: String
    , tokenPos :: Int
    }
    deriving (Show, Eq, Ord)

tokenizeFile :: String -> ([Token], [LexingError])
tokenizeFile content = tokenize content 0 [0]

tokenize :: String -> Int -> [Int] -> ([Token], [LexingError])
tokenize [] i stack =
    let dedentTokens = map (\_ -> Token TokenLayoutEnd "" i) (tail stack)
    in (dedentTokens, [])
tokenize (c : cs) i stack
    | isSpace c = tokenize cs (i + 1) stack
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
        in addToken (Token kind [c] i) (tokenize cs (i + 1) stack)
    | c == '-' = case cs of
        '>' : rest -> addToken (Token TokenRightArrow "->" i) (tokenize rest (i + 2) stack)
        _ ->
            let (ops, rest) = span isOperatorChar (c : cs)
            in addToken (Token TokenVarSymbol ops i) (tokenize rest (i + length ops) stack)
    | c == '<'
    , ('-' : ' ' : cs') <- cs =
        addToken (Token TokenLeftArrow "<- " i) (tokenize cs' (i + 3) stack)
    | c == '=' = case cs of
        '=' : _rest ->
            let (ops, rest) = span isOperatorChar (c : cs)
            in addToken (Token TokenVarSymbol ops i) (tokenize rest (i + length ops) stack)
        '>' : rest -> addToken (Token TokenStrongRightArrow "=>" i) (tokenize rest (i + 2) stack)
        _ -> addToken (Token TokenEquals "=" i) (tokenize cs (i + 1) stack)
    | c == ':' = case cs of
        ':' : rest -> addToken (Token TokenReturns "::" i) (tokenize rest (i + 2) stack)
        _ -> addToken (Token TokenColon ":" i) (tokenize cs (i + 1) stack)
    | c == '/' = case cs of
        '/' : rest ->
            let (comment, rest') = span (/= '\n') rest
            in tokenize rest' (i + 2 + length comment) stack
        '*' : rest ->
            let (comment, rest') = break (== '*') rest
            in case rest' of
                '*' : '/' : rest'' ->
                    tokenize rest'' (i + 4 + length comment) stack
                _ ->
                    let (restTokens, restErrors) = tokenize rest' (i + 2 + length comment) stack
                    in (restTokens, UnterminatedComment i : restErrors)
        ' ' : _ ->
            let (ops, rest) = span isOperatorChar (c : cs)
            in addToken (Token TokenVarSymbol ops i) (tokenize rest (i + length ops) stack)
        _ ->
            addToken (Token TokenSlash "/" i) (tokenize cs (i + 1) stack)
        | c == '\n' =
                let (spaces, rest) = span isSpace cs
                    newIndent = length spaces
                    newI = i + 1 + length spaces
                    current = head stack
                    isEmpty = null rest || head rest == '\n' || all isSpace rest
                    (layoutTokens, newStack, newErrors)
                        | isEmpty = 
                            ([], stack, [])
                        | newIndent > current =
                            ([Token TokenLayoutStart "" i], newIndent : stack, [])
                        | newIndent == current =
                            if current > 0
                                then
                                    ([Token TokenLayoutSeparator "" i], stack, [])
                                else
                                    ([], stack, [])
                        | otherwise =
                            let
                                (dedentToks, remainingStack, isMatch) = dedentTo stack newIndent i
                            in
                                if isMatch
                                    then
                                        (dedentToks, remainingStack, [])
                                    else
                                        (dedentToks, newIndent : remainingStack, [InconsistentIndent i])
                    (restTokens, restErrors) = tokenize rest newI newStack
                in (layoutTokens ++ restTokens, newErrors ++ restErrors)
    | c == '|' = case cs of
        ' ' : rest -> addToken (Token TokenPipe "|" i) (tokenize rest (i + 2) stack)
        _ ->
            let (ops, rest) = span isOperatorChar (c : cs)
            in addToken (Token TokenVarSymbol ops i) (tokenize rest (i + length ops) stack)
    | c == '"' =
        if take 2 cs == "\"\""
            then
                let restAfterOpening = drop 2 cs
                    (text, rest) = breakTripleQuote restAfterOpening
                in case rest of
                    '"' : '"' : '"' : rest' ->
                        let quotedText = "\"\"\"" ++ text ++ "\"\"\""
                        in addToken (Token (TokenString text) quotedText i) (tokenize rest' (i + length quotedText) stack)
                    _ ->
                        let (restTokens, restErrors) = tokenize rest (i + length ("\"\"\"" ++ text)) stack
                        in (restTokens, UnterminatedString i : restErrors)
            else
                let (text, rest) = span (\x -> x /= '"' && x /= '\n') cs
                in case rest of
                    '"' : rest' ->
                        let quotedText = c : text ++ "\""
                        in addToken (Token (TokenString text) quotedText i) (tokenize rest' (i + length quotedText) stack)
                    '\n' : _ ->
                        let (restTokens, restErrors) = tokenize rest (i + length (c : text)) stack
                        in (restTokens, UnterminatedString i : restErrors)
                    _ ->
                        let (restTokens, restErrors) = tokenize rest (i + length (c : text)) stack
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
                in addToken (Token kind quotedText i) (tokenize rest' (i + length quotedText) stack)
            _ ->
                let (restTokens, restErrors) = tokenize rest (i + length (c : text)) stack
                in (restTokens, UnterminatedIdentifier i : restErrors)
    | isDigit c =
        let (numberToken, rest) = span isDigit (c : cs)
        in addToken (Token TokenNumber numberToken i) (tokenize rest (i + length numberToken) stack)
    | isCharacter c =
        let (text, rest) = span isAlphanumeric (c : cs)
            kind = case text of
                "let" -> TokenLet
                "in" -> TokenIn
                "case" -> TokenCase
                "def" -> TokenDef
                "intrinsic" -> TokenIntrinsic
                "use" -> TokenImport
                "data" -> TokenData
                "struct" -> TokenStruct
                "trait" -> TokenClass -- todo: rename
                "where" -> TokenWhere
                "instance" -> TokenInstance
                "true" -> TokenTrue
                "false" -> TokenFalse
                "bind" -> TokenBind
                "compose" -> TokenCompose
                "if" -> TokenIf
                "then" -> TokenThen
                "else" -> TokenElse
                _ ->
                    if C.isLower c
                        then TokenLowerIdentifier
                        else TokenUpperIdentifier
        in addToken (Token kind text i) (tokenize rest (i + length text) stack)
    | isOperatorChar c =
        let (ops, rest) = span isOperatorChar (c : cs)
        in addToken (Token TokenVarSymbol ops i) (tokenize rest (i + length ops) stack)
    | otherwise =
        let (restTokens, restErrors) = tokenize cs (i + 1) stack
        in (restTokens, UnexpectedCharacter c i : restErrors)

dedentTo :: [Int] -> Int -> Int -> ([Token], [Int], Bool)
dedentTo stack target pos = go stack []
  where
    go s accToks =
        if null s || head s <= target
            then
                (reverse accToks, s, not (null s) && head s == target)
            else
                go (tail s) (Token TokenLayoutEnd "" pos : accToks)

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
    TokenLowerIdentifier -> "lower-case identifier '" ++ tokenValue token ++ "'"
    TokenUpperIdentifier -> "upper-case identifier '" ++ tokenValue token ++ "'"
    TokenString str -> "string '" ++ str ++ "'"
    TokenLayoutStart -> "layout start"
    TokenLayoutSeparator -> "layout separator"
    TokenLayoutEnd -> "layout end"
    _ -> "'" ++ tokenValue token ++ "'"

referenceTokenKind :: TokenKind -> String
referenceTokenKind TokenNumber = "a number"
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
referenceTokenKind TokenDef = "'def'"
referenceTokenKind TokenIntrinsic = "'intrinsic'"
referenceTokenKind TokenImport = "'import'"
referenceTokenKind TokenSlash = "a slash"
referenceTokenKind TokenLeftParen = "a left parenthesis"
referenceTokenKind TokenRightParen = "a right parenthesis"
referenceTokenKind TokenPipe = "a vertical bar"
referenceTokenKind TokenLet = "'let'"
referenceTokenKind TokenIn = "'in'"
referenceTokenKind TokenThen = "'then'"
referenceTokenKind (TokenString _) = "a string"
referenceTokenKind TokenStruct = "a struct"
referenceTokenKind TokenData = "a data type"
referenceTokenKind TokenLeftBracket = "a left bracket"
referenceTokenKind TokenRightBracket = "a right bracket"
referenceTokenKind TokenComma = "a comma"
referenceTokenKind TokenTrue = "'true'"
referenceTokenKind TokenFalse = "'false'"
referenceTokenKind TokenClass = "'class'"
referenceTokenKind TokenWhere = "'where'"
referenceTokenKind TokenIf = "'if'"
referenceTokenKind TokenElse = "'else'"
referenceTokenKind TokenInstance = "'instance'"
referenceTokenKind TokenLambda = "'\\'"
referenceTokenKind TokenForall = "'∀'"
referenceTokenKind TokenUnderscore = "an underscore"
referenceTokenKind TokenBind = "'bind'"
referenceTokenKind TokenCompose = "'compose'"
referenceTokenKind TokenLayoutStart = "layout start"
referenceTokenKind TokenLayoutSeparator = "layout separator"
referenceTokenKind TokenLayoutEnd = "layout end"
referenceTokenKind TokenEOF = "end of file"

tokenSpan :: Token -> Span
tokenSpan token = Span (tokenPos token) (tokenPos token + length (tokenValue token))

spanningTokens :: Token -> Token -> Span
spanningTokens start end =
    Span (tokenPos start) (tokenPos end + length (tokenValue end))

isOperatorChar :: Char -> Bool
isOperatorChar c = c `elem` "!#$%&*+.-/<=>?@|"
