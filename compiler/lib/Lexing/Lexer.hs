module Lexing.Lexer (
    Token (..),
    TokenKind (..),
    lexCode,
    referenceToken,
    referenceTokenKind,
    tokenSpan,
    spanningTokens,
) where

import Data.Char (generalCategory)
import qualified Data.Char as C
import Data.Text (Text)
import qualified Data.Text as T
import Lexing.Errors (LexingError (..))
import Lexing.Position (Span (Span))
import Utils.Lists (hardHead, hardTail)

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
    | TokenTrait
    | TokenWhere
    | TokenWith
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

lexCode :: Text -> ([Token], [LexingError])
lexCode content = lexCode' content 0 [0]

lexCode' :: Text -> Int -> [Int] -> ([Token], [LexingError])
lexCode' text i stack
    | T.null text =
        let dedentTokens = map (\_ -> Token TokenLayoutEnd "" i) (hardTail stack)
        in (dedentTokens, [])
lexCode' text i stack =
    let c = T.head text
        cs = T.tail text
    in case () of
        _
            | isSpace c -> lexCode' cs (i + 1) stack
            | c `elem` ("(){}[],λ\\∀_" :: String) ->
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
                in addToken (Token kind [c] i) (lexCode' cs (i + 1) stack)
            | c == '-' ->
                if T.isPrefixOf (T.pack ">") cs
                    then addToken (Token TokenRightArrow "->" i) (lexCode' (T.drop 1 cs) (i + 2) stack)
                    else
                        let (ops, rest) = T.span isOperatorChar text
                            opsStr = T.unpack ops
                        in addToken (Token TokenVarSymbol opsStr i) (lexCode' rest (i + T.length ops) stack)
            | c == '<' && T.isPrefixOf (T.pack "- ") cs ->
                addToken (Token TokenLeftArrow "<- " i) (lexCode' (T.drop 2 cs) (i + 3) stack)
            | c == '=' ->
                if T.isPrefixOf (T.pack "=") cs
                    then
                        let (ops, rest) = T.span isOperatorChar text
                            opsStr = T.unpack ops
                        in addToken (Token TokenVarSymbol opsStr i) (lexCode' rest (i + T.length ops) stack)
                    else
                        if T.isPrefixOf (T.pack ">") cs
                            then addToken (Token TokenStrongRightArrow "=>" i) (lexCode' (T.drop 1 cs) (i + 2) stack)
                            else addToken (Token TokenEquals "=" i) (lexCode' cs (i + 1) stack)
            | c == ':' ->
                if T.isPrefixOf (T.pack ":") cs
                    then addToken (Token TokenReturns "::" i) (lexCode' (T.drop 1 cs) (i + 2) stack)
                    else addToken (Token TokenColon ":" i) (lexCode' cs (i + 1) stack)
            | c == '/' ->
                if T.isPrefixOf (T.pack "/") cs
                    then
                        let (comment, rest') = T.span (/= '\n') (T.drop 1 cs)
                        in lexCode' rest' (i + 2 + T.length comment) stack
                    else
                        if T.isPrefixOf (T.pack "*") cs
                            then
                                let (comment, rest') = T.break (== '*') (T.drop 1 cs)
                                in if T.isPrefixOf (T.pack "*/") rest'
                                    then lexCode' (T.drop 2 rest') (i + 4 + T.length comment) stack
                                    else
                                        let (restTokens, restErrors) = lexCode' rest' (i + 2 + T.length comment) stack
                                        in (restTokens, UnterminatedComment i : restErrors)
                            else
                                if not (isAlphanumeric (T.head cs))
                                    then
                                        let (ops, rest) = T.span isOperatorChar text
                                            opsStr = T.unpack ops
                                        in addToken (Token TokenVarSymbol opsStr i) (lexCode' rest (i + T.length ops) stack)
                                    else
                                        addToken (Token TokenSlash "/" i) (lexCode' cs (i + 1) stack)
            | c == '\n' ->
                let (spaces, rest) = T.span isSpace cs
                    newIndent = T.length spaces
                    newI = i + 1 + T.length spaces
                    current = hardHead stack
                    isEmpty = T.null rest || T.head rest == '\n' || T.all isSpace rest
                    (layoutTokens, newStack, newErrors)
                        | isEmpty =
                            ([], stack, [])
                        | newIndent > current =
                            ([Token TokenLayoutStart "" i], newIndent : stack, [])
                        | newIndent == current =
                            ([Token TokenLayoutSeparator "" i], stack, [])
                        | otherwise =
                            let (dedentToks, remainingStack, isMatch) = dedentTo stack newIndent i
                            in if isMatch
                                then
                                    let separatorTok = [Token TokenLayoutSeparator "" i]
                                    in (dedentToks ++ separatorTok, remainingStack, [])
                                else
                                    (dedentToks, newIndent : remainingStack, [InconsistentIndent i])
                    (restTokens, restErrors) = lexCode' rest newI newStack
                in (layoutTokens ++ restTokens, newErrors ++ restErrors)
            | c == '|' ->
                if T.isPrefixOf (T.pack " ") cs
                    then addToken (Token TokenPipe "|" i) (lexCode' (T.drop 1 cs) (i + 2) stack)
                    else
                        let (ops, rest) = T.span isOperatorChar text
                            opsStr = T.unpack ops
                        in addToken (Token TokenVarSymbol opsStr i) (lexCode' rest (i + T.length ops) stack)
            | c == '"' ->
                if T.isPrefixOf (T.pack "\"\"") cs
                    then
                        let restAfterOpening = T.drop 2 cs
                            (textContent, rest) = breakTripleQuote restAfterOpening
                        in if T.isPrefixOf (T.pack "\"\"\"") rest
                            then
                                let textStr = T.unpack textContent
                                    quotedText = "\"\"\"" ++ textStr ++ "\"\"\""
                                in addToken (Token (TokenString textStr) quotedText i) (lexCode' (T.drop 3 rest) (i + length quotedText) stack)
                            else
                                let (restTokens, restErrors) = lexCode' rest (i + length ("\"\"\"" ++ T.unpack textContent)) stack
                                in (restTokens, UnterminatedString i : restErrors)
                    else
                        let (textContent, rest) = T.span (\x -> x /= '"' && x /= '\n') cs
                        in if T.isPrefixOf (T.pack "\"") rest
                            then
                                let textStr = T.unpack textContent
                                    quotedText = c : textStr ++ "\""
                                in addToken (Token (TokenString textStr) quotedText i) (lexCode' (T.drop 1 rest) (i + length quotedText) stack)
                            else
                                let (restTokens, restErrors) = lexCode' rest (i + 1 + T.length textContent) stack
                                in (restTokens, UnterminatedString i : restErrors)
            | c == '`' ->
                let (textContent, rest) = T.span (/= '`') cs
                in if T.isPrefixOf (T.pack "`") rest
                    then
                        let quotedText = c : T.unpack textContent ++ "`"
                            kind = case T.uncons textContent of
                                Nothing -> TokenLowerIdentifier -- default for empty backticks
                                Just (x, _) ->
                                    if C.isLower x
                                        then TokenLowerIdentifier
                                        else TokenUpperIdentifier
                        in addToken (Token kind quotedText i) (lexCode' (T.drop 1 rest) (i + length quotedText) stack)
                    else
                        let (restTokens, restErrors) = lexCode' rest (i + 1 + T.length textContent) stack
                        in (restTokens, UnterminatedIdentifier i : restErrors)
            | isDigit c ->
                let (numberToken, rest) = T.span isDigit text
                    numberStr = T.unpack numberToken
                in addToken (Token TokenNumber numberStr i) (lexCode' rest (i + T.length numberToken) stack)
            | isCharacter c ->
                let (textContent, rest) = T.span isAlphanumeric text
                    textStr = T.unpack textContent
                    kind = case textStr of
                        "let" -> TokenLet
                        "in" -> TokenIn
                        "case" -> TokenCase
                        "def" -> TokenDef
                        "intrinsic" -> TokenIntrinsic
                        "use" -> TokenImport
                        "data" -> TokenData
                        "struct" -> TokenStruct
                        "trait" -> TokenTrait
                        "where" -> TokenWhere
                        "with" -> TokenWith
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
                in addToken (Token kind textStr i) (lexCode' rest (i + T.length textContent) stack)
            | isOperatorChar c ->
                let (ops, rest) = T.span isOperatorChar text
                    opsStr = T.unpack ops
                in addToken (Token TokenVarSymbol opsStr i) (lexCode' rest (i + T.length ops) stack)
            | otherwise ->
                let (restTokens, restErrors) = lexCode' cs (i + 1) stack
                in (restTokens, UnexpectedCharacter c i : restErrors)

dedentTo :: [Int] -> Int -> Int -> ([Token], [Int], Bool)
dedentTo stack target pos = go stack []
  where
    go s accToks =
        if null s || hardHead s <= target
            then
                (reverse accToks, s, not (null s) && hardHead s == target)
            else case s of
                [] -> (reverse accToks, s, False)
                (_ : t) ->
                    go t (Token TokenLayoutEnd "" pos : accToks)

breakTripleQuote :: Text -> (Text, Text)
breakTripleQuote s = go s T.empty
  where
    go text acc
        | T.null text = (acc, T.empty)
        | T.length text >= 3 && T.isPrefixOf (T.pack "\"\"\"") text = (acc, text)
        | otherwise = go (T.tail text) (T.snoc acc (T.head text))

addToken :: Token -> ([Token], [LexingError]) -> ([Token], [LexingError])
addToken token (tokens, errors) = (token : tokens, errors)

isDigit :: Char -> Bool
isDigit c = c `elem` (['0' .. '9'] :: String)

isCharacter :: Char -> Bool
isCharacter c = c `elem` (['a' .. 'z'] :: String) || c `elem` (['A' .. 'Z'] :: String) || c == '_' || isEmoji c

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
referenceTokenKind TokenWith = "'with'"
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
referenceTokenKind TokenTrait = "'trait'"
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
isOperatorChar c = c `elem` ("!#$%&*+.-/<=>?@|" :: String)
