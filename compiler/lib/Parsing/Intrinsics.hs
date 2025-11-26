module Parsing.Intrinsics (parseIntrinsic) where

import Lexing.Lexer (Token (tokenKind, tokenValue), TokenKind (..), spanningTokens)
import Parsing.Errors (ParsingError (..))
import Parsing.Parser (Parser, consume, parseFuncName, tryPeekOrEOF)
import Parsing.Types (parseKind, parseLocatedQualifiedType)
import Syntax.Tree (Expr (..))
import qualified Text.Megaparsec as MP

parseIntrinsic :: Parser Expr
parseIntrinsic = do
    _ <- consume TokenIntrinsic
    inc <- tryPeekOrEOF
    case tokenKind inc of
        TokenDef -> parseIntrinsicDef
        TokenData -> parseIntrinsicDataType
        _ -> MP.customFailure $ InvalidIntrinsic inc

parseIntrinsicDef :: Parser Expr
parseIntrinsicDef = do
    defTok <- consume TokenDef
    name <- parseFuncName
    retTok <- consume TokenReturns
    bindType <- parseLocatedQualifiedType
    pure
        $ ExprIntrinsicDef
            { intrinsicName = name
            , intrinsicType = bindType
            , intrinsicSpan = spanningTokens defTok retTok
            }

parseIntrinsicDataType :: Parser Expr
parseIntrinsicDataType = do
    dataTok <- consume TokenData
    name <- tokenValue <$> consume TokenUpperIdentifier
    retTok <- consume TokenReturns
    kind <- parseKind
    pure
        $ ExprIntrinsicDataTypeDef
            { intrinsicDataTypeName = name
            , intrinsicDataTypeKind = kind
            , intrinsicDataTypeSpan = spanningTokens dataTok retTok
            }
