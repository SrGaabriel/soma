{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}

module Souls.Loc where

import Control.Lens ((^.))
import Data.Maybe (listToMaybe, mapMaybe)
import qualified Data.Text as T
import Language.LSP.Protocol.Lens (HasParams, HasPosition, HasTextDocument, HasUri)
import qualified Language.LSP.Protocol.Lens as L
import Language.LSP.Protocol.Types
import Lexing.Position (Span (..))
import Project.Symbols (Symbol)
import Syntax.Tree (Expr (..), exprChildren, exprSpan)

spanToRange :: T.Text -> Span -> Range
spanToRange code (Span start' end') =
    Range (offsetToPosition code start') (offsetToPosition code end')

lspPositionToOffset :: T.Text -> Position -> Int
lspPositionToOffset text (Position line' col) =
    let linesList = T.lines text
        precedingChars = sum $ map (\l -> T.length l + 1) (take (fromIntegral line') linesList)
    in precedingChars + fromIntegral col

offsetToPosition :: T.Text -> Int -> Position
offsetToPosition text offset =
    let
        (prefix, _) = T.splitAt offset text
        line' = fromIntegral $ T.count (T.pack "\n") prefix
        col = fromIntegral $ T.length $ T.takeWhileEnd (/= '\n') prefix
    in
        Position line' col

findExprAtPos :: Int -> Expr -> Maybe Expr
findExprAtPos offset expr =
    case expr of
        ExprRoot{} ->
            listToMaybe (mapMaybe (findExprAtPos offset) (exprChildren expr))
        _ ->
            case listToMaybe (mapMaybe (findExprAtPos offset) (exprChildren expr)) of
                Just e -> Just e
                Nothing -> if exprContainsOffset offset expr then Just expr else Nothing
  where
    exprContainsOffset off e =
        let Span start' end' = exprSpan e
        in off >= start' && off < end'

findSymbolAtPos :: Int -> Expr -> Maybe Symbol
findSymbolAtPos offset expr =
    case listToMaybe (mapMaybe (findSymbolAtPos offset) (exprChildren expr)) of
        Just s -> Just s
        Nothing -> case expr of
            ExprVar sym span' | offsetInSpan offset span' -> Just sym
            _ -> Nothing
  where
    offsetInSpan off (Span start' end') = off >= start' && off < end'

extractReq ::
    (HasParams s a, HasPosition a Position, HasTextDocument a b, HasUri b Uri) =>
    s -> (Position, Uri)
extractReq req =
    let pos = req ^. L.params . L.position
        fileUri = req ^. L.params . L.textDocument . L.uri
    in (pos, fileUri)
