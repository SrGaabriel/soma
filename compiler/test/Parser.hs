{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}

module Parser (spec) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Data.Vector.Strict as V
import Maple.Ast (fromRaw)
import Maple.Cache (mkCache)
import Maple.Green (Green (GNode, GToken), GreenNode (GreenNode, gnChildren, gnKind, gnWidth), GreenToken (GreenToken, gtKind, gtSymbol))
import Soma.Syntax.Kind (Kind)
import Soma.Syntax.Lexer (lexAll)
import Soma.Syntax.Parser (parseRoot, runParser)
import Symbolize (unintern)
import Test.Hspec (Spec, describe, it, shouldBe)

basicSource :: Text
basicSource = "def id (a : Nat) : Nat := a\n"

showKind :: Int -> String
showKind raw = show (fromRaw raw :: Kind)

renderNode :: Int -> GreenNode -> [Text]
renderNode depth GreenNode{gnKind, gnChildren} =
    (indent depth <> T.pack (showKind gnKind))
        : concatMap (renderGreen (depth + 1)) (V.toList gnChildren)

renderGreen :: Int -> Green -> [Text]
renderGreen depth (GNode n) = renderNode depth n
renderGreen depth (GToken GreenToken{gtKind, gtSymbol}) =
    [indent depth <> T.pack (showKind gtKind) <> " " <> T.pack (show (unintern gtSymbol :: Text))]

indent :: Int -> Text
indent depth = T.replicate depth "  "

spec :: Spec
spec = describe "basic.soma" $ do
    it "lexes without diagnostics" $ do
        let (toks, diag) = lexAll basicSource
        putStrLn $ show toks
        diag `shouldBe` []

    it "parses without diagnostics" $ do
        ((root, _), diag) <- runParser basicSource mkCache parseRoot
        TIO.putStrLn (T.unlines (renderNode 0 root))
        diag `shouldBe` []

    it "parses with the same tree size as source length" $ do
        ((GreenNode{gnWidth}, _), _) <- runParser basicSource mkCache parseRoot
        gnWidth `shouldBe` (T.length basicSource)
