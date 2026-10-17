{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Parser (spec) where

import Blammo.Logging (Logger)
import Blammo.Logging.Setup (newLoggerEnv)
import Control.Exception (SomeException, evaluate, try)
import Control.Monad (forM, forM_, unless, when)
import Data.List (isSuffixOf, sort)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Data.Vector.Strict as V
import Maple.Cache (mkCache)
import Maple.Green (Green (GNode, GToken), GreenNode (GreenNode, gnChildren), GreenToken (GreenToken, gtSymbol))
import Maple.Position (Range (Range), posRowCol)
import Maple.Print (prettyGreen, showKind)
import Soma.Diagnostic (Diagnostic (Diagnostic, diagMessage, diagPrimary, diagSecondaries), Label (Label, labMessage, labRange))
import Soma.File (SourceFile (SourceFile, srcContent, srcPath), readSource)
import Soma.Syntax.Kind (Kind (KEof))
import Soma.Syntax.Lexer (Token (tKind, tText), lexAll)
import Soma.Syntax.Parser (parseRoot, runParser)
import Symbolize (unintern)
import System.Directory (doesFileExist, listDirectory)
import System.Environment (lookupEnv)
import System.FilePath (replaceExtension, (</>))
import Test.Hspec (Spec, describe, expectationFailure, it, runIO, shouldBe, shouldNotBe)

fixturesDir :: FilePath
fixturesDir = "compiler/test/fixtures/parser"

sources :: FilePath -> IO [SourceFile]
sources sub = do
    let dir = fixturesDir </> sub
    files <- sort . filter (".soma" `isSuffixOf`) <$> listDirectory dir
    forM files $ \file -> readSource (dir </> file)

parse :: Logger -> SourceFile -> IO (GreenNode, [Diagnostic])
parse logger src = do
    ((root, _), diags) <- runParser logger src mkCache parseRoot
    pure (root, diags)

greenText :: GreenNode -> T.Text
greenText = T.concat . go
  where
    go GreenNode{gnChildren} = concatMap goChild (V.toList gnChildren)
    goChild (GNode n) = go n
    goChild (GToken GreenToken{gtSymbol}) = [unintern gtSymbol]

renderDiag :: T.Text -> Diagnostic -> T.Text
renderDiag src Diagnostic{diagMessage, diagPrimary, diagSecondaries} =
    T.unlines
        $ ("error: " <> diagMessage)
            : map (\l -> "  " <> renderLabel l) (diagPrimary : diagSecondaries)
  where
    renderLabel Label{labRange = Range s e, labMessage} =
        pos s <> "-" <> pos e <> ": " <> labMessage
    pos p = let (r, c) = posRowCol src p in T.pack (show r <> ":" <> show c)

snapshot :: T.Text -> GreenNode -> [Diagnostic] -> T.Text
snapshot src root diags =
    prettyGreen (showKind @Kind) root <> T.concat (map (("\n" <>) . renderDiag src) diags)

golden :: FilePath -> T.Text -> IO ()
golden path actual = do
    update <- maybe False (not . null) <$> lookupEnv "SOMA_UPDATE_GOLDEN"
    exists <- doesFileExist path
    if update || not exists
        then do
            TIO.writeFile path actual
            unless update
                $ expectationFailure ("created " <> path <> "; review it and re-run")
        else do
            expected <- TIO.readFile path
            actual `shouldBe` expected

checkResilient :: Logger -> FilePath -> T.Text -> IO ()
checkResilient logger path input = do
    result <- try @SomeException $ do
        (root, diags) <- parse logger (SourceFile path input)
        _ <- evaluate (length diags)
        pure root
    case result of
        Left err -> expectationFailure ("parser crashed on " <> show input <> ":\n" <> show err)
        Right root ->
            when (greenText root /= input)
                $ expectationFailure ("tree is not lossless for " <> show input)

mutations :: T.Text -> [T.Text]
mutations src = prefixes <> deletions
  where
    prefixes = [T.take n src | n <- [0 .. T.length src - 1]]
    toks = filter ((/= KEof) . tKind) (fst (lexAll src))
    deletions =
        [ T.concat [tText t | (j, t) <- zip [0 :: Int ..] toks, j /= i]
        | i <- [0 .. length toks - 1]
        ]

fixtureSpec :: Logger -> Bool -> SourceFile -> Spec
fixtureSpec logger shouldSucceed src@SourceFile{srcPath, srcContent} = describe srcPath $ do
    it "lexes without diagnostics"
        $ snd (lexAll srcContent) `shouldBe` []

    it "is lossless" $ do
        (root, _) <- parse logger src
        greenText root `shouldBe` srcContent

    if shouldSucceed
        then it "parses without diagnostics" $ do
            (_, diags) <- parse logger src
            map diagMessage diags `shouldBe` []
        else it "reports diagnostics" $ do
            (_, diags) <- parse logger src
            diags `shouldNotBe` []

    it "matches its golden tree" $ do
        (root, diags) <- parse logger src
        golden (replaceExtension srcPath "tree") (snapshot srcContent root diags)

    it "recovers from every prefix and token deletion"
        $ mapM_ (checkResilient logger srcPath) (mutations srcContent)

spec :: Spec
spec = describe "Parser" $ do
    logger <- runIO newLoggerEnv
    oks <- runIO (sources "ok")
    errs <- runIO (sources "err")
    describe "ok" $ forM_ oks (fixtureSpec logger True)
    describe "err" $ forM_ errs (fixtureSpec logger False)
