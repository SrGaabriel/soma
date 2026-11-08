module Main (main) where

import Blammo.Logging.Setup (newLoggerEnv)
import Control.Monad (unless)
import Data.Text.IO qualified as TIO
import Maple.Ast (cast)
import Maple.Cache (mkCache)
import Maple.Position (TreeId (TreeId))
import Maple.Red (materializeRoot)
import Soma.Diagnostic (reportAll)
import Soma.Elaborator (elaborateFile)
import Soma.File (SourceFile (srcId), mkFiles, readSource)
import Soma.Print (Pretty (pretty))
import Soma.Syntax.Parser (parseRoot, runParser)
import Soma.Syntax.Tree (Root)
import Somac.Cli (Cli (Elaborate), runCli)
import System.Exit (exitFailure)

main :: IO ()
main = do
    cli <- runCli
    case cli of
        Elaborate path -> elaborate path
        _ -> print cli

elaborate :: FilePath -> IO ()
elaborate path = do
    src <- readSource (TreeId 0) path
    let files = mkFiles [src]
    logger <- newLoggerEnv
    ((green, _), parseDiags) <- runParser logger src mkCache parseRoot
    reportAll files parseDiags
    case cast @Root (materializeRoot (srcId src) green) of
        Nothing -> putStrLn "internal error: parser did not produce a root node" >> exitFailure
        Just root -> do
            (elaborated, elabDiags) <- elaborateFile src root
            reportAll files elabDiags
            TIO.putStrLn (pretty elaborated)
            unless (null parseDiags && null elabDiags) exitFailure
