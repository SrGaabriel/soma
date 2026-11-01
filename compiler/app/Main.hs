module Main (main) where

import Blammo.Logging.Setup (newLoggerEnv)
import Maple.Ast (cast)
import Maple.Cache (mkCache)
import Maple.Red (materializeRoot)
import Soma.Diagnostic (reportAll)
import Data.Text.IO qualified as TIO
import Soma.Elaborator (elaborateFile)
import Soma.Print (Pretty (pretty))
import Soma.File (readSource)
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
    src <- readSource path
    logger <- newLoggerEnv
    ((green, _), parseDiags) <- runParser logger src mkCache parseRoot
    reportAll parseDiags
    case cast @Root (materializeRoot green) of
        Nothing -> putStrLn "internal error: parser did not produce a root node" >> exitFailure
        Just root -> do
            (elaborated, elabDiags) <- elaborateFile src root
            reportAll elabDiags
            TIO.putStrLn (pretty elaborated)
            if null parseDiags && null elabDiags then pure () else exitFailure
