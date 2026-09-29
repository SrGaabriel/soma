module Somac.Cli where

import Options.Applicative (Parser, execParser, fullDesc, help, helper, info, metavar, strArgument)

data Cli = Cli
    { target :: String
    }
    deriving (Show)

cli :: Parser Cli
cli =
    Cli
        <$> strArgument
            (metavar "TARGET" <> help "The target of the compilation")

runCli :: IO Cli
runCli = execParser (info (helper <*> cli) fullDesc)
