module Somac.Cli where

import Options.Applicative (Parser, command, execParser, fullDesc, help, helper, hsubparser, info, metavar, progDesc, strArgument, (<|>))

data Cli
    = Compile String
    | Lex String
    | Parse String
    | Elaborate String
    deriving (Show)

targetArgument :: String -> Parser String
targetArgument desc = strArgument (metavar "TARGET" <> help desc)

cli :: Parser Cli
cli =
    hsubparser
        ( command
            "lex"
            (info (Lex <$> targetArgument "The target to lex") (progDesc "Print the tokens of TARGET"))
            <> command
                "elaborate"
                (info (Elaborate <$> targetArgument "The target to elaborate") (progDesc "Elaborate TARGET and report diagnostics"))
        )
        <|> Compile
        <$> targetArgument "The target of the compilation"

runCli :: IO Cli
runCli = execParser (info (helper <*> cli) fullDesc)
