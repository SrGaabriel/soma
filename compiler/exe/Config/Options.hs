module Config.Options (
    Options (..),
    CheckOptions (..),
    CircuitOptions (..),
    OutputFormat (..),
    CompilationMode (..),
    CommandLineError (..),
    formatError,
    fileExt,
    getInputFile,
    getInputName,
    Command (..),
    commandParser,
    extractCommand,
) where

import Data.List (isPrefixOf)
import Options.Applicative
import System.Environment (getArgs)

fileExt :: String
fileExt = ".soma"

data Command
    = Build Options
    | Check CheckOptions
    | Lex String
    | Parse String
    | Circuit CircuitOptions
    deriving (Show)

data CircuitOptions = CircuitOptions
    { circuitInput :: String
    , circuitLinearize :: Bool
    , circuitGraphFormat :: Bool
    , circuitEval :: Bool
    , circuitToAlloy :: Bool
    , circuitToLlvm :: Bool
    }
    deriving (Show)

data OutputFormat
    = FormatHuman
    | FormatJson
    deriving (Show, Eq)

data CompilationMode
    = ModeStandard
    | ModeGraph
    | ModeHybrid
    deriving (Show, Eq)

data CheckOptions = CheckOptions
    { checkInput :: String
    , checkName :: Maybe String
    , checkDeps :: [(String, String)]
    , checkFormat :: OutputFormat
    }
    deriving (Show)

data Options = Options
    { optionsInput :: String
    , optionsOutput :: Maybe String
    , optionsName :: Maybe String
    , optionsLib :: Bool
    , optionsDeps :: [(String, String)]
    , optionsSkipCircuit :: Bool -- todo: remove
    , optionsMode :: CompilationMode
    , optionsOptimizationLevel :: Maybe Int
    , optionsValidateCircuit :: Bool
    }
    deriving (Show)

commandParser :: Parser Command
commandParser =
    hsubparser
        ( command "lex" (info (Lex <$> inputParser) (progDesc "Run the lexer"))
            <> command "build" (info (Build <$> optionsParser) (progDesc "Build the program"))
            <> command "check" (info (Check <$> checkOptionsParser) (progDesc "Check for errors without building (outputs JSON)"))
            <> command "parse" (info (Parse <$> inputParser) (progDesc "Run the parser"))
            <> command "circuit" (info (Circuit <$> circuitOptionsParser) (progDesc "Lower to Circuit IR (Interaction Nets)"))
        )
        <|> (Build <$> optionsParser)

circuitOptionsParser :: Parser CircuitOptions
circuitOptionsParser =
    CircuitOptions
        <$> inputParser
        <*> switch
            ( long "linearize"
                <> short 'l'
                <> help "Apply linearization pass (insert DUP/ERA nodes)"
            )
        <*> switch
            ( long "graph"
                <> short 'g'
                <> help "Output in graph format (nodes and edges) instead of term format"
            )
        <*> switch
            ( long "eval"
                <> short 'e'
                <> help "Evaluate the Circuit IR using interaction net reduction"
            )
        <*> switch
            ( long "alloy"
                <> short 'a'
                <> help "Lower Circuit IR to Alloy MIR"
            )
        <*> switch
            ( long "llvm"
                <> help "Lower Circuit IR to LLVM IR (implies -l -a)"
            )

checkOptionsParser :: Parser CheckOptions
checkOptionsParser =
    CheckOptions
        <$> inputParser
        <*> optional
            ( strOption
                ( long "name"
                    <> metavar "NAME"
                    <> help "Name of the module"
                )
            )
        <*> many
            ( option
                (eitherReader parseExtern)
                ( long "dep"
                    <> metavar "NAME=PATH"
                    <> help "External dependency (e.g. --dep foo=src/lib/foo.toria)"
                )
            )
        <*> option
            (eitherReader parseFormat)
            ( long "format"
                <> metavar "FORMAT"
                <> value FormatJson
                <> help "Output format: json (default) or human"
            )

parseFormat :: String -> Either String OutputFormat
parseFormat "json" = Right FormatJson
parseFormat "human" = Right FormatHuman
parseFormat s = Left $ "Unknown format: " ++ s ++ ". Use 'json' or 'human'"

inputParser :: Parser String
inputParser =
    argument
        str
        ( metavar "INPUT"
            <> help ("Input source file (" ++ fileExt ++ ")")
        )

getInputFile :: Options -> String
getInputFile opts =
    case break (== '.') (optionsInput opts) of
        (name, ext) | ext == fileExt -> name ++ fileExt
        (name, _) -> name ++ fileExt

getInputName :: Options -> Maybe String
getInputName opts =
    case break (== '.') (optionsInput opts) of
        (name, ext) | ext == fileExt -> Just name
        _ -> Nothing

data CommandLineError
    = NoInputFile
    | InvalidArgument String
    deriving (Show, Eq)

formatError :: CommandLineError -> String
formatError NoInputFile =
    "Error: No input file specified. Please provide a source file with "
        ++ fileExt
        ++ " extension."
formatError (InvalidArgument arg) =
    "Error: Invalid argument: " ++ arg

optionsParser :: Parser Options
optionsParser =
    Options
        <$> inputParser
        <*> optional
            ( strOption
                ( long "out"
                    <> short 'o'
                    <> metavar "OUTPUT"
                    <> help "Output file path"
                )
            )
        <*> optional
            ( strOption
                ( long "name"
                    <> metavar "NAME"
                    <> help "Name of the compiled program or library"
                )
            )
        <*> switch
            ( long "lib"
                <> help "Compile as a Soma library"
            )
        <*> many
            ( option
                (eitherReader parseExtern)
                ( long "dep"
                    <> metavar "NAME=PATH"
                    <> help "Link external library (e.g. --dep foo=src/lib/foo.toria)"
                )
            )
        <*> switch
            ( long "skip-circuit"
                <> help "Do not use Circuit IR pipeline with interaction nets and C runtime"
            )
        <*> option
            (eitherReader parseMode)
            ( long "mode"
                <> short 'm'
                <> metavar "MODE"
                <> value ModeStandard
                <> help "Compilation mode: standard (default), graph (parallel reduction), or hybrid"
            )
        <*> optional
            ( option
                auto
                ( long "opt-level"
                    <> short 'O'
                    <> metavar "LEVEL"
                    <> help "Optimization level (0-3)"
                )
            )
        <*> switch
            ( long "validate"
                <> help "Validate the Circuit IR for correctness"
            )

parseMode :: String -> Either String CompilationMode
parseMode "standard" = Right ModeStandard
parseMode "graph" = Right ModeGraph
parseMode "hybrid" = Right ModeHybrid
parseMode s = Left $ "Unknown mode: " ++ s ++ ". Use 'standard', 'graph', 'lgraph', or 'hybrid'"

parseExtern :: String -> Either String (String, String)
parseExtern s =
    case break (== '=') s of
        (k, '=' : v) | not (null k) && not (null v) -> Right (k, v)
        _ -> Left "Expected format NAME=PATH"

commandInfo :: ParserInfo Command
commandInfo =
    info
        (commandParser <**> helper)
        ( fullDesc
            <> progDesc "Compile and/or run Soma source files"
            <> header "soma-compiler - a compiler for the Soma language"
        )

extractCommand :: IO (Either CommandLineError Command)
extractCommand = do
    args <- getArgs
    if all (isPrefixOf "-") args
        then pure (Left NoInputFile)
        else Right <$> execParser commandInfo
