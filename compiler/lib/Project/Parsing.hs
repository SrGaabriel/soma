module Project.Parsing where

import qualified Data.ByteString as BS
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Format.Errors (SomeError (SomeError))
import Lexing.Lexer (lexCode)
import Parsing.Ast (parse)
import Project.Module (ModuleInfo (..))

parseModule :: String -> FilePath -> IO (Either [SomeError] ModuleInfo)
parseModule modName path = do
    bytes <- BS.readFile path
    let content = TE.decodeUtf8 bytes
    let (tokens, lexErrors) = lexCode content
    let contentStr = T.unpack content
    case parse tokens of
        Left parsingErrors -> do
            let convertedLexErrors = map (\e -> SomeError e path contentStr "LEXING") lexErrors
                convertedParsingErrors = map (\e -> SomeError e path contentStr "LEXING") parsingErrors
                allErrors = convertedLexErrors ++ convertedParsingErrors
            return $ Left allErrors
        Right (parseErrors, ast) -> do
            let allErrors =
                    map (\e -> SomeError e path contentStr "LEXING") lexErrors
                        ++ map (\e -> SomeError e path contentStr "PARSING") parseErrors
            if null allErrors
                then return $ Right $ ModuleInfo modName path contentStr tokens ast
                else return $ Left allErrors
