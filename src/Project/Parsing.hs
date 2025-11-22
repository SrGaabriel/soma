module Project.Parsing where

import qualified Data.ByteString as BS
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Lexing.Lexer (lexCode)
import Logging.Errors (SomeError (SomeError))
import Logging.PrettyTrees (TreeShow (treeShow))
import Parsing.Ast (parse)
import Project.Module (ModuleInfo (..))
import Syntax.Tree (Expr, exprChildren)

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
        Right ast -> do
            case lexErrors of
                [] -> return $ Right $ ModuleInfo modName path contentStr tokens ast
                errs -> return $ Left $ map (\e -> SomeError e path contentStr "LEXING") errs

prettyPrintAst :: Expr -> IO ()
prettyPrintAst root = prettyPrintAst' root 0
  where
    prettyPrintAst' expr indent = do
        putStrLn $ replicate indent ' ' ++ treeShow expr
        mapM_ (\child -> prettyPrintAst' child (indent + 2)) (exprChildren expr)
