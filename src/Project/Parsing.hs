module Project.Parsing where

import Control.Monad (unless)
import qualified Data.ByteString as BS
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Lexing.Lexer (lexCode)
import Logging.ErrorPrinter (printError)
import Logging.PrettyTrees (TreeShow (treeShow))
import Parsing.Ast (parse)
import Parsing.Errors (ParsingError)
import Project.Module (ModuleInfo (..))
import Syntax.Tree (Expr, exprChildren)

-- todo: fix signature
parseModule :: (String, FilePath) -> IO (Either [ParsingError] ModuleInfo)
parseModule (modName, path) = do
    bytes <- BS.readFile path
    let content = TE.decodeUtf8 bytes
    let (tokens, lexErrors) = lexCode content
    case parse tokens of
        Left errors -> do
            let contentStr = T.unpack content
            return $ Left errors
        Right ast -> do
            let contentStr = T.unpack content
            return $ Right $ ModuleInfo modName path contentStr tokens ast

prettyPrintAst :: Expr -> IO ()
prettyPrintAst root = prettyPrintAst' root 0
  where
    prettyPrintAst' expr indent = do
        putStrLn $ replicate indent ' ' ++ treeShow expr
        mapM_ (\child -> prettyPrintAst' child (indent + 2)) (exprChildren expr)
