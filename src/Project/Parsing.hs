module Project.Parsing where

import Control.Monad (unless)
import Lexing.Lexer (tokenizeFile)
import Logging.ErrorPrinter (printError)
import Logging.PrettyTrees (TreeShow (treeShow))
import Parsing.Ast (parse)
import Parsing.Errors (ParsingError)
import Project.Module (ModuleInfo (..))
import Syntax.Tree (Expr, exprChildren)

parseModule :: (String, FilePath) -> IO (Either ParsingError ModuleInfo)
parseModule (modName, path) = do
    content <- readFile path
    let (tokens, lexErrors) = tokenizeFile content -- todo rename this fn
    unless (null lexErrors) $ do
        mapM_ (\e -> printError e path content "LEXING") lexErrors
    case parse tokens of
        Left err -> do
            printError err path content "PARSING"
            return $ Left err
        Right ast -> do
            putStrLn "Parsed AST:"
            prettyPrintAst ast
            return $ Right $ ModuleInfo modName path content tokens ast

prettyPrintAst :: Expr -> IO ()
prettyPrintAst root = prettyPrintAst' root 0
  where
    prettyPrintAst' expr indent = do
        putStrLn $ replicate indent ' ' ++ treeShow expr
        mapM_ (\child -> prettyPrintAst' child (indent + 2)) (exprChildren expr)
