module Project.Parsing where
import Project.Name (Name)
import Project.Module (ModuleInfo (..))
import Lexing.Lexer (tokenizeFile)
import Logging.ErrorPrinter (printError)
import Parsing.Ast (parse)
import Control.Monad (unless)

parseModule :: (Name, FilePath) -> IO (Either () ModuleInfo)
parseModule (modName, path) = do
    content <- readFile path
    let (tokens, lexErrors) = tokenizeFile content
    unless (null lexErrors) $ do
        mapM_ (\e -> printError e path content "LEXING") lexErrors
    case parse tokens of
        Left err -> do
            printError err path content "PARSING"
            return $ Left ()
        Right ast ->
            return $ Right $ ModuleInfo modName path content tokens ast