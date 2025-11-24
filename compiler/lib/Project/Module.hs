module Project.Module where

import Lexing.Lexer (Token)
import Syntax.Tree (Expr)

type ModuleName = String

data ModuleInfo = ModuleInfo
    { moduleName :: ModuleName
    , modulePath :: FilePath
    , moduleContent :: String
    , moduleTokens :: [Token]
    , moduleAst :: Expr
    }
