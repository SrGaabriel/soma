module Project.Extracts where
import Syntax.Tree (Expr(..), exprChildren)
import Typing.Types (QualifiedType)
import qualified Data.Map.Strict as Map
import Project.Symbols (Symbol (resolvedSymbolName))

extractSymbolImports :: Expr -> [(String, [String])]
extractSymbolImports (ExprRoot cs) = concatMap extractSymbolImports cs
extractSymbolImports (ExprImport name elements _) =
    [(name, elements)]
extractSymbolImports e = concatMap extractSymbolImports (exprChildren e)

filterSymbolsByNames :: [String] -> Map.Map Symbol QualifiedType -> Map.Map Symbol QualifiedType
filterSymbolsByNames names =
    Map.filterWithKey (\sym _ -> resolvedSymbolName sym `elem` names)
