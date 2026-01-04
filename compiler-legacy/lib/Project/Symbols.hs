module Project.Symbols (
    Symbol (..),
    SymbolKind (..),
    symbolUnique,
    symbolName,
) where

import Lexing.Position (Span)
import Project.Unique (Unique)
import Typing.Types (QualifiedType)

data Symbol = ResolvedSymbol
    { resolvedSymbolUnique :: !(Maybe Unique)
    , resolvedSymbolName :: !String
    , resolvedSymbolKind :: !SymbolKind
    , resolvedSymbolModule :: !String
    , resolvedSymbolPackage :: !String
    , resolvedSymbolSpan :: !Span
    }
    deriving (Show)

instance Eq Symbol where
    s1 == s2 = case (resolvedSymbolUnique s1, resolvedSymbolUnique s2) of
        (Just u1, Just u2) -> u1 == u2
        _ ->
            resolvedSymbolName s1 == resolvedSymbolName s2
                && resolvedSymbolModule s1 == resolvedSymbolModule s2

instance Ord Symbol where
    compare s1 s2 = case (resolvedSymbolUnique s1, resolvedSymbolUnique s2) of
        (Just u1, Just u2) -> compare u1 u2
        _ -> case compare (resolvedSymbolModule s1) (resolvedSymbolModule s2) of
            EQ -> compare (resolvedSymbolName s1) (resolvedSymbolName s2)
            other -> other

symbolUnique :: Symbol -> Maybe Unique
symbolUnique = resolvedSymbolUnique

symbolName :: Symbol -> String
symbolName = resolvedSymbolName

data SymbolKind
    = BindingSymbol {bindingType :: QualifiedType}
    | DataConstructorSymbol {constructorParent :: String}
    | TypeSymbol
    | TypeClassSymbol
    | TypeClassMethodSymbol {methodClass :: String}
    | InstanceMethodSymbol {methodInstance :: String, methodClass :: String}
    | LetBindingSymbol
    | LambdaParameterSymbol
    | PatternVariableSymbol
    | PatternAsSymbol
    | ComposeBindingSymbol
    | IntrinsicBindingSymbol
    | IntrinsicTypeSymbol
    deriving (Show, Eq, Ord)
