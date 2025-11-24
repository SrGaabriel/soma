module Project.Symbols where

import Lexing.Position (Span)
import Typing.Types (QualifiedType)

data Symbol = ResolvedSymbol
    { resolvedSymbolName :: String
    , resolvedSymbolKind :: SymbolKind
    , resolvedSymbolModule :: String
    , resolvedSymbolPackage :: String
    , resolvedSymbolSpan :: Span
    }
    deriving (Show, Eq, Ord)

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
