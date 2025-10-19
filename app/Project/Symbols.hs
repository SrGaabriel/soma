module Project.Symbols where

import Lexing.Position (Span)

data Symbol = ResolvedSymbol
    { resolvedSymbolName :: String
    , resolvedSymbolKind :: SymbolKind
    , resolvedSymbolModule :: String
    , resolvedSymbolSpan :: Span
    }
    deriving (Show, Eq, Ord)

data SymbolKind
    = BindingSymbol
    | DataConstructorSymbol {constructorParent :: String}
    | TypeSymbol {typeArity :: Int}
    | TypeClassSymbol
    | TypeClassMethodSymbol {methodClass :: String}
    | InstanceMethodSymbol {methodInstance :: String, methodClass :: String}
    | LocalVariableSymbol
    | IntrinsicBindingSymbol
    | IntrinsicTypeSymbol
    deriving (Show, Eq, Ord)
