{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Project.Metadata where

import Data.Aeson
import qualified Data.Map as Map
import GHC.Generics
import Lexing.Position (Span (..))
import Project.Symbols (Symbol (..), SymbolKind (..))
import Typing.Types (Constraint (..), Kind (..), QualifiedType (..), Rigidity (..), SkolemVar (..), TyConstructor (..), TyVar (..), Type (..), constraintType)

data SerializableConstructorMetadata = SerializableConstructorMetadata
    { scmTypeName :: String
    , scmTag :: Int
    , scmFields :: [SerializableType]
    }
    deriving (Show, Eq, Generic)

data ModuleMetadata = ModuleMetadata
    { metaModuleName :: String
    , metaVersion :: String
    , metaHash :: Maybe String
    , metaSourceFiles :: [FilePath]
    , metaDependencies :: [String]
    }
    deriving (Show, Eq, Generic)

data SerializableType
    = STyVar String
    | STyCon String
    | STyApp SerializableType SerializableType
    | STyArrow SerializableType SerializableType
    | STySkolem String Int
    | STyUnresolved String
    deriving (Show, Eq, Generic)

data SerializableQualType = SerializableQualType
    { sqtType :: SerializableType
    , sqtConstraints :: [SerializableType]
    , sqtForallVars :: [String]
    }
    deriving (Show, Eq, Generic)

data SerializableSymbolKind
    = SBindingSymbol SerializableQualType
    | SDataConstructorSymbol String
    | STypeSymbol Int
    | STypeClassSymbol
    | STypeClassMethodSymbol String
    | SInstanceMethodSymbol String String
    | SLocalVariableSymbol String
    | SIntrinsicBindingSymbol
    | SIntrinsicTypeSymbol
    deriving (Show, Eq, Generic)

data SerializableSymbol = SerializableSymbol
    { ssName :: String
    , ssKind :: SerializableSymbolKind
    , ssModule :: String
    , ssPackage :: String
    }
    deriving (Show, Eq, Generic)

data PublicSymbol = PublicSymbol
    { psSymbol :: SerializableSymbol
    , psTypeSignature :: SerializableQualType
    }
    deriving (Show, Eq, Generic)

data ProjectMetadata = ProjectMetadata
    { pmModuleMetadata :: ModuleMetadata
    , pmPublicSymbols :: [PublicSymbol]
    , pmDependencyGraph :: Map.Map String [String]
    , pmConstructorMetadata :: Map.Map String SerializableConstructorMetadata
    }
    deriving (Show, Eq, Generic)

instance ToJSON ModuleMetadata where
    toEncoding = genericToEncoding defaultOptions

instance FromJSON ModuleMetadata

instance ToJSON SerializableType where
    toEncoding = genericToEncoding defaultOptions

instance FromJSON SerializableType

instance ToJSON SerializableQualType where
    toEncoding = genericToEncoding defaultOptions

instance FromJSON SerializableQualType

instance ToJSON SerializableSymbolKind where
    toEncoding = genericToEncoding defaultOptions

instance FromJSON SerializableSymbolKind

instance ToJSON SerializableSymbol where
    toEncoding = genericToEncoding defaultOptions

instance FromJSON SerializableSymbol

instance ToJSON PublicSymbol where
    toEncoding = genericToEncoding defaultOptions

instance FromJSON PublicSymbol

instance ToJSON SerializableConstructorMetadata where
    toEncoding = genericToEncoding defaultOptions

instance FromJSON SerializableConstructorMetadata

instance ToJSON ProjectMetadata where
    toEncoding = genericToEncoding defaultOptions

instance FromJSON ProjectMetadata

typeToSerializable :: Type -> SerializableType
typeToSerializable (TVar (TypeVar name _)) = STyVar name
typeToSerializable (TConstructor (TypeConstructor name _)) = STyCon name
typeToSerializable (TApp t1 t2) = STyApp (typeToSerializable t1) (typeToSerializable t2)
typeToSerializable (TArrow t1 t2) = STyArrow (typeToSerializable t1) (typeToSerializable t2)
typeToSerializable (TSkolem (SkolemVar _ _ uniq name _)) = STySkolem name uniq
typeToSerializable (TUnresolved name) = STyUnresolved name

serializableToType :: SerializableType -> Type
serializableToType (STyVar name) = TVar (TypeVar{tvId = name, tvKind = KindStar})
serializableToType (STyCon name) = TConstructor (TypeConstructor{tcName = name, tcKind = KindStar})
serializableToType (STyApp t1 t2) = TApp (serializableToType t1) (serializableToType t2)
serializableToType (STyArrow t1 t2) = TArrow (serializableToType t1) (serializableToType t2)
serializableToType (STySkolem name uniq) = TSkolem (SkolemVar{skId = "", skKind = KindStar, skUnique = uniq, skName = name, skRigidity = Rigid})
serializableToType (STyUnresolved name) = TUnresolved name

qualTypeToSerializable :: QualifiedType -> SerializableQualType
qualTypeToSerializable (Forall vars constraints ty) =
    SerializableQualType
        { sqtType = typeToSerializable ty
        , sqtConstraints = map (typeToSerializable . constraintType) constraints
        , sqtForallVars = map tvId vars
        }

serializableToQualType :: SerializableQualType -> QualifiedType
serializableToQualType (SerializableQualType ty constraints forallVars) =
    Forall
        [TypeVar{tvId = name, tvKind = KindStar} | name <- forallVars]
        [Constraint (serializableToType c) | c <- constraints]
        (serializableToType ty)

symbolKindToSerializable :: SymbolKind -> SerializableSymbolKind
symbolKindToSerializable (BindingSymbol ty) = SBindingSymbol (qualTypeToSerializable ty)
symbolKindToSerializable (DataConstructorSymbol parent) = SDataConstructorSymbol parent
symbolKindToSerializable (TypeSymbol arity) = STypeSymbol arity
symbolKindToSerializable TypeClassSymbol = STypeClassSymbol
symbolKindToSerializable (TypeClassMethodSymbol cls) = STypeClassMethodSymbol cls
symbolKindToSerializable (InstanceMethodSymbol inst cls) = SInstanceMethodSymbol inst cls
symbolKindToSerializable (LocalVariableSymbol name) = SLocalVariableSymbol name
symbolKindToSerializable IntrinsicBindingSymbol = SIntrinsicBindingSymbol
symbolKindToSerializable IntrinsicTypeSymbol = SIntrinsicTypeSymbol

serializableToSymbolKind :: SerializableSymbolKind -> SymbolKind
serializableToSymbolKind (SBindingSymbol ty) = BindingSymbol (serializableToQualType ty)
serializableToSymbolKind (SDataConstructorSymbol parent) = DataConstructorSymbol parent
serializableToSymbolKind (STypeSymbol arity) = TypeSymbol arity
serializableToSymbolKind STypeClassSymbol = TypeClassSymbol
serializableToSymbolKind (STypeClassMethodSymbol cls) = TypeClassMethodSymbol cls
serializableToSymbolKind (SInstanceMethodSymbol inst cls) = InstanceMethodSymbol inst cls
serializableToSymbolKind (SLocalVariableSymbol name) = LocalVariableSymbol name
serializableToSymbolKind SIntrinsicBindingSymbol = IntrinsicBindingSymbol
serializableToSymbolKind SIntrinsicTypeSymbol = IntrinsicTypeSymbol

symbolToSerializable :: Symbol -> SerializableSymbol
symbolToSerializable (ResolvedSymbol name kind modName pName _) =
    SerializableSymbol
        { ssName = name
        , ssKind = symbolKindToSerializable kind
        , ssModule = modName
        , ssPackage = pName
        }

serializableToSymbol :: SerializableSymbol -> Symbol
serializableToSymbol (SerializableSymbol name kind modName pName) =
    ResolvedSymbol
        { resolvedSymbolName = name
        , resolvedSymbolKind = serializableToSymbolKind kind
        , resolvedSymbolModule = modName
        , resolvedSymbolPackage = pName
        , resolvedSymbolSpan = Span 0 0
        }

createPublicSymbol :: Symbol -> QualifiedType -> PublicSymbol
createPublicSymbol sym ty =
    PublicSymbol
        { psSymbol = symbolToSerializable sym
        , psTypeSignature = qualTypeToSerializable ty
        }

extractPublicSymbols :: Map.Map Symbol QualifiedType -> [PublicSymbol]
extractPublicSymbols symMap =
    [ createPublicSymbol sym ty
    | (sym, ty) <- Map.toList symMap
    , not (isLocalSymbol sym)
    ]
  where
    isLocalSymbol (ResolvedSymbol _ (LocalVariableSymbol _) _ _ _) = True
    isLocalSymbol _ = False

createProjectMetadata ::
    String ->
    String ->
    [FilePath] ->
    Map.Map Symbol QualifiedType ->
    Map.Map String [String] ->
    Map.Map String SerializableConstructorMetadata ->
    ProjectMetadata
createProjectMetadata modName version sourceFiles publicSyms depGraph constructors =
    ProjectMetadata
        { pmModuleMetadata =
            ModuleMetadata
                { metaModuleName = modName
                , metaVersion = version
                , metaHash = Nothing
                , metaSourceFiles = sourceFiles
                , metaDependencies = Map.keys depGraph
                }
        , pmPublicSymbols = extractPublicSymbols publicSyms
        , pmDependencyGraph = depGraph
        , pmConstructorMetadata = constructors
        }

projectMetadataPublicSymbols :: ProjectMetadata -> Map.Map Symbol QualifiedType
projectMetadataPublicSymbols pm =
    Map.fromList
        [ ( serializableToSymbol (psSymbol ps)
          , serializableToQualType (psTypeSignature ps)
          )
        | ps <- pmPublicSymbols pm
        ]

projectMetadataConstructors :: ProjectMetadata -> Map.Map String SerializableConstructorMetadata
projectMetadataConstructors = pmConstructorMetadata
