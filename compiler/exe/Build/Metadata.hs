{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Build.Metadata where

import Data.Aeson
import Data.Aeson.Types (Parser, toJSONKeyText)
import qualified Data.Map as Map
import qualified Data.Text as Text
import GHC.Generics
import Lexing.Position (Span (..))
import Metal.Metadata
import Project.Name (DictId (..), DictKind (..), Intrinsic (..), LocalId (..), LocalPrefix (..), Name (..), PrimOp (..), Projection (..), RuntimeFn (..), SyntheticId (..), SyntheticKind (..))
import Project.Symbols (Symbol (..), SymbolKind (..))
import Project.Unique (Unique (..))
import Typing.Types (Constraint (..), Kind (..), QualifiedType (..), Rigidity (..), SkolemVar (..), TyConstructor (..), TyUnique (..), TyVar (..), Type (..), constraintType, primitiveFromName, primitiveName)

data SerializableConstructorMetadata = SerializableConstructorMetadata
    { scmTypeName :: SerializableName
    , scmTag :: Int
    , scmFields :: [SerializableType]
    }
    deriving (Show, Eq, Generic)

data SerializableName
    = SNUser !SerializableUnique
    | SNSynthetic !SerializableSyntheticId
    | SNIntrinsic !SerializableIntrinsic
    | SNLocal !SerializableLocalId
    | SNProjection !SerializableProjection
    | SNDict !SerializableDictId
    deriving (Show, Read, Eq, Ord, Generic)

data SerializableUnique = SerializableUnique
    { suId :: !Int
    , suModule :: !String
    , suOriginal :: !String
    }
    deriving (Show, Read, Eq, Ord, Generic)

data SerializableSyntheticId = SerializableSyntheticId
    { ssidBase :: !SerializableUnique
    , ssidKind :: !SerializableSyntheticKind
    , ssidDiscriminator :: !Int
    }
    deriving (Show, Read, Eq, Ord, Generic)

data SerializableSyntheticKind
    = SSKLiftedLambda
    | SSKClosureEnv
    | SSKMonomorphized ![SerializableType]
    | SSKInstanceMethod !SerializableType
    | SSKDictParam !String !SerializableType
    | SSKDictGlobal !String !SerializableType
    | SSKDictStruct !String
    | SSKRefParam !SerializableName
    deriving (Show, Read, Eq, Ord, Generic)

data SerializableIntrinsic
    = SILlvm !String
    | SIRuntime !String
    | SIPrimOp !String
    deriving (Show, Read, Eq, Ord, Generic)

data SerializableLocalId = SerializableLocalId
    { slidPrefix :: !String
    , slidIndex :: !Int
    }
    deriving (Show, Read, Eq, Ord, Generic)

data SerializableProjection = SerializableProjection
    { spBase :: !SerializableName
    , spIndex :: !Int
    }
    deriving (Show, Read, Eq, Ord, Generic)

data SerializableDictId = SerializableDictId
    { sdModule :: !String
    , sdClass :: !String
    , sdInstanceType :: !SerializableType
    , sdKind :: !String
    }
    deriving (Show, Read, Eq, Ord, Generic)

data ModuleMetadata = ModuleMetadata
    { metaModuleName :: String
    , metaVersion :: String
    , metaHash :: Maybe String
    , metaSourceFiles :: [FilePath]
    , metaDependencies :: [String]
    }
    deriving (Show, Eq, Generic)

data SerializableTyUnique
    = STyPrim String
    | STyUserDefined SerializableUnique
    deriving (Show, Read, Eq, Ord, Generic)

data SerializableType
    = STyVar String
    | STyCon SerializableTyUnique
    | STyApp SerializableType SerializableType
    | STyArrow SerializableType SerializableType
    | STySkolem String Int
    | STyUnresolved String
    deriving (Show, Read, Eq, Ord, Generic)

data SerializableQualType = SerializableQualType
    { sqtType :: SerializableType
    , sqtConstraints :: [SerializableType]
    , sqtForallVars :: [String]
    }
    deriving (Show, Eq, Generic)

data SerializableSymbolKind
    = SBindingSymbol SerializableQualType
    | SDataConstructorSymbol String
    | STypeSymbol
    | STypeClassSymbol
    | STypeClassMethodSymbol String
    | SInstanceMethodSymbol String String
    | SLetBindingSymbol
    | SLambdaParameterSymbol
    | SComposeBindingSymbol
    | SPatternVariableSymbol
    | SPatternAsSymbol
    | SIntrinsicBindingSymbol
    | SIntrinsicTypeSymbol
    deriving (Show, Eq, Generic)

data SerializableSymbol = SerializableSymbol
    { ssName :: String
    , ssKind :: SerializableSymbolKind
    , ssModule :: String
    , ssPackage :: String
    , ssSpan :: Span
    , ssUnique :: Maybe SerializableUnique
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
    , pmPublicInstances :: [SerializableQualType]
    , pmDependencyGraph :: Map.Map String [String]
    , pmConstructorMetadata :: Map.Map SerializableName SerializableConstructorMetadata
    }
    deriving (Show, Eq, Generic)

instance ToJSON ModuleMetadata where
    toEncoding = genericToEncoding defaultOptions

instance FromJSON ModuleMetadata

instance ToJSON SerializableTyUnique where
    toEncoding = genericToEncoding defaultOptions

instance FromJSON SerializableTyUnique

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

instance ToJSON Span where
    toEncoding = genericToEncoding defaultOptions

instance FromJSON Span

instance ToJSON PublicSymbol where
    toEncoding = genericToEncoding defaultOptions

instance FromJSON PublicSymbol

instance ToJSON SerializableConstructorMetadata where
    toEncoding = genericToEncoding defaultOptions

instance FromJSON SerializableConstructorMetadata

instance ToJSON SerializableName where
    toEncoding = genericToEncoding defaultOptions

instance FromJSON SerializableName

instance ToJSONKey SerializableName where
    toJSONKey = toJSONKeyText serializableNameToText

instance FromJSONKey SerializableName where
    fromJSONKey = FromJSONKeyTextParser textToSerializableName

-- Helper for JSON key serialization
serializableNameToText :: SerializableName -> Text.Text
serializableNameToText sn = Text.pack $ show sn

-- Helper for JSON key deserialization
textToSerializableName :: Text.Text -> Parser SerializableName
textToSerializableName t = case reads (Text.unpack t) of
    [(sn, "")] -> pure sn
    _ -> fail $ "Cannot parse SerializableName: " ++ Text.unpack t

instance ToJSON SerializableUnique where
    toEncoding = genericToEncoding defaultOptions

instance FromJSON SerializableUnique

instance ToJSON SerializableSyntheticId where
    toEncoding = genericToEncoding defaultOptions

instance FromJSON SerializableSyntheticId

instance ToJSON SerializableSyntheticKind where
    toEncoding = genericToEncoding defaultOptions

instance FromJSON SerializableSyntheticKind

instance ToJSON SerializableIntrinsic where
    toEncoding = genericToEncoding defaultOptions

instance FromJSON SerializableIntrinsic

instance ToJSON SerializableLocalId where
    toEncoding = genericToEncoding defaultOptions

instance FromJSON SerializableLocalId

instance ToJSON SerializableProjection where
    toEncoding = genericToEncoding defaultOptions

instance FromJSON SerializableProjection

instance ToJSON SerializableDictId where
    toEncoding = genericToEncoding defaultOptions

instance FromJSON SerializableDictId

instance ToJSON ProjectMetadata where
    toEncoding = genericToEncoding defaultOptions

instance FromJSON ProjectMetadata

tyUniqueToSerializable :: TyUnique -> SerializableTyUnique
tyUniqueToSerializable (TyPrim prim) = STyPrim (primitiveName prim)
tyUniqueToSerializable (TyUserDefined u) = STyUserDefined (uniqueToSerializable u)

serializableToTyUnique :: SerializableTyUnique -> TyUnique
serializableToTyUnique (STyPrim name) = case primitiveFromName name of
    Just prim -> TyPrim prim
    Nothing -> error $ "Unknown primitive type: " ++ name
serializableToTyUnique (STyUserDefined su) = TyUserDefined (serializableToUnique su)

typeToSerializable :: Type -> SerializableType
typeToSerializable (TVar (TypeVar name _)) = STyVar name
typeToSerializable (TConstructor (TypeConstructor tyId _)) = STyCon (tyUniqueToSerializable tyId)
typeToSerializable (TApp t1 t2) = STyApp (typeToSerializable t1) (typeToSerializable t2)
typeToSerializable (TArrow t1 t2) = STyArrow (typeToSerializable t1) (typeToSerializable t2)
typeToSerializable (TSkolem (SkolemVar _ _ uniq name _)) = STySkolem name uniq
typeToSerializable (TUnresolved name) = STyUnresolved name

serializableToType :: SerializableType -> Type
serializableToType (STyVar name) = TVar (TypeVar{tvId = name, tvKind = KindStar})
serializableToType (STyCon stu) = TConstructor (TypeConstructor{tcId = serializableToTyUnique stu, tcKind = KindStar})
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
symbolKindToSerializable TypeSymbol = STypeSymbol
symbolKindToSerializable TypeClassSymbol = STypeClassSymbol
symbolKindToSerializable (TypeClassMethodSymbol cls) = STypeClassMethodSymbol cls
symbolKindToSerializable (InstanceMethodSymbol inst cls) = SInstanceMethodSymbol inst cls
symbolKindToSerializable LetBindingSymbol = SLetBindingSymbol
symbolKindToSerializable LambdaParameterSymbol = SLambdaParameterSymbol
symbolKindToSerializable IntrinsicBindingSymbol = SIntrinsicBindingSymbol
symbolKindToSerializable IntrinsicTypeSymbol = SIntrinsicTypeSymbol
symbolKindToSerializable ComposeBindingSymbol = SComposeBindingSymbol
symbolKindToSerializable PatternVariableSymbol = SPatternVariableSymbol
symbolKindToSerializable PatternAsSymbol = SPatternAsSymbol

serializableToSymbolKind :: SerializableSymbolKind -> SymbolKind
serializableToSymbolKind (SBindingSymbol ty) = BindingSymbol (serializableToQualType ty)
serializableToSymbolKind (SDataConstructorSymbol parent) = DataConstructorSymbol parent
serializableToSymbolKind STypeSymbol = TypeSymbol
serializableToSymbolKind STypeClassSymbol = TypeClassSymbol
serializableToSymbolKind (STypeClassMethodSymbol cls) = TypeClassMethodSymbol cls
serializableToSymbolKind (SInstanceMethodSymbol inst cls) = InstanceMethodSymbol inst cls
serializableToSymbolKind SLetBindingSymbol = LetBindingSymbol
serializableToSymbolKind SLambdaParameterSymbol = LambdaParameterSymbol
serializableToSymbolKind SIntrinsicBindingSymbol = IntrinsicBindingSymbol
serializableToSymbolKind SIntrinsicTypeSymbol = IntrinsicTypeSymbol
serializableToSymbolKind SComposeBindingSymbol = ComposeBindingSymbol
serializableToSymbolKind SPatternVariableSymbol = PatternVariableSymbol
serializableToSymbolKind SPatternAsSymbol = PatternAsSymbol

symbolToSerializable :: Symbol -> SerializableSymbol
symbolToSerializable (ResolvedSymbol unique name kind modName pName sySpan) =
    SerializableSymbol
        { ssName = name
        , ssKind = symbolKindToSerializable kind
        , ssModule = modName
        , ssPackage = pName
        , ssSpan = sySpan
        , ssUnique = fmap uniqueToSerializable unique
        }

serializableToSymbol :: SerializableSymbol -> Symbol
serializableToSymbol (SerializableSymbol name kind modName pName sySpan unique) =
    ResolvedSymbol
        { resolvedSymbolUnique = fmap serializableToUnique unique
        , resolvedSymbolName = name
        , resolvedSymbolKind = serializableToSymbolKind kind
        , resolvedSymbolModule = modName
        , resolvedSymbolPackage = pName
        , resolvedSymbolSpan = sySpan
        }

createPublicSymbol :: Symbol -> QualifiedType -> PublicSymbol
createPublicSymbol sym ty =
    PublicSymbol
        { psSymbol = symbolToSerializable sym
        , psTypeSignature = qualTypeToSerializable ty
        }

extractPublicSymbols :: [(Symbol, QualifiedType)] -> [PublicSymbol]
extractPublicSymbols symList =
    [ createPublicSymbol sym ty
    | (sym, ty) <- symList
    , not (isLocalSymbol sym)
    ]
  where
    isLocalSymbol (ResolvedSymbol _ _ LetBindingSymbol _ _ _) = True
    isLocalSymbol _ = False

createProjectMetadata ::
    String ->
    String ->
    [FilePath] ->
    [(Symbol, QualifiedType)] ->
    [(QualifiedType, Bool)] ->
    Map.Map String [String] ->
    Map.Map SerializableName SerializableConstructorMetadata ->
    ProjectMetadata
createProjectMetadata modName version sourceFiles publicSyms publicInsts depGraph constructors =
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
        , pmPublicInstances = map (qualTypeToSerializable . fst) publicInsts
        , pmDependencyGraph = depGraph
        , pmConstructorMetadata = constructors
        }

projectMetadataPublicSymbols :: ProjectMetadata -> Map.Map Symbol QualifiedType
projectMetadataPublicSymbols pm = Map.fromList (projectMetadataPublicSymbolsList pm)

projectMetadataPublicSymbolsList :: ProjectMetadata -> [(Symbol, QualifiedType)]
projectMetadataPublicSymbolsList pm =
    [ ( serializableToSymbol (psSymbol ps)
      , serializableToQualType (psTypeSignature ps)
      )
    | ps <- pmPublicSymbols pm
    ]

projectMetadataConstructors :: ProjectMetadata -> Map.Map SerializableName SerializableConstructorMetadata
projectMetadataConstructors = pmConstructorMetadata

projectMetadataInstances :: ProjectMetadata -> Map.Map QualifiedType Bool
projectMetadataInstances pm =
    Map.fromList [(serializableToQualType inst, True) | inst <- pmPublicInstances pm]

constructorMetadataToSerializable :: MetallicConstructorMetadata -> SerializableConstructorMetadata
constructorMetadataToSerializable (MetallicConstructorMetadata typeName tag fields) =
    SerializableConstructorMetadata
        { scmTypeName = nameToSerializable typeName
        , scmTag = tag
        , scmFields = map typeToSerializable fields
        }

serializableToConstructorMetadata :: SerializableConstructorMetadata -> MetallicConstructorMetadata
serializableToConstructorMetadata (SerializableConstructorMetadata typeName tag fields) =
    MetallicConstructorMetadata
        { mcmTypeName = serializableToName typeName
        , mcmTag = tag
        , mcmFields = map serializableToType fields
        }

nameToSerializable :: Name -> SerializableName
nameToSerializable (NUser u) = SNUser (uniqueToSerializable u)
nameToSerializable (NSynthetic s) = SNSynthetic (syntheticIdToSerializable s)
nameToSerializable (NIntrinsic i) = SNIntrinsic (intrinsicToSerializable i)
nameToSerializable (NLocal l) = SNLocal (localIdToSerializable l)
nameToSerializable (NProjection p) = SNProjection (projectionToSerializable p)
nameToSerializable (NDict d) = SNDict (dictIdToSerializable d)

serializableToName :: SerializableName -> Name
serializableToName (SNUser u) = NUser (serializableToUnique u)
serializableToName (SNSynthetic s) = NSynthetic (serializableToSyntheticId s)
serializableToName (SNIntrinsic i) = NIntrinsic (serializableToIntrinsic i)
serializableToName (SNLocal l) = NLocal (serializableToLocalId l)
serializableToName (SNProjection p) = NProjection (serializableToProjection p)
serializableToName (SNDict d) = NDict (serializableToDictId d)

uniqueToSerializable :: Unique -> SerializableUnique
uniqueToSerializable u =
    SerializableUnique
        { suId = uniqueId u
        , suModule = uniqueModule u
        , suOriginal = uniqueOriginal u
        }

serializableToUnique :: SerializableUnique -> Unique
serializableToUnique su =
    Unique
        { uniqueId = suId su
        , uniqueModule = suModule su
        , uniqueOriginal = suOriginal su
        }

syntheticIdToSerializable :: SyntheticId -> SerializableSyntheticId
syntheticIdToSerializable s =
    SerializableSyntheticId
        { ssidBase = uniqueToSerializable (synBase s)
        , ssidKind = syntheticKindToSerializable (synKind s)
        , ssidDiscriminator = synDiscriminator s
        }

serializableToSyntheticId :: SerializableSyntheticId -> SyntheticId
serializableToSyntheticId ss =
    SyntheticId
        { synBase = serializableToUnique (ssidBase ss)
        , synKind = serializableToSyntheticKind (ssidKind ss)
        , synDiscriminator = ssidDiscriminator ss
        }

syntheticKindToSerializable :: SyntheticKind -> SerializableSyntheticKind
syntheticKindToSerializable SKLiftedLambda = SSKLiftedLambda
syntheticKindToSerializable SKClosureEnv = SSKClosureEnv
syntheticKindToSerializable (SKMonomorphized tys) = SSKMonomorphized (map typeToSerializable tys)
syntheticKindToSerializable (SKInstanceMethod ty) = SSKInstanceMethod (typeToSerializable ty)
syntheticKindToSerializable (SKDictParam cls ty) = SSKDictParam cls (typeToSerializable ty)
syntheticKindToSerializable (SKDictGlobal cls ty) = SSKDictGlobal cls (typeToSerializable ty)
syntheticKindToSerializable (SKDictStruct cls) = SSKDictStruct cls
syntheticKindToSerializable (SKRefParam n) = SSKRefParam (nameToSerializable n)

serializableToSyntheticKind :: SerializableSyntheticKind -> SyntheticKind
serializableToSyntheticKind SSKLiftedLambda = SKLiftedLambda
serializableToSyntheticKind SSKClosureEnv = SKClosureEnv
serializableToSyntheticKind (SSKMonomorphized tys) = SKMonomorphized (map serializableToType tys)
serializableToSyntheticKind (SSKInstanceMethod ty) = SKInstanceMethod (serializableToType ty)
serializableToSyntheticKind (SSKDictParam cls ty) = SKDictParam cls (serializableToType ty)
serializableToSyntheticKind (SSKDictGlobal cls ty) = SKDictGlobal cls (serializableToType ty)
serializableToSyntheticKind (SSKDictStruct cls) = SKDictStruct cls
serializableToSyntheticKind (SSKRefParam n) = SKRefParam (serializableToName n)

intrinsicToSerializable :: Intrinsic -> SerializableIntrinsic
intrinsicToSerializable (ILlvm s) = SILlvm s
intrinsicToSerializable (IRuntime r) = SIRuntime (runtimeFnToString r)
intrinsicToSerializable (IPrimOp p) = SIPrimOp (primOpToString p)

serializableToIntrinsic :: SerializableIntrinsic -> Intrinsic
serializableToIntrinsic (SILlvm s) = ILlvm s
serializableToIntrinsic (SIRuntime s) = IRuntime (stringToRuntimeFn s)
serializableToIntrinsic (SIPrimOp s) = IPrimOp (stringToPrimOp s)

runtimeFnToString :: RuntimeFn -> String
runtimeFnToString RtPrintInt = "RtPrintInt"
runtimeFnToString RtPrintStr = "RtPrintStr"
runtimeFnToString RtPanic = "RtPanic"
runtimeFnToString RtTrace = "RtTrace"
runtimeFnToString RtAlloc = "RtAlloc"
runtimeFnToString RtFree = "RtFree"

stringToRuntimeFn :: String -> RuntimeFn
stringToRuntimeFn "RtPrintInt" = RtPrintInt
stringToRuntimeFn "RtPrintStr" = RtPrintStr
stringToRuntimeFn "RtPanic" = RtPanic
stringToRuntimeFn "RtTrace" = RtTrace
stringToRuntimeFn "RtAlloc" = RtAlloc
stringToRuntimeFn "RtFree" = RtFree
stringToRuntimeFn s = error ("Unknown RuntimeFn: " ++ s)

primOpToString :: PrimOp -> String
primOpToString PrimAdd = "PrimAdd"
primOpToString PrimSub = "PrimSub"
primOpToString PrimMul = "PrimMul"
primOpToString PrimDiv = "PrimDiv"
primOpToString PrimMod = "PrimMod"
primOpToString PrimEq = "PrimEq"
primOpToString PrimNe = "PrimNe"
primOpToString PrimLt = "PrimLt"
primOpToString PrimLe = "PrimLe"
primOpToString PrimGt = "PrimGt"
primOpToString PrimGe = "PrimGe"
primOpToString PrimAnd = "PrimAnd"
primOpToString PrimOr = "PrimOr"
primOpToString PrimNot = "PrimNot"
primOpToString PrimNeg = "PrimNeg"

stringToPrimOp :: String -> PrimOp
stringToPrimOp "PrimAdd" = PrimAdd
stringToPrimOp "PrimSub" = PrimSub
stringToPrimOp "PrimMul" = PrimMul
stringToPrimOp "PrimDiv" = PrimDiv
stringToPrimOp "PrimMod" = PrimMod
stringToPrimOp "PrimEq" = PrimEq
stringToPrimOp "PrimNe" = PrimNe
stringToPrimOp "PrimLt" = PrimLt
stringToPrimOp "PrimLe" = PrimLe
stringToPrimOp "PrimGt" = PrimGt
stringToPrimOp "PrimGe" = PrimGe
stringToPrimOp "PrimAnd" = PrimAnd
stringToPrimOp "PrimOr" = PrimOr
stringToPrimOp "PrimNot" = PrimNot
stringToPrimOp "PrimNeg" = PrimNeg
stringToPrimOp s = error ("Unknown PrimOp: " ++ s)

localIdToSerializable :: LocalId -> SerializableLocalId
localIdToSerializable l =
    SerializableLocalId
        { slidPrefix = localPrefixToString (localPrefix l)
        , slidIndex = localIndex l
        }

serializableToLocalId :: SerializableLocalId -> LocalId
serializableToLocalId sl =
    LocalId
        { localPrefix = stringToLocalPrefix (slidPrefix sl)
        , localIndex = slidIndex sl
        }

localPrefixToString :: LocalPrefix -> String
localPrefixToString LPTemp = "LPTemp"
localPrefixToString LPBlock = "LPBlock"
localPrefixToString LPParam = "LPParam"
localPrefixToString LPReg = "LPReg"
localPrefixToString LPPatternVar = "LPPatternVar"
localPrefixToString LPClosureSelf = "LPClosureSelf"
localPrefixToString LPDictParam = "LPDictParam"
localPrefixToString LPRefParam = "LPRefParam"
localPrefixToString LPErasure = "LPErasure"
localPrefixToString LPForkedTask = "LPForkedTask"

stringToLocalPrefix :: String -> LocalPrefix
stringToLocalPrefix "LPTemp" = LPTemp
stringToLocalPrefix "LPBlock" = LPBlock
stringToLocalPrefix "LPParam" = LPParam
stringToLocalPrefix "LPReg" = LPReg
stringToLocalPrefix "LPPatternVar" = LPPatternVar
stringToLocalPrefix "LPClosureSelf" = LPClosureSelf
stringToLocalPrefix "LPDictParam" = LPDictParam
stringToLocalPrefix "LPRefParam" = LPRefParam
stringToLocalPrefix "LPErasure" = LPErasure
stringToLocalPrefix "LPForkedTask" = LPForkedTask
stringToLocalPrefix s = error ("Unknown LocalPrefix: " ++ s)

projectionToSerializable :: Projection -> SerializableProjection
projectionToSerializable p =
    SerializableProjection
        { spBase = nameToSerializable (projectionBase p)
        , spIndex = projectionIndex p
        }

serializableToProjection :: SerializableProjection -> Projection
serializableToProjection sp =
    Projection
        { projectionBase = serializableToName (spBase sp)
        , projectionIndex = spIndex sp
        }

dictIdToSerializable :: DictId -> SerializableDictId
dictIdToSerializable d =
    SerializableDictId
        { sdModule = dictModule d
        , sdClass = dictClass d
        , sdInstanceType = typeToSerializable (dictInstanceType d)
        , sdKind = dictKindToString (dictKind d)
        }

serializableToDictId :: SerializableDictId -> DictId
serializableToDictId sd =
    DictId
        { dictModule = sdModule sd
        , dictClass = sdClass sd
        , dictInstanceType = serializableToType (sdInstanceType sd)
        , dictKind = stringToDictKind (sdKind sd)
        }

dictKindToString :: DictKind -> String
dictKindToString DKGlobal = "global"
dictKindToString DKStruct = "struct"

stringToDictKind :: String -> DictKind
stringToDictKind "global" = DKGlobal
stringToDictKind "struct" = DKStruct
stringToDictKind s = error ("Unknown DictKind: " ++ s)
