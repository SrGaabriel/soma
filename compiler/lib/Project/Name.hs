{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NamedFieldPuns #-}

module Project.Name (
    Name (..),
    SyntheticId (..),
    SyntheticKind (..),
    LocalId (..),
    LocalPrefix (..),
    DictId (..),
    DictKind (..),
    mkDictGlobal,
    mkDictStruct,
    Intrinsic (..),
    RuntimeFn (..),
    PrimOp (..),
    Projection (..),
    mkProj0,
    mkProj1,
    projBase,
    isProj0,
    isProj1,
    nameToString,
    nameToLLVM,
    nameOriginal,
    nameModule,
    nameBaseUnique,
    makeSynthetic,
    makeMonomorphized,
    makeInstanceMethod,
    makeDictParam,
    makeRefParam,
    makeDictGlobal,
    isInstanceMethodFor,
    getInstanceMethodType,
    getInstanceMethodBase,
    isInstanceMethod,
    decomposeInstanceMethod,
    nameMatchesAny,
    nameMatchesStdlib,
    isStdlibModule,
    isUserName,
    isSyntheticName,
    isIntrinsicName,
    isLocalName,
    isProjection,
    isErasureName,
    isForkedTaskName,
    mkForkedTaskName,
) where

import Data.Char (isAlphaNum)
import Data.Hashable (Hashable (..))
import Data.List (intercalate)
import GHC.Generics (Generic)
import Project.Unique (Unique (..))
import Typing.Types (Type (..))

data Name
    = NUser !Unique
    | NSynthetic !SyntheticId
    | NIntrinsic !Intrinsic
    | NLocal !LocalId
    | NProjection !Projection
    | NDict !DictId
    deriving (Show, Eq, Ord, Generic)

data DictId = DictId
    { dictModule :: !String
    , dictClass :: !String
    , dictInstanceType :: !Type
    , dictKind :: !DictKind
    }
    deriving (Show, Eq, Ord, Generic)

data DictKind
    = DKGlobal
    | DKStruct
    deriving (Show, Eq, Ord, Generic)

instance Hashable DictId where
    hashWithSalt salt (DictId m c t k) =
        salt `hashWithSalt` m `hashWithSalt` c `hashWithSalt` show t `hashWithSalt` k

instance Hashable DictKind where
    hashWithSalt salt DKGlobal = salt `hashWithSalt` (0 :: Int)
    hashWithSalt salt DKStruct = salt `hashWithSalt` (1 :: Int)

data Intrinsic
    = ILlvm !String
    | IRuntime !RuntimeFn
    | IPrimOp !PrimOp
    deriving (Show, Eq, Ord, Generic)

data RuntimeFn
    = RtPrintInt
    | RtPrintStr
    | RtPanic
    | RtTrace
    | RtAlloc
    | RtFree
    deriving (Show, Eq, Ord, Generic, Enum, Bounded)

data PrimOp
    = PrimAdd
    | PrimSub
    | PrimMul
    | PrimDiv
    | PrimMod
    | PrimEq
    | PrimNe
    | PrimLt
    | PrimLe
    | PrimGt
    | PrimGe
    | PrimAnd
    | PrimOr
    | PrimNot
    | PrimNeg
    deriving (Show, Eq, Ord, Generic, Enum, Bounded)

instance Hashable Intrinsic where
    hashWithSalt salt (ILlvm s) = salt `hashWithSalt` (0 :: Int) `hashWithSalt` s
    hashWithSalt salt (IRuntime r) = salt `hashWithSalt` (1 :: Int) `hashWithSalt` fromEnum r
    hashWithSalt salt (IPrimOp p) = salt `hashWithSalt` (2 :: Int) `hashWithSalt` fromEnum p

instance Hashable RuntimeFn where
    hashWithSalt salt r = salt `hashWithSalt` fromEnum r

instance Hashable PrimOp where
    hashWithSalt salt p = salt `hashWithSalt` fromEnum p

data Projection = Projection
    { projectionBase :: !Name
    , projectionIndex :: !Int
    }
    deriving (Show, Eq, Ord, Generic)

instance Hashable Projection where
    hashWithSalt salt (Projection base idx) =
        salt `hashWithSalt` base `hashWithSalt` idx

instance Hashable Name where
    hashWithSalt salt (NUser u) = salt `hashWithSalt` (0 :: Int) `hashWithSalt` u
    hashWithSalt salt (NSynthetic s) = salt `hashWithSalt` (1 :: Int) `hashWithSalt` s
    hashWithSalt salt (NIntrinsic i) = salt `hashWithSalt` (2 :: Int) `hashWithSalt` i
    hashWithSalt salt (NLocal l) = salt `hashWithSalt` (3 :: Int) `hashWithSalt` l
    hashWithSalt salt (NProjection p) = salt `hashWithSalt` (4 :: Int) `hashWithSalt` p
    hashWithSalt salt (NDict d) = salt `hashWithSalt` (5 :: Int) `hashWithSalt` d

data SyntheticId = SyntheticId
    { synBase :: !Unique
    , synKind :: !SyntheticKind
    , synDiscriminator :: !Int
    }
    deriving (Show, Eq, Ord, Generic)

instance Hashable SyntheticId where
    hashWithSalt salt s =
        salt
            `hashWithSalt` synBase s
            `hashWithSalt` synKind s
            `hashWithSalt` synDiscriminator s

data SyntheticKind
    = SKLiftedLambda
    | SKClosureEnv
    | SKMonomorphized ![Type]
    | SKInstanceMethod !Type
    | SKDictParam !String !Type
    | SKDictGlobal !String !Type
    | SKDictStruct !String
    | SKRefParam !Name
    deriving (Show, Eq, Ord, Generic)

instance Hashable SyntheticKind where
    hashWithSalt salt SKLiftedLambda = salt `hashWithSalt` (0 :: Int)
    hashWithSalt salt SKClosureEnv = salt `hashWithSalt` (1 :: Int)
    hashWithSalt salt (SKMonomorphized tys) = salt `hashWithSalt` (2 :: Int) `hashWithSalt` show tys
    hashWithSalt salt (SKInstanceMethod ty) = salt `hashWithSalt` (3 :: Int) `hashWithSalt` show ty
    hashWithSalt salt (SKDictParam cls ty) = salt `hashWithSalt` (4 :: Int) `hashWithSalt` cls `hashWithSalt` show ty
    hashWithSalt salt (SKDictGlobal cls ty) = salt `hashWithSalt` (5 :: Int) `hashWithSalt` cls `hashWithSalt` show ty
    hashWithSalt salt (SKDictStruct cls) = salt `hashWithSalt` (6 :: Int) `hashWithSalt` cls
    hashWithSalt salt (SKRefParam blk) = salt `hashWithSalt` (7 :: Int) `hashWithSalt` blk

data LocalId = LocalId
    { localPrefix :: !LocalPrefix
    , localIndex :: !Int
    }
    deriving (Show, Eq, Ord, Generic)

instance Hashable LocalId where
    hashWithSalt salt l =
        salt `hashWithSalt` localPrefix l `hashWithSalt` localIndex l

data LocalPrefix
    = LPTemp
    | LPBlock
    | LPParam
    | LPReg
    | LPPatternVar
    | LPClosureSelf
    | LPDictParam
    | LPRefParam
    | LPErasure
    | LPForkedTask
    deriving (Show, Eq, Ord, Generic)

instance Hashable LocalPrefix where
    hashWithSalt salt LPTemp = salt `hashWithSalt` (0 :: Int)
    hashWithSalt salt LPBlock = salt `hashWithSalt` (1 :: Int)
    hashWithSalt salt LPParam = salt `hashWithSalt` (2 :: Int)
    hashWithSalt salt LPReg = salt `hashWithSalt` (3 :: Int)
    hashWithSalt salt LPPatternVar = salt `hashWithSalt` (4 :: Int)
    hashWithSalt salt LPClosureSelf = salt `hashWithSalt` (5 :: Int)
    hashWithSalt salt LPDictParam = salt `hashWithSalt` (6 :: Int)
    hashWithSalt salt LPRefParam = salt `hashWithSalt` (7 :: Int)
    hashWithSalt salt LPErasure = salt `hashWithSalt` (8 :: Int)
    hashWithSalt salt LPForkedTask = salt `hashWithSalt` (9 :: Int)

nameToString :: Name -> String
nameToString (NUser u) = uniqueOriginal u
nameToString (NSynthetic s) = renderSynthetic s
nameToString (NIntrinsic i) = renderIntrinsic i
nameToString (NLocal l) = renderLocal l
nameToString (NProjection p) = renderProjection p
nameToString (NDict d) = renderDict d

nameToLLVM :: Name -> String
nameToLLVM (NUser u) =
    sanitize (uniqueModule u)
        ++ "_"
        ++ sanitize (uniqueOriginal u)
        ++ "_"
        ++ show (uniqueId u)
nameToLLVM (NSynthetic s) = renderSyntheticLLVM s
nameToLLVM (NIntrinsic i) = renderIntrinsicLLVM i
nameToLLVM (NLocal l) = renderLocalLLVM l
nameToLLVM (NProjection p) = renderProjectionLLVM p
nameToLLVM (NDict d) = renderDictLLVM d

nameOriginal :: Name -> String
nameOriginal (NUser u) = uniqueOriginal u
nameOriginal (NSynthetic s) = uniqueOriginal (synBase s)
nameOriginal (NIntrinsic i) = renderIntrinsic i
nameOriginal (NLocal l) = renderLocal l
nameOriginal (NProjection p) = nameOriginal (projectionBase p)
nameOriginal (NDict d) = renderDict d

nameModule :: Name -> Maybe String
nameModule (NUser u) = Just (uniqueModule u)
nameModule (NSynthetic s) = Just (uniqueModule (synBase s))
nameModule (NIntrinsic _) = Nothing
nameModule (NLocal _) = Nothing
nameModule (NProjection p) = nameModule (projectionBase p)
nameModule (NDict d) = Just (dictModule d)

nameBaseUnique :: Name -> Maybe Unique
nameBaseUnique (NUser u) = Just u
nameBaseUnique (NSynthetic s) = Just (synBase s)
nameBaseUnique (NIntrinsic _) = Nothing
nameBaseUnique (NLocal _) = Nothing
nameBaseUnique (NProjection p) = nameBaseUnique (projectionBase p)
nameBaseUnique (NDict _) = Nothing

makeSynthetic :: Name -> SyntheticKind -> Name
makeSynthetic baseName kind = case nameBaseUnique baseName of
    Just u -> NSynthetic (SyntheticId u kind 0)
    Nothing -> error $ "makeSynthetic: cannot create synthetic from " ++ nameToString baseName

makeMonomorphized :: Name -> [Type] -> Name
makeMonomorphized baseName types = makeSynthetic baseName (SKMonomorphized types)

makeInstanceMethod :: Name -> Type -> Name
makeInstanceMethod baseName instanceType = makeSynthetic baseName (SKInstanceMethod instanceType)

makeDictParam :: Name -> String -> Type -> Name
makeDictParam baseName className instanceType =
    makeSynthetic baseName (SKDictParam className instanceType)

makeRefParam :: Name -> Name -> Name
makeRefParam refName blockName = makeSynthetic refName (SKRefParam blockName)

makeDictGlobal :: Name -> String -> Type -> Name
makeDictGlobal baseName className instanceType =
    makeSynthetic baseName (SKDictGlobal className instanceType)

mkDictGlobal :: String -> String -> Type -> Name
mkDictGlobal moduleName className instanceType =
    NDict (DictId moduleName className instanceType DKGlobal)

mkDictStruct :: String -> String -> Type -> Name
mkDictStruct moduleName className instanceType =
    NDict (DictId moduleName className instanceType DKStruct)

isInstanceMethodFor :: Unique -> Name -> Bool
isInstanceMethodFor baseUnique (NSynthetic (SyntheticId base (SKInstanceMethod _) _)) = base == baseUnique
isInstanceMethodFor _ _ = False

getInstanceMethodType :: Name -> Maybe Type
getInstanceMethodType (NSynthetic (SyntheticId _ (SKInstanceMethod ty) _)) = Just ty
getInstanceMethodType _ = Nothing

getInstanceMethodBase :: Name -> Maybe Unique
getInstanceMethodBase (NSynthetic (SyntheticId base (SKInstanceMethod _) _)) = Just base
getInstanceMethodBase _ = Nothing

isInstanceMethod :: Name -> Bool
isInstanceMethod (NSynthetic (SyntheticId _ (SKInstanceMethod _) _)) = True
isInstanceMethod _ = False

decomposeInstanceMethod :: Name -> Maybe (Unique, Type)
decomposeInstanceMethod (NSynthetic (SyntheticId base (SKInstanceMethod ty) _)) = Just (base, ty)
decomposeInstanceMethod _ = Nothing

nameMatchesAny :: [String] -> Name -> Bool
nameMatchesAny patterns name = nameOriginal name `elem` patterns

nameMatchesStdlib :: [String] -> Name -> Bool
nameMatchesStdlib patterns name =
    -- TODO: properly check stdlib module once module naming is finalized
    nameOriginal name `elem` patterns

isStdlibModule :: String -> Bool
isStdlibModule _modName = True

isUserName :: Name -> Bool
isUserName (NUser _) = True
isUserName _ = False

isSyntheticName :: Name -> Bool
isSyntheticName (NSynthetic _) = True
isSyntheticName _ = False

isIntrinsicName :: Name -> Bool
isIntrinsicName (NIntrinsic _) = True
isIntrinsicName _ = False

isLocalName :: Name -> Bool
isLocalName (NLocal _) = True
isLocalName _ = False

isProjection :: Name -> Bool
isProjection (NProjection _) = True
isProjection _ = False

isErasureName :: Name -> Bool
isErasureName (NLocal (LocalId LPErasure _)) = True
isErasureName _ = False

isForkedTaskName :: Name -> Bool
isForkedTaskName (NLocal (LocalId LPForkedTask _)) = True
isForkedTaskName _ = False

mkForkedTaskName :: Name -> Name
mkForkedTaskName (NLocal (LocalId _ n)) = NLocal (LocalId LPForkedTask n)
mkForkedTaskName n = error $ "mkForkedTaskName: expected NLocal, got " ++ show n

mkProj0 :: Name -> Name
mkProj0 base = NProjection (Projection base 0)

mkProj1 :: Name -> Name
mkProj1 base = NProjection (Projection base 1)

projBase :: Name -> Maybe Name
projBase (NProjection p) = Just (projectionBase p)
projBase _ = Nothing

isProj0 :: Name -> Bool
isProj0 (NProjection (Projection _ 0)) = True
isProj0 _ = False

isProj1 :: Name -> Bool
isProj1 (NProjection (Projection _ 1)) = True
isProj1 _ = False

sanitize :: String -> String
sanitize = map (\c -> if isAlphaNum c || c == '_' then c else '_')

renderSynthetic :: SyntheticId -> String
renderSynthetic SyntheticId{synBase, synKind, synDiscriminator} =
    uniqueOriginal synBase
        ++ "$"
        ++ kindSuffix synKind
        ++ (if synDiscriminator > 0 then "$" ++ show synDiscriminator else "")
  where
    kindSuffix SKLiftedLambda = "lambda"
    kindSuffix SKClosureEnv = "env"
    kindSuffix (SKMonomorphized tys) = "mono$" ++ intercalate "_" (map encodeType tys)
    kindSuffix (SKInstanceMethod ty) = "inst$" ++ encodeType ty
    kindSuffix (SKDictParam cls ty) = "dict$" ++ cls ++ "$" ++ encodeType ty
    kindSuffix (SKDictGlobal cls ty) = "Dict$" ++ cls ++ "$" ++ encodeType ty
    kindSuffix (SKDictStruct cls) = "DictStruct$" ++ cls
    kindSuffix (SKRefParam blk) = "refparam$" ++ nameToString blk

renderSyntheticLLVM :: SyntheticId -> String
renderSyntheticLLVM s =
    sanitize (uniqueModule (synBase s))
        ++ "_"
        ++ sanitize (renderSynthetic s)
        ++ "_"
        ++ show (uniqueId (synBase s))
        ++ "_"
        ++ show (synDiscriminator s)

renderIntrinsic :: Intrinsic -> String
renderIntrinsic (ILlvm s) = s
renderIntrinsic (IRuntime r) = renderRuntimeFn r
renderIntrinsic (IPrimOp p) = renderPrimOp p

renderIntrinsicLLVM :: Intrinsic -> String
renderIntrinsicLLVM (ILlvm s) = s -- LLVM intrinsics keep their names
renderIntrinsicLLVM (IRuntime r) = renderRuntimeFn r
renderIntrinsicLLVM (IPrimOp p) = "primop_" ++ primOpName p

renderRuntimeFn :: RuntimeFn -> String
renderRuntimeFn RtPrintInt = "soma_print_int"
renderRuntimeFn RtPrintStr = "soma_print_str"
renderRuntimeFn RtPanic = "soma_panic"
renderRuntimeFn RtTrace = "soma_trace"
renderRuntimeFn RtAlloc = "soma_alloc"
renderRuntimeFn RtFree = "soma_free"

renderPrimOp :: PrimOp -> String
renderPrimOp PrimAdd = "+"
renderPrimOp PrimSub = "-"
renderPrimOp PrimMul = "*"
renderPrimOp PrimDiv = "/"
renderPrimOp PrimMod = "%"
renderPrimOp PrimEq = "=="
renderPrimOp PrimNe = "!="
renderPrimOp PrimLt = "<"
renderPrimOp PrimLe = "<="
renderPrimOp PrimGt = ">"
renderPrimOp PrimGe = ">="
renderPrimOp PrimAnd = "&&"
renderPrimOp PrimOr = "||"
renderPrimOp PrimNot = "!"
renderPrimOp PrimNeg = "neg"

primOpName :: PrimOp -> String
primOpName PrimAdd = "add"
primOpName PrimSub = "sub"
primOpName PrimMul = "mul"
primOpName PrimDiv = "div"
primOpName PrimMod = "mod"
primOpName PrimEq = "eq"
primOpName PrimNe = "ne"
primOpName PrimLt = "lt"
primOpName PrimLe = "le"
primOpName PrimGt = "gt"
primOpName PrimGe = "ge"
primOpName PrimAnd = "and"
primOpName PrimOr = "or"
primOpName PrimNot = "not"
primOpName PrimNeg = "neg"

renderLocal :: LocalId -> String
renderLocal LocalId{localPrefix, localIndex} =
    prefixStr localPrefix ++ show localIndex
  where
    prefixStr LPTemp = "t"
    prefixStr LPBlock = "block"
    prefixStr LPParam = "p"
    prefixStr LPReg = "r"
    prefixStr LPPatternVar = "pv"
    prefixStr LPClosureSelf = "closure_self"
    prefixStr LPDictParam = "dict_param"
    prefixStr LPRefParam = "ref_param"
    prefixStr LPErasure = "era"
    prefixStr LPForkedTask = "fork"

renderLocalLLVM :: LocalId -> String
renderLocalLLVM = renderLocal

renderProjection :: Projection -> String
renderProjection (Projection base idx) =
    nameToString base ++ "." ++ show idx

renderProjectionLLVM :: Projection -> String
renderProjectionLLVM (Projection base idx) =
    nameToLLVM base ++ "_proj" ++ show idx

encodeType :: Type -> String
encodeType (TConstructor tc) = sanitize (show tc)
encodeType (TVar tv) = sanitize (show tv)
encodeType (TSkolem sk) = sanitize (show sk)
encodeType (TApp t1 t2) = encodeType t1 ++ "_" ++ encodeType t2
encodeType (TArrow t1 t2) = encodeType t1 ++ "_to_" ++ encodeType t2
encodeType (TUnresolved s) = sanitize s

renderDict :: DictId -> String
renderDict DictId{dictClass, dictInstanceType, dictKind} =
    case dictKind of
        DKGlobal -> "Dict$" ++ dictClass ++ "$" ++ encodeType dictInstanceType
        DKStruct -> "DictStruct$" ++ dictClass

renderDictLLVM :: DictId -> String
renderDictLLVM d@DictId{dictModule} =
    sanitize dictModule ++ "_" ++ sanitize (renderDict d)
