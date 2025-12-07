{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NamedFieldPuns #-}

module Project.Name (
    -- * Core Name Type
    Name (..),

    -- * Synthetic Names
    SyntheticId (..),
    SyntheticKind (..),

    -- * Local Names
    LocalId (..),
    LocalPrefix (..),

    -- * Dictionary Names
    DictId (..),
    DictKind (..),
    mkDictGlobal,
    mkDictStruct,

    -- * Intrinsic Names
    Intrinsic (..),
    RuntimeFn (..),
    PrimOp (..),

    -- * Projection Names (for DUP nodes in Circuit IR)
    Projection (..),
    mkProj0,
    mkProj1,
    projBase,
    isProj0,
    isProj1,

    -- * Name Operations
    nameToString,
    nameToLLVM,
    nameOriginal,
    nameModule,
    nameBaseUnique,

    -- * Creating Synthetic Names
    makeSynthetic,
    makeMonomorphized,
    makeInstanceMethod,
    makeDictParam,
    makeRefParam,
    makeDictGlobal,

    -- * Name Analysis
    isInstanceMethodFor,
    getInstanceMethodType,
    getInstanceMethodBase,
    isInstanceMethod,
    decomposeInstanceMethod,
    nameMatchesAny,
    nameMatchesStdlib,
    isStdlibModule,

    -- * Predicates
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

{- | A Name is the identity of any named entity in the compiler.
This replaces all uses of `type Name = String` throughout the pipeline.
-}
data Name
    = -- | User-defined binding or type (has a Unique from Resolver)
      NUser !Unique
    | -- | Compiler-generated name (lambdas, dictionaries, specializations)
      NSynthetic !SyntheticId
    | -- | Built-in intrinsic (LLVM intrinsics, runtime functions, primitive ops)
      NIntrinsic !Intrinsic
    | -- | Block-local name (temps, blocks, params) - no global uniqueness needed
      NLocal !LocalId
    | -- | Projection from a DUP node (used in Circuit IR linearization)
      NProjection !Projection
    | -- | Dictionary-related name (global dict instances, doesn't derive from user binding)
      NDict !DictId
    deriving (Show, Eq, Ord, Generic)

-- | Identity for dictionary-related names
data DictId = DictId
    { dictModule :: !String
    -- ^ Module where this dictionary is defined
    , dictClass :: !String
    -- ^ Type class name (e.g., "Show")
    , dictInstanceType :: !Type
    -- ^ The concrete type this dictionary is for (e.g., Int)
    , dictKind :: !DictKind
    -- ^ What kind of dictionary name this is
    }
    deriving (Show, Eq, Ord, Generic)

-- | What kind of dictionary name
data DictKind
    = -- | Global dictionary instance (the actual dict struct)
      DKGlobal
    | -- | Dictionary struct type name
      DKStruct
    deriving (Show, Eq, Ord, Generic)

instance Hashable DictId where
    hashWithSalt salt (DictId m c t k) =
        salt `hashWithSalt` m `hashWithSalt` c `hashWithSalt` show t `hashWithSalt` k

instance Hashable DictKind where
    hashWithSalt salt DKGlobal = salt `hashWithSalt` (0 :: Int)
    hashWithSalt salt DKStruct = salt `hashWithSalt` (1 :: Int)

-- | Built-in intrinsic - only for things that are truly built into the compiler/runtime
data Intrinsic
    = -- | LLVM intrinsic function (e.g., "llvm.sadd.with.overflow.i64")
      ILlvm !String
    | -- | Soma runtime function
      IRuntime !RuntimeFn
    | -- | Primitive arithmetic/comparison operator
      IPrimOp !PrimOp
    deriving (Show, Eq, Ord, Generic)

-- | Runtime functions provided by the Soma runtime
data RuntimeFn
    = RtPrintInt
    | RtPrintStr
    | RtPanic
    | RtTrace
    | RtAlloc
    | RtFree
    deriving (Show, Eq, Ord, Generic, Enum, Bounded)

-- | Primitive operations that map directly to LLVM instructions
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

-- | A projection from a DUP binding - either the first or second copy
data Projection = Projection
    { projectionBase :: !Name
    -- ^ The DUP binding this projects from
    , projectionIndex :: !Int
    -- ^ 0 for first projection, 1 for second
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

-- | Identity for compiler-generated names
data SyntheticId = SyntheticId
    { synBase :: !Unique
    -- ^ The original user-defined entity this derives from
    , synKind :: !SyntheticKind
    -- ^ What kind of synthetic name this is
    , synDiscriminator :: !Int
    -- ^ For disambiguation when multiple synthetics of same kind exist
    }
    deriving (Show, Eq, Ord, Generic)

instance Hashable SyntheticId where
    hashWithSalt salt s =
        salt
            `hashWithSalt` synBase s
            `hashWithSalt` synKind s
            `hashWithSalt` synDiscriminator s

-- | What kind of synthetic name is this?
data SyntheticKind
    = -- | Lambda lifted to top level
      SKLiftedLambda
    | -- | Closure environment struct
      SKClosureEnv
    | -- | Monomorphic specialization for specific types
      SKMonomorphized ![Type]
    | -- | Instance method for a specific type
      SKInstanceMethod !Type
    | -- | Dictionary parameter (class name, instance type)
      SKDictParam !String !Type
    | -- | Global dictionary instance (class name, instance type)
      SKDictGlobal !String !Type
    | -- | Dictionary struct type (class name)
      SKDictStruct !String
    | -- | Promoted ref parameter (block name where this param appears)
      SKRefParam !Name
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

-- | Identity for block-local names (don't need global uniqueness)
data LocalId = LocalId
    { localPrefix :: !LocalPrefix
    , localIndex :: !Int
    }
    deriving (Show, Eq, Ord, Generic)

instance Hashable LocalId where
    hashWithSalt salt l =
        salt `hashWithSalt` localPrefix l `hashWithSalt` localIndex l

-- | Prefix indicating what kind of local name
data LocalPrefix
    = -- | Temporary variable
      LPTemp
    | -- | Basic block
      LPBlock
    | -- | Function parameter
      LPParam
    | -- | LLVM register
      LPReg
    | -- | Pattern variable
      LPPatternVar
    | -- | Closure self parameter (the closure passed to its own lifted function)
      LPClosureSelf
    | -- | Dictionary parameter (for type class constraints)
      LPDictParam
    | -- | Promoted ref parameter (for PromoteRefs pass)
      LPRefParam
    | -- | Erasure name (unused field that should be dropped)
      LPErasure
    | -- | Forked task handle
      LPForkedTask
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

-- | Convert Name to human-readable string (for errors, debugging)
nameToString :: Name -> String
nameToString (NUser u) = uniqueOriginal u
nameToString (NSynthetic s) = renderSynthetic s
nameToString (NIntrinsic i) = renderIntrinsic i
nameToString (NLocal l) = renderLocal l
nameToString (NProjection p) = renderProjection p
nameToString (NDict d) = renderDict d

-- | Convert Name to LLVM-safe identifier
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

-- | Get original name for error messages
nameOriginal :: Name -> String
nameOriginal (NUser u) = uniqueOriginal u
nameOriginal (NSynthetic s) = uniqueOriginal (synBase s)
nameOriginal (NIntrinsic i) = renderIntrinsic i
nameOriginal (NLocal l) = renderLocal l
nameOriginal (NProjection p) = nameOriginal (projectionBase p)
nameOriginal (NDict d) = renderDict d

-- | Get module name if applicable
nameModule :: Name -> Maybe String
nameModule (NUser u) = Just (uniqueModule u)
nameModule (NSynthetic s) = Just (uniqueModule (synBase s))
nameModule (NIntrinsic _) = Nothing
nameModule (NLocal _) = Nothing
nameModule (NProjection p) = nameModule (projectionBase p)
nameModule (NDict d) = Just (dictModule d)

-- | Extract the base Unique from a Name (for creating synthetic derivatives)
-- Returns Nothing for intrinsics, locals, and dicts which have no associated Unique.
nameBaseUnique :: Name -> Maybe Unique
nameBaseUnique (NUser u) = Just u
nameBaseUnique (NSynthetic s) = Just (synBase s)
nameBaseUnique (NIntrinsic _) = Nothing
nameBaseUnique (NLocal _) = Nothing
nameBaseUnique (NProjection p) = nameBaseUnique (projectionBase p)
nameBaseUnique (NDict _) = Nothing

--------------------------------------------------------------------------------
-- Creating Synthetic Names
--------------------------------------------------------------------------------

-- | Create a synthetic name from a base name with a specific kind
-- The discriminator defaults to 0; use this for unique synthetics.
makeSynthetic :: Name -> SyntheticKind -> Name
makeSynthetic baseName kind = case nameBaseUnique baseName of
    Just u -> NSynthetic (SyntheticId u kind 0)
    Nothing -> error $ "makeSynthetic: cannot create synthetic from " ++ nameToString baseName

-- | Create a monomorphized specialization of a function
makeMonomorphized :: Name -> [Type] -> Name
makeMonomorphized baseName types = makeSynthetic baseName (SKMonomorphized types)

-- | Create an instance method name for a specific type
makeInstanceMethod :: Name -> Type -> Name
makeInstanceMethod baseName instanceType = makeSynthetic baseName (SKInstanceMethod instanceType)

-- | Create a dictionary parameter name
makeDictParam :: Name -> String -> Type -> Name
makeDictParam baseName className instanceType =
    makeSynthetic baseName (SKDictParam className instanceType)

-- | Create a promoted ref parameter name
-- Takes the ref name (to derive from) and the block name (to distinguish params in different blocks)
makeRefParam :: Name -> Name -> Name
makeRefParam refName blockName = makeSynthetic refName (SKRefParam blockName)

-- | Create a global dictionary instance name (from a base name)
makeDictGlobal :: Name -> String -> Type -> Name
makeDictGlobal baseName className instanceType =
    makeSynthetic baseName (SKDictGlobal className instanceType)

-- | Create a global dictionary instance name (standalone, no base)
mkDictGlobal :: String -> String -> Type -> Name
mkDictGlobal moduleName className instanceType =
    NDict (DictId moduleName className instanceType DKGlobal)

-- | Create a dictionary struct type name
mkDictStruct :: String -> String -> Type -> Name
mkDictStruct moduleName className instanceType =
    NDict (DictId moduleName className instanceType DKStruct)

--------------------------------------------------------------------------------
-- Name Analysis
--------------------------------------------------------------------------------

-- | Check if a name is an instance method for a given base unique
-- Returns True if this is an SKInstanceMethod synthetic derived from the given unique
isInstanceMethodFor :: Unique -> Name -> Bool
isInstanceMethodFor baseUnique (NSynthetic (SyntheticId base (SKInstanceMethod _) _)) = base == baseUnique
isInstanceMethodFor _ _ = False

-- | Get the instance type from an instance method name
-- Returns Nothing if this is not an instance method
getInstanceMethodType :: Name -> Maybe Type
getInstanceMethodType (NSynthetic (SyntheticId _ (SKInstanceMethod ty) _)) = Just ty
getInstanceMethodType _ = Nothing

-- | Get the base unique from an instance method name
-- Returns Nothing if this is not an instance method
getInstanceMethodBase :: Name -> Maybe Unique
getInstanceMethodBase (NSynthetic (SyntheticId base (SKInstanceMethod _) _)) = Just base
getInstanceMethodBase _ = Nothing

-- | Check if a name is an instance method (any instance)
isInstanceMethod :: Name -> Bool
isInstanceMethod (NSynthetic (SyntheticId _ (SKInstanceMethod _) _)) = True
isInstanceMethod _ = False

-- | Decompose an instance method name into (baseUnique, instanceType)
-- Returns Nothing if not an instance method
decomposeInstanceMethod :: Name -> Maybe (Unique, Type)
decomposeInstanceMethod (NSynthetic (SyntheticId base (SKInstanceMethod ty) _)) = Just (base, ty)
decomposeInstanceMethod _ = Nothing

-- | Check if a name matches any of the given original name patterns
-- Used for compiler passes that need to recognize well-known library functions
nameMatchesAny :: [String] -> Name -> Bool
nameMatchesAny patterns name = nameOriginal name `elem` patterns

-- | Check if a name matches any of the given patterns AND is from the stdlib
-- This is the preferred check for recognizing well-known stdlib functions
nameMatchesStdlib :: [String] -> Name -> Bool
nameMatchesStdlib patterns name =
    -- TODO: properly check stdlib module once module naming is finalized
    nameOriginal name `elem` patterns

-- | Check if a module name belongs to the standard library
-- TODO: implement proper stdlib module detection
isStdlibModule :: String -> Bool
isStdlibModule _modName = True

-- | Check if this is a user-defined name
isUserName :: Name -> Bool
isUserName (NUser _) = True
isUserName _ = False

-- | Check if this is a synthetic (compiler-generated) name
isSyntheticName :: Name -> Bool
isSyntheticName (NSynthetic _) = True
isSyntheticName _ = False

-- | Check if this is an intrinsic name
isIntrinsicName :: Name -> Bool
isIntrinsicName (NIntrinsic _) = True
isIntrinsicName _ = False

-- | Check if this is a local name
isLocalName :: Name -> Bool
isLocalName (NLocal _) = True
isLocalName _ = False

-- | Check if this is a projection name
isProjection :: Name -> Bool
isProjection (NProjection _) = True
isProjection _ = False

-- | Check if a name is an erasure name (unused field that should be dropped)
isErasureName :: Name -> Bool
isErasureName (NLocal (LocalId LPErasure _)) = True
isErasureName _ = False

-- | Check if a name is a forked task handle
isForkedTaskName :: Name -> Bool
isForkedTaskName (NLocal (LocalId LPForkedTask _)) = True
isForkedTaskName _ = False

-- | Create a forked task name from a task name
-- The forked task name shares the same ID but uses LPForkedTask prefix
mkForkedTaskName :: Name -> Name
mkForkedTaskName (NLocal (LocalId _ n)) = NLocal (LocalId LPForkedTask n)
mkForkedTaskName n = error $ "mkForkedTaskName: expected NLocal, got " ++ show n

--------------------------------------------------------------------------------
-- Projection helpers
--------------------------------------------------------------------------------

-- | Create a first projection (proj0) from a DUP binding
mkProj0 :: Name -> Name
mkProj0 base = NProjection (Projection base 0)

-- | Create a second projection (proj1) from a DUP binding
mkProj1 :: Name -> Name
mkProj1 base = NProjection (Projection base 1)

-- | Get the base name from a projection (returns Nothing if not a projection)
projBase :: Name -> Maybe Name
projBase (NProjection p) = Just (projectionBase p)
projBase _ = Nothing

-- | Check if a name is a first projection (proj0)
isProj0 :: Name -> Bool
isProj0 (NProjection (Projection _ 0)) = True
isProj0 _ = False

-- | Check if a name is a second projection (proj1)
isProj1 :: Name -> Bool
isProj1 (NProjection (Projection _ 1)) = True
isProj1 _ = False

--------------------------------------------------------------------------------
-- Internal helpers
--------------------------------------------------------------------------------

-- | Sanitize a string for use in LLVM identifiers
sanitize :: String -> String
sanitize = map (\c -> if isAlphaNum c || c == '_' then c else '_')

-- | Render synthetic name for display
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

-- | Render synthetic name for LLVM
renderSyntheticLLVM :: SyntheticId -> String
renderSyntheticLLVM s =
    sanitize (uniqueModule (synBase s))
        ++ "_"
        ++ sanitize (renderSynthetic s)
        ++ "_"
        ++ show (uniqueId (synBase s))
        ++ "_"
        ++ show (synDiscriminator s)

-- | Render intrinsic name for display
renderIntrinsic :: Intrinsic -> String
renderIntrinsic (ILlvm s) = s
renderIntrinsic (IRuntime r) = renderRuntimeFn r
renderIntrinsic (IPrimOp p) = renderPrimOp p

-- | Render intrinsic name for LLVM
renderIntrinsicLLVM :: Intrinsic -> String
renderIntrinsicLLVM (ILlvm s) = s  -- LLVM intrinsics keep their names
renderIntrinsicLLVM (IRuntime r) = renderRuntimeFn r
renderIntrinsicLLVM (IPrimOp p) = "primop_" ++ primOpName p

-- | Render runtime function name
renderRuntimeFn :: RuntimeFn -> String
renderRuntimeFn RtPrintInt = "soma_print_int"
renderRuntimeFn RtPrintStr = "soma_print_str"
renderRuntimeFn RtPanic = "soma_panic"
renderRuntimeFn RtTrace = "soma_trace"
renderRuntimeFn RtAlloc = "soma_alloc"
renderRuntimeFn RtFree = "soma_free"

-- | Render primitive operation for display
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

-- | Primitive operation name for LLVM (without special characters)
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

-- | Render local name for display
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

-- | Render local name for LLVM (already LLVM-safe)
renderLocalLLVM :: LocalId -> String
renderLocalLLVM = renderLocal

-- | Render projection name for display
renderProjection :: Projection -> String
renderProjection (Projection base idx) =
    nameToString base ++ "." ++ show idx

-- | Render projection name for LLVM
renderProjectionLLVM :: Projection -> String
renderProjectionLLVM (Projection base idx) =
    nameToLLVM base ++ "_proj" ++ show idx

-- | Encode a type as a string for use in synthetic names
encodeType :: Type -> String
encodeType (TConstructor tc) = sanitize (show tc)
encodeType (TVar tv) = sanitize (show tv)
encodeType (TSkolem sk) = sanitize (show sk)
encodeType (TApp t1 t2) = encodeType t1 ++ "_" ++ encodeType t2
encodeType (TArrow t1 t2) = encodeType t1 ++ "_to_" ++ encodeType t2
encodeType (TUnresolved s) = sanitize s

-- | Render dictionary name for display
renderDict :: DictId -> String
renderDict DictId{dictClass, dictInstanceType, dictKind} =
    case dictKind of
        DKGlobal -> "Dict$" ++ dictClass ++ "$" ++ encodeType dictInstanceType
        DKStruct -> "DictStruct$" ++ dictClass

-- | Render dictionary name for LLVM
renderDictLLVM :: DictId -> String
renderDictLLVM d@DictId{dictModule} =
    sanitize dictModule ++ "_" ++ sanitize (renderDict d)
