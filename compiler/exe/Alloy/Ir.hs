{-# LANGUAGE DeriveGeneric #-}

module Alloy.Ir where

import GHC.Generics (Generic)
import Metal.Metadata (MetallicTypeClassMetadata)
import Typing.Types (Constraint, Type)

type Name = String

type BlockName = String

type FieldIndex = Int

data AlloyModule = AlloyModule
    { amName :: String
    , amFunctions :: [AlloyFunction]
    , amDictionaries :: [DictionaryDef]
    , amTypeClasses :: [MetallicTypeClassMetadata]
    }
    deriving (Generic, Show, Eq)

data DictionaryDef = DictionaryDef
    { ddClassName :: String
    , ddForType :: Type
    , ddMethods :: [(String, Name)]
    }
    deriving (Generic, Show, Eq)

data AlloyFunction = AlloyFunction
    { afName :: Name
    , afParams :: [(Name, Type)]
    , afReturnType :: Type
    , afEntry :: BlockName
    , afBlocks :: [ABlock]
    , afConstraints :: [Constraint]
    }
    deriving (Generic, Show, Eq)

data ABlock = ABlock
    { abName :: BlockName
    , abParams :: [(Name, Type)]
    , abInstrs :: [AInstr]
    , abTerminator :: ATerminator
    }
    deriving (Generic, Show, Eq)

data AInstr
    = ILet Name Type AOp
    | IEffect AEffect
    deriving (Generic, Show, Eq)

data AOperand
    = OpVar Name
    | OpConst AConst
    deriving (Generic, Show, Eq, Ord)

data AConst
    = CInt Int
    | CBool Bool
    | CString String
    | CUnit
    deriving (Generic, Show, Eq, Ord)

data ACallable
    = Direct Name
    | Indirect AOperand
    deriving (Generic, Show, Eq, Ord)

data AOp
    = OpBin ABinOpKind AOperand AOperand -- Int/arithmetic/bitwise binop
    | OpUnary AUnaryOpKind AOperand -- not/neg etc.
    | OpCmp ACmpOp AOperand AOperand -- comparisons
    | OpLoad AOperand -- load from pointer-like operand
    | OpAllocStack Type -- allocate stack storage; returns address
    | OpAllocHeap Type -- allocate heap storage; returns address
    | OpCall ACallable [AOperand] -- call; result type given by ILet
    | OpConstruct
        { acTypeName :: String
        , acTag :: Int
        , acFields :: [AOperand]
        } -- ADT/enum constructor; returns aggregate
    | OpTagOf AOperand -- extract tag from ADT/enum aggregate
    | OpProject AOperand FieldIndex -- project field by index (records/tuples/constructors)
    | OpIndex AOperand AOperand -- index into array/slice: base, idx
    | OpMakeArray [AOperand] -- array aggregate literal (element type dictated by ILet type)
    | OpMakeTuple [AOperand] -- tuple aggregate literal (shape dictated by ILet type)
    | OpGetDict String Type -- get dictionary for typeclass + type
    | OpDictCall AOperand Int String [AOperand] -- call method through dictionary: dict, method index, method name, args
    deriving (Generic, Show, Eq)

data AEffect
    = EffStore AOperand AOperand -- store value at address
    | EffStoreIndex AOperand AOperand AOperand -- store at array[index] := value
    | EffDrop AOperand
    deriving (Generic, Show, Eq)

data ATerminator
    = ABr BlockName [AOperand] -- branch to block with arguments
    | ACondBr AOperand BlockName [AOperand] BlockName [AOperand] -- conditional branch
    | ASwitch AOperand [(Int, BlockName)] (Maybe BlockName) -- switch on an Int-like operand
    | ARet (Maybe AOperand) -- return optional value (use unit type for void-like)
    | AUnreachable -- unreachable
    deriving (Generic, Show, Eq)

data ABinOpKind
    = IAdd
    | ISub
    | IMul
    | IDiv
    | IMod
    | And
    | Or
    | Xor
    | Shl
    | LShr
    | AShr
    deriving (Generic, Show, Eq, Ord)

data AUnaryOpKind
    = Not -- boolean/Int bitwise not
    | Neg -- arithmetic negation
    deriving (Generic, Show, Eq, Ord)

data ACmpOp
    = CEq
    | CNe
    | CUlt
    | CUle
    | CUgt
    | CUge
    | CSlt
    | CSle
    | CSgt
    | CSge
    deriving (Generic, Show, Eq, Ord)
