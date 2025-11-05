module Alloy.Ir where

import Typing.Types (Type)

type Name = String
type BlockName = String
type FieldIndex = Int

data AlloyModule = AlloyModule
    { amName :: String
    , amFunctions :: [AlloyFunction]
    }
    deriving (Show, Eq)

data AlloyFunction = AlloyFunction
    { afName :: Name
    , afParams :: [(Name, Type)]
    , afReturnType :: Type
    , afEntry :: BlockName
    , afBlocks :: [ABlock]
    }
    deriving (Show, Eq)

data ABlock = ABlock
    { abName :: BlockName
    , abParams :: [(Name, Type)]
    , abInstrs :: [AInstr]
    , abTerminator :: ATerminator
    }
    deriving (Show, Eq)

data AInstr
    = ILet Name Type AOp
    | IEffect AEffect
    deriving (Show, Eq)

data AOperand
    = OpVar Name
    | OpConst AConst
    deriving (Show, Eq, Ord)

data AConst
    = CInt Integer
    | CBool Bool
    | CString String
    | CUnit
    deriving (Show, Eq, Ord)

data ACallable
    = Direct Name
    | Indirect AOperand
    deriving (Show, Eq, Ord)

data AOp
    = OpBin ABinOpKind AOperand AOperand -- integer/arithmetic/bitwise binop
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
    deriving (Show, Eq)

data AEffect
    = EffStore AOperand AOperand -- store value at address
    | EffStoreIndex AOperand AOperand AOperand -- store at array[index] := value
    | EffDrop AOperand -- language-defined destructor/drop if applicable
    deriving (Show, Eq)

data ATerminator
    = ABr BlockName [AOperand] -- branch to block with arguments
    | ACondBr AOperand BlockName [AOperand] BlockName [AOperand] -- conditional branch
    | ASwitch AOperand [(Integer, BlockName)] (Maybe BlockName) -- switch on an integer-like operand
    | ARet (Maybe AOperand) -- return optional value (use unit type for void-like)
    | AUnreachable -- unreachable
    deriving (Show, Eq)

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
    deriving (Show, Eq, Ord)

data AUnaryOpKind
    = Not -- boolean/integer bitwise not
    | Neg -- arithmetic negation
    deriving (Show, Eq, Ord)

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
    deriving (Show, Eq, Ord)
