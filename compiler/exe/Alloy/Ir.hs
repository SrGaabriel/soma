{-# LANGUAGE DeriveGeneric #-}

module Alloy.Ir where

import GHC.Generics (Generic)
import Metal.Metadata (MetallicTypeClassMetadata)
import Typing.Types (Constraint, Type)

type Name = String

type BlockName = String

type FieldIndex = Int

{- | Information about closure environment slots for specialized duplication.
Each entry is (slotIndex, isClosureTyped) where isClosureTyped indicates
whether the slot contains a closure that needs recursive duplication.
-}
type SlotInfo = [(Int, Bool)]

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
    , afIsInline :: Bool
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
    -- Lazy duplication operations (Interaction Net DUP/SUP)
    | OpDup !Int AOperand -- create lazy duplication node: label, value -> SUP handle
    | OpDupProj0 AOperand -- first projection from SUP handle (dp0)
    | OpDupProj1 AOperand -- second projection from SUP handle (dp1)
    -- Closure operations (for Path B runtime)
    | OpWrapClosure AOperand -- wrap a function pointer in a SomaClosure (for DUP-LAM)
    | OpAllocClosure AOperand !Int !Int -- allocate closure: func_ptr, arity, env_size
    | OpClosureSetEnv AOperand !Int AOperand -- set env slot: closure, index, value
    | OpClosureGetEnv AOperand !Int -- get env slot: closure, index
    | OpClosureGetFunc AOperand -- get function pointer from closure
    -- Session 13: Specialized closure duplication with HVM-style SUP propagation
    -- These operations enable lazy cloning where nested closures in env slots
    -- are wrapped in SUPs rather than eagerly cloned
    | {- | Specialized DUP for closures: label, closure, slot_info
      Creates a SUP handle like OpDup, but carries slot type info for specialized cloning
      -}
      OpDupClosure !Int AOperand !SlotInfo
    | {- | First projection from closure SUP: sup_handle, env_size, slot_info
      Returns original closure, marks state as "proj0 accessed"
      -}
      OpDupClosureProj0 AOperand !Int !SlotInfo
    | {- | Second projection from closure SUP: sup_handle, env_size, slot_info
      Creates clone with SUPs in closure-typed env slots (inline specialized code)
      -}
      OpDupClosureProj1 AOperand !Int !SlotInfo
    | {- | Direct env slot access (for original closures): closure, index
      Single load, no SUP projection needed
      -}
      OpClosureGetEnvDirect AOperand !Int
    | {- | SUP env slot access (for cloned closures with closure-typed slots): closure, index
      Loads SUP from slot, then projects through it (uses proj1 since clone is "second copy")
      -}
      OpClosureGetEnvSUP AOperand !Int
    | -- Session 19: Parallel reduction support
      -- These operations enable demand-driven parallel reduction of DUP projections

      {- | Parallel-aware first projection: sup_handle, work_estimate
      When workers are hungry and work_estimate >= threshold, may spawn the other branch
      as a parallel task. Otherwise behaves like OpDupProj0.
      -}
      OpParProj0 AOperand !Int
    | {- | Parallel-aware second projection: sup_handle, work_estimate
      When workers are hungry and work_estimate >= threshold, may spawn the other branch
      as a parallel task. Otherwise behaves like OpDupProj1.
      -}
      OpParProj1 AOperand !Int
    | {- | Parallel-aware closure first projection: sup_handle, env_size, slot_info, work_estimate
      Like OpDupClosureProj0 but with parallel task spawning support.
      -}
      OpParClosureProj0 AOperand !Int !SlotInfo !Int
    | {- | Parallel-aware closure second projection: sup_handle, env_size, slot_info, work_estimate
      Like OpDupClosureProj1 but with parallel task spawning support.
      -}
      OpParClosureProj1 AOperand !Int !SlotInfo !Int
    deriving (Generic, Show, Eq)

data AEffect
    = EffStore AOperand AOperand -- store value at address
    | EffStoreIndex AOperand AOperand AOperand -- store at array[index] := value
    | EffDrop AOperand -- free heap-allocated value (ERA node)
    | EffClosureSetEnv AOperand !Int AOperand -- set closure env slot: closure, index, value
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
