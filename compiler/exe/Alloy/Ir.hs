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
    | OpSelect AOperand AOperand AOperand -- select cond trueVal falseVal (ternary)
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
    | -- These operations enable demand-driven parallel reduction of DUP projections

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
    | {- | Panic: abort execution with an error message.
      Calls soma_panic runtime function and is followed by unreachable.
      -}
      OpPanic !String
    | {- | Fork: spawn a parallel task
      OpFork taskFn taskArgs
      - taskFn: function to execute (direct function reference)
      - taskArgs: list of arguments for the function
      Returns: task handle (opaque pointer) or encoded inline result if parallelism disabled
      -}
      OpFork AOperand [AOperand]
    | {- | Join: wait for a forked task and get its result
        OpJoin taskHandle
        - taskHandle: the handle from OpFork
        Returns: the computation's result
      -}
      OpJoin AOperand
    | {- | Initialize graph runtime: num_workers
      Returns a pointer to the GraphRuntime (stored in a global typically)
      -}
      OpGraphInit !Int
    | -- | Shutdown graph runtime
      OpGraphShutdown
    | {- | Create a NUM node in the graph: value
      Returns node index (u32)
      -}
      OpGraphNum AOperand
    | {- | Create an ADD node in the graph: left_idx, right_idx
      Returns node index (u32)
      -}
      OpGraphAdd AOperand AOperand
    | {- | Create a SUB node in the graph: left_idx, right_idx
      Returns node index (u32)
      -}
      OpGraphSub AOperand AOperand
    | {- | Create a MUL node in the graph: left_idx, right_idx
      Returns node index (u32)
      -}
      OpGraphMul AOperand AOperand
    | {- | Create a DIV node in the graph: left_idx, right_idx
      Returns node index (u32)
      -}
      OpGraphDiv AOperand AOperand
    | {- | Create a MOD node in the graph: left_idx, right_idx
      Returns node index (u32)
      -}
      OpGraphMod AOperand AOperand
    | {- | Create a CALL node in the graph: fn_idx, arg_indices
      The function index refers to a registered graph function.
      Returns node index (u32)
      -}
      OpGraphCall !String [AOperand]
    | {- | Reduce a graph to a value: root_idx
      Returns the final i64 value after reduction.
      Uses parallel reduction if workers > 1.
      NOTE: Only call from top-level (soma_main), never from graph functions!
      -}
      OpGraphReduce AOperand
    | {- | Extract integer from a NUM term.
      Assumes the term is already a TAG_NUM. Does NOT reduce.
      Use this in graph functions to extract arg values.
      Calls inet_get_num_ext(term) -> i64
      -}
      OpGraphExtractNum AOperand
    | {- | Register a function for graph reduction: name, arity, impl_ptr
      Returns function index (u16) for use in OpGraphCall.
      -}
      OpGraphRegisterFunc !String !Int AOperand
    | {- | Create a DUP node in the graph: label, target_idx
      For duplicating values in interaction nets.
      Returns the DUP term (u64). Use OpGraphDupGetProj0/1 to get projections.
      -}
      OpGraphDup !Int AOperand
    | {- | Get first projection from a DUP node: dup_term
      Reads from proj0 slot of the DUP node.
      Returns Term (u64)
      -}
      OpGraphDupGetProj0 AOperand
    | {- | Get second projection from a DUP node: dup_term
      Reads from proj1 slot of the DUP node.
      Returns Term (u64)
      -}
      OpGraphDupGetProj1 AOperand
    | {- | Create a SUP node in the graph: label, left_idx, right_idx
      Superposition node for interaction nets.
      Returns node index (u32)
      -}
      OpGraphSup !Int AOperand AOperand
    | {- | Create a LAM node in the graph: var_slot_idx, body_idx
      Lambda abstraction for higher-order functions.
      Returns node index (u32)
      -}
      OpGraphLam AOperand AOperand
    | {- | Create an APP node in the graph: fn_idx, arg_idx
      Function application for beta reduction.
      Returns node index (u32)
      -}
      OpGraphApp AOperand AOperand
    | {- | Create an ERA node in the graph (erasure/unit)
      Returns node index (u32)
      -}
      OpGraphEra
    | {- | Create a REF node in the graph: func_name, arg_term
      Function reference that will be expanded lazily by the runtime.
      Returns Term (u64)
      -}
      OpGraphRef !String !Int AOperand -- func_name, func_index, arg
    | {- | Create a closure in the graph: func_idx, arity, env_values
      Closures capture environment values and are applied incrementally.
      Returns Term (u64)
      -}
      OpGraphClosure !Int !Int [AOperand]
    | {- | Apply a closure to an argument
      If arity > 1: creates partial application (new closure with arg added to env)
      If arity == 1: calls the function with full environment
      Returns Term (u64)
      -}
      OpGraphClosureApp AOperand AOperand
    | {- | Extract a value from a closure's environment
      OpGraphClosureGetEnv closure index
      Returns the Term at env[index]
      -}
      OpGraphClosureGetEnv AOperand !Int
    deriving (Generic, Show, Eq)

data AEffect
    = EffStore AOperand AOperand -- store value at address
    | EffStoreIndex AOperand AOperand AOperand -- store at array[index] := value
    | EffDrop AOperand -- free heap-allocated value (ERA node)
    | EffClosureSetEnv AOperand !Int AOperand -- set closure env slot: closure, index, value
    -- Graph reduction effects
    | EffGraphInit !Int -- initialize graph runtime with N workers
    | EffGraphShutdown -- shutdown graph runtime
    | EffGraphRegisterFunc !String !Int AOperand -- register function: name, arity, impl_ptr
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
