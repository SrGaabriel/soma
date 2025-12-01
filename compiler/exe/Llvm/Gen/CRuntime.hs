{- | External C Runtime Declarations for Soma

This module provides LLVM external declarations for linking against
the C runtime library (libsoma_runtime.a).

The INET runtime provides:
- Parallel graph reduction with work-stealing
- Lambda/closure support with shallow cloning
- Tagged pointer representation for unboxed primitives
- Chase-Lev deque for efficient parallelism
-}
module Llvm.Gen.CRuntime (
    cRuntimeExternalDeclarations,
    cRuntimeDependencies,
    cRuntimeStructs,
) where

import Llvm.Dependencies (LlvmDependency (..))
import Llvm.Ir (IR (toLlvm))
import Llvm.Types (LlvmType (..))

-- | Opaque pointer type
ptrType :: LlvmType
ptrType = LlvmPointer LlvmI8

{- | INET Term is i64 (64-bit encoded term)
   [loc:32][aux:16][sub:1][reserved:7][tag:8]
-}
termType :: LlvmType
termType = LlvmI64

-- | Location type (32-bit)
locType :: LlvmType
locType = LlvmI32

-- | All struct definitions (INET uses flat encoding, minimal structs)
cRuntimeStructs :: [LlvmDependency]
cRuntimeStructs = []

-- | External function declarations for INET runtime
cRuntimeDependencies :: [LlvmDependency]
cRuntimeDependencies =
    [ -- INET lifecycle
      LlvmFunctionDependency "inet_init" ptrType [LlvmI32] -- num_threads -> INet*
    , LlvmFunctionDependency "inet_init_globals" LlvmVoid [LlvmI32] -- num_threads -> void (sets g_inet and g_inet_tm)
    , LlvmFunctionDependency "inet_free" LlvmVoid [ptrType] -- INet* -> void
    , -- Function registration
      LlvmFunctionDependency "inet_register_func" LlvmVoid [ptrType, ptrType, LlvmI16, ptrType]
    , -- INet*, name, arity, func_ptr

      -- Heap operations (thread-local)
      LlvmFunctionDependency "inet_alloc" locType [ptrType, ptrType, LlvmI32]
    , -- INet*, ThreadMem*, count -> Loc
      LlvmFunctionDependency "inet_set" LlvmVoid [ptrType, locType, termType]
    , -- INet*, Loc, Term -> void
      LlvmFunctionDependency "inet_get" termType [ptrType, locType]
    , -- INet*, Loc -> Term
      LlvmFunctionDependency "inet_subst" LlvmVoid [ptrType, locType, termType]
    , -- INet*, Loc, Term -> void (set with SUB bit)

      -- Term constructors (using _ext wrappers for inline functions)
      LlvmFunctionDependency "inet_num_ext" termType [LlvmI64]
    , -- int64 -> Term (create NUM term)
      LlvmFunctionDependency "inet_lam" termType [ptrType, ptrType, locType, termType]
    , -- INet*, ThreadMem*, var_loc, body -> Term
      LlvmFunctionDependency "inet_app" termType [ptrType, ptrType, termType, termType]
    , -- INet*, ThreadMem*, fun, arg -> Term
      LlvmFunctionDependency "inet_opr" termType [ptrType, ptrType, LlvmI16, termType, termType]
    , -- INet*, ThreadMem*, op, a, b -> Term
      LlvmFunctionDependency "inet_ref" termType [ptrType, ptrType, LlvmI16, termType]
    , -- INet*, ThreadMem*, func_idx, arg -> Term
      LlvmFunctionDependency "inet_con" termType [ptrType, ptrType, termType, termType]
    , -- INet*, ThreadMem*, fst, snd -> Term (constructor/pair)
      LlvmFunctionDependency "inet_sup" termType [ptrType, ptrType, LlvmI16, termType, termType]
    , -- INet*, ThreadMem*, label, a, b -> Term (superposition)
      LlvmFunctionDependency "inet_dup" termType [ptrType, ptrType, LlvmI16, termType]
    , -- INet*, ThreadMem*, label, target -> Term (duplicator)
      LlvmFunctionDependency "inet_closure" termType [ptrType, ptrType, LlvmI16, LlvmI16, ptrType, LlvmI16]
    , -- INet*, ThreadMem*, func_idx, arity, env_ptr, env_size -> Term

      -- Closure operations
      LlvmFunctionDependency "inet_clone_closure" termType [ptrType, ptrType, termType]
    , -- INet*, ThreadMem*, closure -> Term (shallow copy)
      LlvmFunctionDependency "inet_closure_get_env" termType [ptrType, termType, LlvmI16]
    , -- INet*, closure_term, index -> Term (get env slot)

      -- Reduction
      LlvmFunctionDependency "inet_reduce" LlvmI64 [ptrType, termType]
    , -- INet*, root_term -> int64 (result)

      -- Term accessors (using _ext wrappers for inline functions)
      LlvmFunctionDependency "inet_get_num_ext" LlvmI64 [termType]
    , -- Term -> int64 (extract number value)

      -- Debug
      LlvmFunctionDependency "inet_print_term" LlvmVoid [ptrType, termType]
    , LlvmFunctionDependency "inet_print_stats" LlvmVoid [ptrType]
    , -- Global INET pointer (set in main)
      LlvmGlobalDependency "g_inet" ptrType
    , LlvmGlobalDependency
        "g_inet_tm"
        ptrType -- Main thread's ThreadMem
    , LlvmFunctionDependency
        "soma_pool_init"
        LlvmVoid
        []
    , LlvmFunctionDependency "soma_pool_cleanup" LlvmVoid []
    , -- SUP operations
      LlvmFunctionDependency "soma_dup" ptrType [LlvmI32, ptrType]
    , LlvmFunctionDependency "soma_proj0" LlvmI64 [LlvmI64]
    , LlvmFunctionDependency "soma_proj1" LlvmI64 [LlvmI64]
    , -- Parallel SUP operations (SomaValue = i64)
      LlvmFunctionDependency "soma_par_proj0" LlvmI64 [LlvmI64, LlvmI32]
    , LlvmFunctionDependency "soma_par_proj1" LlvmI64 [LlvmI64, LlvmI32]
    , -- Fork-join parallelism (returns ptr to SomaTask, or NULL if parallel disabled)
      LlvmFunctionDependency "soma_fork_direct" ptrType [ptrType, LlvmI64] -- fn, arg
    , LlvmFunctionDependency "soma_fork_closure" ptrType [ptrType, ptrType, LlvmI64] -- fn, closure, arg
    , LlvmFunctionDependency "soma_fork_multi" ptrType [ptrType, LlvmPointer LlvmI64, LlvmI32] -- fn, args[], num_args
    , LlvmFunctionDependency "soma_join" LlvmI64 [ptrType] -- task -> result
    , LlvmFunctionDependency "soma_par_enabled_export" LlvmI32 [] -- check if parallel runtime enabled (exported wrapper)
    , -- Closure operations
      LlvmFunctionDependency "soma_alloc_closure" ptrType [ptrType, LlvmI8, LlvmI16]
    , LlvmFunctionDependency "soma_closure_set_env" LlvmVoid [ptrType, LlvmI16, LlvmI64]
    , LlvmFunctionDependency "soma_closure_get_env" LlvmI64 [ptrType, LlvmI16]
    , LlvmFunctionDependency "soma_clone_closure" ptrType [ptrType]
    , -- Memory management
      LlvmFunctionDependency "soma_era_free" LlvmVoid [ptrType]
    , LlvmFunctionDependency "soma_fresh_label" LlvmI32 []
    , -- Pool allocation (for direct use)
      LlvmFunctionDependency "soma_pool_alloc_sup" ptrType []
    , LlvmFunctionDependency "soma_pool_alloc_closure" ptrType [LlvmI16]
    , LlvmFunctionDependency "soma_pool_free_sup" LlvmVoid [ptrType]
    , LlvmFunctionDependency "soma_pool_free_closure" LlvmVoid [ptrType, LlvmI16]
    ]

cRuntimeExternalDeclarations :: String
cRuntimeExternalDeclarations = unlines $ map toLlvm cRuntimeDependencies
