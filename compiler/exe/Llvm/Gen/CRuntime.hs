{- | External C Runtime Declarations for Soma

This module provides LLVM external declarations for linking against
the C runtime library (libsoma_runtime.a) instead of generating
the runtime functions in LLVM IR.

The C runtime provides:
- Memory pool allocation for reduced malloc overhead
- Tagged pointer representation for unboxed primitives
- Optimized closure cloning and SUP operations
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

{- | SUP node struct: { i8, i32, ptr, ptr, ptr }
tag, label, value, proj0, proj1
-}
supNodeStruct :: LlvmDependency
supNodeStruct = LlvmStructDependency "SomaSup" [LlvmI8, LlvmI32, ptrType, ptrType, ptrType]

{- | Closure header struct: { i8, i8, i16, i32, ptr }
tag, arity, env_size, padding, func_ptr (env follows)
-}
closureHeaderStruct :: LlvmDependency
closureHeaderStruct = LlvmStructDependency "SomaClosure" [LlvmI8, LlvmI8, LlvmI16, LlvmI32, ptrType]

-- | All struct definitions
cRuntimeStructs :: [LlvmDependency]
cRuntimeStructs = [supNodeStruct, closureHeaderStruct]

-- | External function declarations for C runtime
cRuntimeDependencies :: [LlvmDependency]
cRuntimeDependencies =
    [ -- Memory pool initialization
      LlvmFunctionDependency "soma_pool_init" LlvmVoid []
    , LlvmFunctionDependency "soma_pool_cleanup" LlvmVoid []
    , -- SUP operations
      LlvmFunctionDependency "soma_dup" ptrType [LlvmI32, ptrType]
    , LlvmFunctionDependency "soma_proj0" LlvmI64 [LlvmI64]
    , LlvmFunctionDependency "soma_proj1" LlvmI64 [LlvmI64]
    , -- Session 19: Parallel SUP operations (SomaValue = i64)
      LlvmFunctionDependency "soma_par_proj0" LlvmI64 [LlvmI64, LlvmI32]
    , LlvmFunctionDependency "soma_par_proj1" LlvmI64 [LlvmI64, LlvmI32]
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
    , -- Standard library dependencies
      LlvmFunctionDependency "malloc" ptrType [LlvmI64]
    , LlvmFunctionDependency "free" LlvmVoid [ptrType]
    , LlvmFunctionDependency "memcpy" ptrType [ptrType, ptrType, LlvmI64]
    , -- Session 27: Graph reduction runtime
      LlvmFunctionDependency "soma_graph_init" ptrType [LlvmI32]
    , LlvmFunctionDependency "soma_graph_shutdown" LlvmVoid [ptrType]
    , LlvmFunctionDependency "soma_graph_num" LlvmI32 [ptrType, LlvmI64]
    , LlvmFunctionDependency "soma_graph_add" LlvmI32 [ptrType, LlvmI32, LlvmI32]
    , LlvmFunctionDependency "soma_graph_sub" LlvmI32 [ptrType, LlvmI32, LlvmI32]
    , LlvmFunctionDependency "soma_graph_mul" LlvmI32 [ptrType, LlvmI32, LlvmI32]
    , LlvmFunctionDependency "soma_graph_call1" LlvmI32 [ptrType, LlvmI16, LlvmI32]
    , LlvmFunctionDependency "soma_graph_call2" LlvmI32 [ptrType, LlvmI16, LlvmI32, LlvmI32]
    , LlvmFunctionDependency "soma_graph_reduce_fast" LlvmI64 [ptrType, LlvmI32]
    , LlvmFunctionDependency "soma_graph_reduce_parallel" LlvmI64 [ptrType, LlvmI32]
    , LlvmFunctionDependency "soma_graph_register_func" LlvmI16 [ptrType, ptrType, LlvmI8, LlvmI8, ptrType]
    , -- Session 29: Interaction net graph operations
      LlvmFunctionDependency "soma_graph_dup" LlvmI32 [ptrType, LlvmI32, LlvmI32]
    , LlvmFunctionDependency "soma_graph_sup" LlvmI32 [ptrType, LlvmI16, LlvmI32, LlvmI32]
    , LlvmFunctionDependency "soma_graph_lam" LlvmI32 [ptrType, LlvmI32, LlvmI32]
    , LlvmFunctionDependency "soma_graph_app" LlvmI32 [ptrType, LlvmI32, LlvmI32]
    , LlvmFunctionDependency "soma_graph_era" LlvmI32 [ptrType]
    , -- Global graph runtime pointer
      LlvmGlobalDependency "g_graph_rt" ptrType
    ]

cRuntimeExternalDeclarations :: String
cRuntimeExternalDeclarations = unlines $ map toLlvm cRuntimeDependencies
