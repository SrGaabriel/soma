module Llvm.Gen.CRuntime (
    cruntimeInetInit,
    cruntimeInetInitGlobals,
    cruntimeInetFree,
    cruntimeInetRegisterFunc,
    cruntimeInetAlloc,
    cruntimeInetSet,
    cruntimeInetGet,
    cruntimeInetSubst,
    cruntimeInetNumExt,
    cruntimeInetLam,
    cruntimeInetApp,
    cruntimeInetOpr,
    cruntimeInetRef,
    cruntimeInetCon,
    cruntimeInetSup,
    cruntimeInetDup,
    cruntimeInetClosure,
    cruntimeInetCloneClosure,
    cruntimeInetClosureGetEnv,
    cruntimeInetReduce,
    cruntimeInetGetNumExt,
    cruntimeInetPrintTerm,
    cruntimeInetPrintStats,
    cruntimeGInet,
    cruntimeGInetTm,
    cruntimeSomaPoolInit,
    cruntimeSomaPoolCleanup,
    cruntimeSomaDup,
    cruntimeSomaProj0,
    cruntimeSomaProj1,
    cruntimeSomaParProj0,
    cruntimeSomaParProj1,
    cruntimeSomaForkDirect,
    cruntimeSomaForkClosure,
    cruntimeSomaForkMulti,
    cruntimeSomaJoin,
    cruntimeSomaParEnabledExport,
    cruntimeSomaAllocClosure,
    cruntimeSomaClosureSetEnv,
    cruntimeSomaClosureGetEnv,
    cruntimeSomaCloneClosure,
    cruntimeSomaEraFree,
    cruntimeSomaFreshLabel,
    cruntimeSomaPoolAllocSup,
    cruntimeSomaPoolAllocClosure,
    cruntimeSomaPoolFreeSup,
    cruntimeSomaPoolFreeClosure,
    cruntimeSomaPanic,
) where

import Llvm.Dependencies (LlvmDependency (..))
import Llvm.Types (LlvmType (..))

ptrType :: LlvmType
ptrType = LlvmPointer LlvmI8

termType :: LlvmType
termType = LlvmI64

locType :: LlvmType
locType = LlvmI32

cruntimeInetInit :: LlvmDependency
cruntimeInetInit = LlvmFunctionDependency "inet_init" ptrType [LlvmI32]

cruntimeInetInitGlobals :: LlvmDependency
cruntimeInetInitGlobals = LlvmFunctionDependency "inet_init_globals" LlvmVoid [LlvmI32]

cruntimeInetFree :: LlvmDependency
cruntimeInetFree = LlvmFunctionDependency "inet_free" LlvmVoid [ptrType]

cruntimeInetRegisterFunc :: LlvmDependency
cruntimeInetRegisterFunc = LlvmFunctionDependency "inet_register_func" LlvmVoid [ptrType, ptrType, LlvmI16, ptrType]

cruntimeInetAlloc :: LlvmDependency
cruntimeInetAlloc = LlvmFunctionDependency "inet_alloc" locType [ptrType, ptrType, LlvmI32]

cruntimeInetSet :: LlvmDependency
cruntimeInetSet = LlvmFunctionDependency "inet_set" LlvmVoid [ptrType, locType, termType]

cruntimeInetGet :: LlvmDependency
cruntimeInetGet = LlvmFunctionDependency "inet_get" termType [ptrType, locType]

cruntimeInetSubst :: LlvmDependency
cruntimeInetSubst = LlvmFunctionDependency "inet_subst" LlvmVoid [ptrType, locType, termType]

cruntimeInetNumExt :: LlvmDependency
cruntimeInetNumExt = LlvmFunctionDependency "inet_num_ext" termType [LlvmI64]

cruntimeInetLam :: LlvmDependency
cruntimeInetLam = LlvmFunctionDependency "inet_lam" termType [ptrType, ptrType, locType, termType]

cruntimeInetApp :: LlvmDependency
cruntimeInetApp = LlvmFunctionDependency "inet_app" termType [ptrType, ptrType, termType, termType]

cruntimeInetOpr :: LlvmDependency
cruntimeInetOpr = LlvmFunctionDependency "inet_opr" termType [ptrType, ptrType, LlvmI16, termType, termType]

cruntimeInetRef :: LlvmDependency
cruntimeInetRef = LlvmFunctionDependency "inet_ref" termType [ptrType, ptrType, LlvmI16, termType]

cruntimeInetCon :: LlvmDependency
cruntimeInetCon = LlvmFunctionDependency "inet_con" termType [ptrType, ptrType, termType, termType]

cruntimeInetSup :: LlvmDependency
cruntimeInetSup = LlvmFunctionDependency "inet_sup" termType [ptrType, ptrType, LlvmI16, termType, termType]

cruntimeInetDup :: LlvmDependency
cruntimeInetDup = LlvmFunctionDependency "inet_dup" termType [ptrType, ptrType, LlvmI16, termType]

cruntimeInetClosure :: LlvmDependency
cruntimeInetClosure = LlvmFunctionDependency "inet_closure" termType [ptrType, ptrType, LlvmI16, LlvmI16, ptrType, LlvmI16]

cruntimeInetCloneClosure :: LlvmDependency
cruntimeInetCloneClosure = LlvmFunctionDependency "inet_clone_closure" termType [ptrType, ptrType, termType]

cruntimeInetClosureGetEnv :: LlvmDependency
cruntimeInetClosureGetEnv = LlvmFunctionDependency "inet_closure_get_env" termType [ptrType, termType, LlvmI16]

cruntimeInetReduce :: LlvmDependency
cruntimeInetReduce = LlvmFunctionDependency "inet_reduce" LlvmI64 [ptrType, termType]

cruntimeInetGetNumExt :: LlvmDependency
cruntimeInetGetNumExt = LlvmFunctionDependency "inet_get_num_ext" LlvmI64 [termType]

cruntimeInetPrintTerm :: LlvmDependency
cruntimeInetPrintTerm = LlvmFunctionDependency "inet_print_term" LlvmVoid [ptrType, termType]

cruntimeInetPrintStats :: LlvmDependency
cruntimeInetPrintStats = LlvmFunctionDependency "inet_print_stats" LlvmVoid [ptrType]

cruntimeGInet :: LlvmDependency
cruntimeGInet = LlvmGlobalDependency "g_inet" (LlvmPointer ptrType) -- pointer to pointer cuz why not

cruntimeGInetTm :: LlvmDependency
cruntimeGInetTm = LlvmGlobalDependency "g_inet_tm" (LlvmPointer ptrType) -- pointer to pointer cuz why not

cruntimeSomaPoolInit :: LlvmDependency
cruntimeSomaPoolInit = LlvmFunctionDependency "soma_pool_init" LlvmVoid []

cruntimeSomaPoolCleanup :: LlvmDependency
cruntimeSomaPoolCleanup = LlvmFunctionDependency "soma_pool_cleanup" LlvmVoid []

cruntimeSomaDup :: LlvmDependency
cruntimeSomaDup = LlvmFunctionDependency "soma_dup" ptrType [LlvmI32, ptrType]

cruntimeSomaProj0 :: LlvmDependency
cruntimeSomaProj0 = LlvmFunctionDependency "soma_proj0" LlvmI64 [LlvmI64]

cruntimeSomaProj1 :: LlvmDependency
cruntimeSomaProj1 = LlvmFunctionDependency "soma_proj1" LlvmI64 [LlvmI64]

cruntimeSomaParProj0 :: LlvmDependency
cruntimeSomaParProj0 = LlvmFunctionDependency "soma_par_proj0" LlvmI64 [LlvmI64, LlvmI32]

cruntimeSomaParProj1 :: LlvmDependency
cruntimeSomaParProj1 = LlvmFunctionDependency "soma_par_proj1" LlvmI64 [LlvmI64, LlvmI32]

cruntimeSomaForkDirect :: LlvmDependency
cruntimeSomaForkDirect = LlvmFunctionDependency "soma_fork_direct" ptrType [ptrType, LlvmI64]

cruntimeSomaForkClosure :: LlvmDependency
cruntimeSomaForkClosure = LlvmFunctionDependency "soma_fork_closure" ptrType [ptrType, ptrType, LlvmI64]

cruntimeSomaForkMulti :: LlvmDependency
cruntimeSomaForkMulti = LlvmFunctionDependency "soma_fork_multi" ptrType [ptrType, LlvmPointer LlvmI64, LlvmI32]

cruntimeSomaJoin :: LlvmDependency
cruntimeSomaJoin = LlvmFunctionDependency "soma_join" LlvmI64 [ptrType]

cruntimeSomaParEnabledExport :: LlvmDependency
cruntimeSomaParEnabledExport = LlvmFunctionDependency "soma_par_enabled_export" LlvmI32 []

cruntimeSomaAllocClosure :: LlvmDependency
cruntimeSomaAllocClosure = LlvmFunctionDependency "soma_alloc_closure" ptrType [ptrType, LlvmI8, LlvmI16]

cruntimeSomaClosureSetEnv :: LlvmDependency
cruntimeSomaClosureSetEnv = LlvmFunctionDependency "soma_closure_set_env" LlvmVoid [ptrType, LlvmI16, LlvmI64]

cruntimeSomaClosureGetEnv :: LlvmDependency
cruntimeSomaClosureGetEnv = LlvmFunctionDependency "soma_closure_get_env" LlvmI64 [ptrType, LlvmI16]

cruntimeSomaCloneClosure :: LlvmDependency
cruntimeSomaCloneClosure = LlvmFunctionDependency "soma_clone_closure" ptrType [ptrType]

cruntimeSomaEraFree :: LlvmDependency
cruntimeSomaEraFree = LlvmFunctionDependency "soma_era_free" LlvmVoid [ptrType]

cruntimeSomaFreshLabel :: LlvmDependency
cruntimeSomaFreshLabel = LlvmFunctionDependency "soma_fresh_label" LlvmI32 []

cruntimeSomaPoolAllocSup :: LlvmDependency
cruntimeSomaPoolAllocSup = LlvmFunctionDependency "soma_pool_alloc_sup" ptrType []

cruntimeSomaPoolAllocClosure :: LlvmDependency
cruntimeSomaPoolAllocClosure = LlvmFunctionDependency "soma_pool_alloc_closure" ptrType [LlvmI16]

cruntimeSomaPoolFreeSup :: LlvmDependency
cruntimeSomaPoolFreeSup = LlvmFunctionDependency "soma_pool_free_sup" LlvmVoid [ptrType]

cruntimeSomaPoolFreeClosure :: LlvmDependency
cruntimeSomaPoolFreeClosure = LlvmFunctionDependency "soma_pool_free_closure" LlvmVoid [ptrType, LlvmI16]

cruntimeSomaPanic :: LlvmDependency
cruntimeSomaPanic = LlvmFunctionDependency "soma_panic" LlvmVoid [ptrType]
