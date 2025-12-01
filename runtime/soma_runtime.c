/*
 * Soma Interaction Net Runtime
 *
 * Implements lazy duplication with HVM-style label-based annihilation.
 * Features:
 * - Per-thread memory pools (TLS) for lock-free allocation
 * - SIMD-optimized bulk operations where applicable
 * - Adaptive work-stealing threshold
 */

#include "soma_runtime.h"
#include <stdlib.h>
#include <string.h>
#include <stdatomic.h>
#include <stdio.h>

/* Debug flag - set via SOMA_DEBUG env var */
static int soma_debug = -1;  /* -1 = uninitialized */

static inline int soma_debug_enabled(void) {
    if (soma_debug < 0) {
        soma_debug = (getenv("SOMA_DEBUG") != NULL) ? 1 : 0;
    }
    return soma_debug;
}

#define DEBUG_PRINT(...) do { if (soma_debug_enabled()) { fprintf(stderr, __VA_ARGS__); } } while(0)

/* Global label counter (atomic for future parallel support) */
_Atomic uint32_t soma_label_counter = 0;

/* Global memory pools (fallback for main thread before TLS init) */
SomaPools soma_pools;
SomaPoolStats soma_pool_stats;

/*
 * ============================================================================
 * Per-Thread Memory Pool Implementation (TLS)
 * ============================================================================
 *
 * Each worker thread gets its own set of memory pools. This eliminates
 * contention on the global pools and enables lock-free allocation.
 *
 * The main thread uses the global pools as a fallback.
 */

/* Thread-local pool storage */
__thread SomaPools* tls_pools = NULL;
__thread int tls_pools_initialized = 0;

/* Allocate a new block for a pool */
static SomaPoolBlock* pool_alloc_block(void) {
    SomaPoolBlock* block = (SomaPoolBlock*)malloc(
        sizeof(SomaPoolBlock) + POOL_BLOCK_SIZE
    );
    if (block) {
        block->next = NULL;
        block->used = 0;
        atomic_fetch_add(&soma_pool_stats.blocks_allocated, 1);
        atomic_fetch_add(&soma_pool_stats.bytes_allocated, sizeof(SomaPoolBlock) + POOL_BLOCK_SIZE);
    }
    return block;
}

/* Initialize a single pool */
static void pool_init(SomaPool* pool, size_t item_size) {
    pool->blocks = pool_alloc_block();
    pool->item_size = item_size;
    pool->free_list = NULL;
}

/* Clean up a single pool */
static void pool_cleanup(SomaPool* pool) {
    SomaPoolBlock* block = pool->blocks;
    while (block) {
        SomaPoolBlock* next = block->next;
        free(block);
        block = next;
    }
    pool->blocks = NULL;
    pool->free_list = NULL;
}

/* Allocate from a pool */
static void* pool_alloc(SomaPool* pool) {
    /* Check free list first */
    if (pool->free_list) {
        void* ptr = pool->free_list;
        pool->free_list = *(void**)ptr;  /* First word is next pointer */
        return ptr;
    }

    /* Try current block */
    SomaPoolBlock* block = pool->blocks;
    if (block->used + pool->item_size <= POOL_BLOCK_SIZE) {
        void* ptr = block->data + block->used;
        block->used += pool->item_size;
        return ptr;
    }

    /* Need new block */
    SomaPoolBlock* new_block = pool_alloc_block();
    if (!new_block) {
        return NULL;  /* Out of memory */
    }
    new_block->next = pool->blocks;
    pool->blocks = new_block;

    void* ptr = new_block->data;
    new_block->used = pool->item_size;
    return ptr;
}

/* Return to pool's free list */
static void pool_free(SomaPool* pool, void* ptr) {
    /* Store next pointer in the freed slot */
    *(void**)ptr = pool->free_list;
    pool->free_list = ptr;
}

/* Initialize per-thread pools */
static void tls_pool_init(void) {
    if (tls_pools_initialized) return;
    
    tls_pools = (SomaPools*)malloc(sizeof(SomaPools));
    if (tls_pools) {
        pool_init(&tls_pools->sup_pool, POOL_SUP_SIZE);
        pool_init(&tls_pools->closure_small, POOL_CLOSURE_SMALL);
        pool_init(&tls_pools->closure_medium, POOL_CLOSURE_MEDIUM);
        tls_pools_initialized = 1;
    }
}

/* Cleanup per-thread pools */
static void tls_pool_cleanup(void) {
    if (!tls_pools_initialized || !tls_pools) return;
    
    pool_cleanup(&tls_pools->sup_pool);
    pool_cleanup(&tls_pools->closure_small);
    pool_cleanup(&tls_pools->closure_medium);
    free(tls_pools);
    tls_pools = NULL;
    tls_pools_initialized = 0;
}

/* Get the appropriate pools (TLS if available, global otherwise) */
static inline SomaPools* get_pools(void) {
    if (tls_pools_initialized && tls_pools) {
        return tls_pools;
    }
    return &soma_pools;
}

void soma_pool_init(void) {
    memset(&soma_pool_stats, 0, sizeof(soma_pool_stats));
    pool_init(&soma_pools.sup_pool, POOL_SUP_SIZE);
    pool_init(&soma_pools.closure_small, POOL_CLOSURE_SMALL);
    pool_init(&soma_pools.closure_medium, POOL_CLOSURE_MEDIUM);
}

void soma_pool_cleanup(void) {
    pool_cleanup(&soma_pools.sup_pool);
    pool_cleanup(&soma_pools.closure_small);
    pool_cleanup(&soma_pools.closure_medium);
}

void* soma_pool_alloc_sup(void) {
    atomic_fetch_add(&soma_pool_stats.sup_allocs, 1);
    SomaPools* pools = get_pools();
    return pool_alloc(&pools->sup_pool);
}

void* soma_pool_alloc_closure(uint16_t env_size) {
    size_t needed = sizeof(SomaClosure) + (env_size * sizeof(void*));
    SomaPools* pools = get_pools();

    if (needed <= POOL_CLOSURE_SMALL) {
        atomic_fetch_add(&soma_pool_stats.closure_small_allocs, 1);
        return pool_alloc(&pools->closure_small);
    }
    if (needed <= POOL_CLOSURE_MEDIUM) {
        atomic_fetch_add(&soma_pool_stats.closure_medium_allocs, 1);
        return pool_alloc(&pools->closure_medium);
    }

    /* Large closure - fall back to malloc */
    atomic_fetch_add(&soma_pool_stats.closure_large_allocs, 1);
    return malloc(needed);
}

void soma_pool_free_sup(void* ptr) {
    atomic_fetch_add(&soma_pool_stats.sup_frees, 1);
    SomaPools* pools = get_pools();
    pool_free(&pools->sup_pool, ptr);
}

void soma_pool_free_closure(void* ptr, uint16_t env_size) {
    size_t needed = sizeof(SomaClosure) + (env_size * sizeof(void*));
    SomaPools* pools = get_pools();

    if (needed <= POOL_CLOSURE_SMALL) {
        atomic_fetch_add(&soma_pool_stats.closure_small_frees, 1);
        pool_free(&pools->closure_small, ptr);
    } else if (needed <= POOL_CLOSURE_MEDIUM) {
        atomic_fetch_add(&soma_pool_stats.closure_medium_frees, 1);
        pool_free(&pools->closure_medium, ptr);
    } else {
        atomic_fetch_add(&soma_pool_stats.closure_large_frees, 1);
        free(ptr);
    }
}

/*
 * soma_fresh_label - Generate a fresh unique label
 *
 * Uses atomic increment for thread-safety (future parallel reduction).
 */
uint32_t soma_fresh_label(void) {
    return atomic_fetch_add(&soma_label_counter, 1);
}

/*
 * soma_dup - Create a lazy SUP node
 *
 * The value is not cloned immediately; cloning happens when both
 * projections are accessed.
 */
void* soma_dup(uint32_t label, void* value) {
    SomaSup* sup = (SomaSup*)soma_pool_alloc_sup();
    sup->tag   = SUP_TAG_FRESH;
    sup->label = label;
    sup->value = value;
    sup->proj0 = NULL;
    sup->proj1 = NULL;
    return sup;
}

/*
 * Helper: Check if a SomaValue is a heap pointer that might be a SUP
 */
static inline int is_heap_sup(SomaValue value) {
    if (!SOMA_IS_PTR(value) || value == 0) return 0;
    uint8_t tag = *(uint8_t*)SOMA_TO_PTR(value);
    return IS_SUP(tag);
}

/*
 * Helper: Check if a SomaValue is a heap pointer to a closure
 */
static inline int is_heap_closure(SomaValue value) {
    if (!SOMA_IS_PTR(value) || value == 0) return 0;
    uint8_t tag = *(uint8_t*)SOMA_TO_PTR(value);
    return tag == NODE_CLOSURE;
}

/*
 * soma_proj0 - Get first projection from SUP
 *
 * Implements HVM-style lazy duplication with label-based annihilation:
 * - If fresh: mark as proj0_accessed, return value
 * - If proj1 was first: check for annihilation or clone
 * - If already accessed: return cached value
 *
 * THREAD SAFETY: Uses atomic CAS on tag to prevent race conditions.
 * HVM3-style optimization: single atomic operation for state transition.
 *
 * Note: Values can be tagged pointers (ints, bools, chars) which don't
 * need cloning, or heap pointers (closures, SUPs) which may need special handling.
 */
SomaValue soma_proj0(SomaValue sup_val) {
    SomaSup* sup = (SomaSup*)SOMA_TO_PTR(sup_val);
    _Atomic uint8_t* tag_ptr = (_Atomic uint8_t*)&sup->tag;
    
    /* Single atomic load for tag - HVM3 style */
    uint8_t tag = atomic_load_explicit(tag_ptr, memory_order_acquire);

    /* Fresh - first access via proj0 */
    if (tag == SUP_TAG_FRESH) {
        /* Atomic CAS to claim this SUP - prevents race with proj1 */
        uint8_t expected = SUP_TAG_FRESH;
        if (atomic_compare_exchange_strong_explicit(tag_ptr, &expected, SUP_TAG_PROJ0,
                                                     memory_order_acq_rel, memory_order_acquire)) {
            /* Won the race - we're first */
            SomaValue value = (SomaValue)sup->value;

            /* Check for annihilation: is value a SUP with same label? */
            if (SOMA_IS_PTR(value) && value != 0) {
                uint8_t inner_tag = *(uint8_t*)SOMA_TO_PTR(value);
                if (IS_SUP(inner_tag)) {
                    SomaSup* inner = (SomaSup*)SOMA_TO_PTR(value);
                    if (inner->label == sup->label) {
                        /* Annihilate: return inner's value directly */
                        sup->proj0 = inner->value;
                        return (SomaValue)inner->value;
                    }
                }
            }

            /* No annihilation - cache and return value */
            sup->proj0 = (void*)value;
            return value;
        }
        /* Lost race - reload tag and fall through */
        tag = expected;
    }

    /* proj1 was accessed first - need to handle second access */
    if (tag == SUP_TAG_PROJ1) {
        /* Atomic CAS to transition to BOTH */
        uint8_t expected = SUP_TAG_PROJ1;
        if (atomic_compare_exchange_strong_explicit(tag_ptr, &expected, SUP_TAG_BOTH,
                                                     memory_order_acq_rel, memory_order_acquire)) {
            SomaValue value = (SomaValue)sup->value;

            /* Tagged values (int, bool, char) don't need cloning */
            if (!SOMA_IS_PTR(value) || value == 0) {
                sup->proj0 = (void*)value;
                return value;
            }

            /* Check for annihilation */
            uint8_t inner_tag = *(uint8_t*)SOMA_TO_PTR(value);
            if (IS_SUP(inner_tag)) {
                SomaSup* inner = (SomaSup*)SOMA_TO_PTR(value);
                if (inner->label == sup->label) {
                    /* Annihilate: return inner's value */
                    sup->proj0 = inner->value;
                    return (SomaValue)inner->value;
                }
                /* Different label - pass through (implicit commutation) */
                sup->proj0 = (void*)value;
                return value;
            }

            /* Check if closure - need to clone */
            if (inner_tag == NODE_CLOSURE) {
                void* cloned = soma_clone_closure(SOMA_TO_PTR(value));
                sup->proj0 = cloned;
                return SOMA_PTR(cloned);
            }

            /* Unknown heap object - shallow copy */
            sup->proj0 = (void*)value;
            return value;
        }
        /* Lost race - someone else transitioned, reload */
        tag = expected;
    }

    /* proj1 was accessed first with speculative cloning - wait for clone */
    if (tag == SUP_TAG_PROJ1_CLONING) {
        atomic_store_explicit(tag_ptr, SUP_TAG_BOTH, memory_order_release);
        SomaTask* task = (SomaTask*)sup->proj0;
        
        /* Wait for the clone task to complete and get result */
        SomaValue cloned = soma_par_run_task(task);
        sup->proj0 = (void*)cloned;
        return cloned;
    }

    /* Already accessed (PROJ0, PROJ0_CLONING, or BOTH) - return cached */
    return (SomaValue)sup->proj0;
}

/*
 * soma_proj1 - Get second projection from SUP
 *
 * Symmetric to soma_proj0.
 * THREAD SAFETY: Uses atomic CAS on tag to prevent race conditions.
 */
SomaValue soma_proj1(SomaValue sup_val) {
    SomaSup* sup = (SomaSup*)SOMA_TO_PTR(sup_val);
    _Atomic uint8_t* tag_ptr = (_Atomic uint8_t*)&sup->tag;
    
    /* Single atomic load for tag - HVM3 style */
    uint8_t tag = atomic_load_explicit(tag_ptr, memory_order_acquire);

    /* Fresh - first access via proj1 */
    if (tag == SUP_TAG_FRESH) {
        /* Atomic CAS to claim this SUP - prevents race with proj0 */
        uint8_t expected = SUP_TAG_FRESH;
        if (atomic_compare_exchange_strong_explicit(tag_ptr, &expected, SUP_TAG_PROJ1,
                                                     memory_order_acq_rel, memory_order_acquire)) {
            /* Won the race - we're first */
            SomaValue value = (SomaValue)sup->value;

            /* Check for annihilation */
            if (SOMA_IS_PTR(value) && value != 0) {
                uint8_t inner_tag = *(uint8_t*)SOMA_TO_PTR(value);
                if (IS_SUP(inner_tag)) {
                    SomaSup* inner = (SomaSup*)SOMA_TO_PTR(value);
                    if (inner->label == sup->label) {
                        /* Annihilate: return inner's value */
                        sup->proj1 = inner->value;
                        return (SomaValue)inner->value;
                    }
                }
            }

            /* No annihilation - cache and return value */
            sup->proj1 = (void*)value;
            return value;
        }
        /* Lost race - reload tag and fall through */
        tag = expected;
    }

    /* proj0 was accessed first - need to handle second access */
    if (tag == SUP_TAG_PROJ0) {
        /* Atomic CAS to transition to BOTH */
        uint8_t expected = SUP_TAG_PROJ0;
        if (atomic_compare_exchange_strong_explicit(tag_ptr, &expected, SUP_TAG_BOTH,
                                                     memory_order_acq_rel, memory_order_acquire)) {
            SomaValue value = (SomaValue)sup->value;

            /* Tagged values (int, bool, char) don't need cloning */
            if (!SOMA_IS_PTR(value) || value == 0) {
                sup->proj1 = (void*)value;
                return value;
            }

            /* Check for annihilation */
            uint8_t inner_tag = *(uint8_t*)SOMA_TO_PTR(value);
            if (IS_SUP(inner_tag)) {
                SomaSup* inner = (SomaSup*)SOMA_TO_PTR(value);
                if (inner->label == sup->label) {
                    /* Annihilate: return inner's value */
                    sup->proj1 = inner->value;
                    return (SomaValue)inner->value;
                }
                /* Different label - pass through */
                sup->proj1 = (void*)value;
                return value;
            }

            /* Check if closure - need to clone */
            if (inner_tag == NODE_CLOSURE) {
                void* cloned = soma_clone_closure(SOMA_TO_PTR(value));
                sup->proj1 = cloned;
                return SOMA_PTR(cloned);
            }

            /* Unknown heap object - shallow copy */
            sup->proj1 = (void*)value;
            return value;
        }
        /* Lost race - someone else transitioned, reload */
        tag = expected;
    }

    /* proj0 was accessed first with speculative cloning - wait for clone */
    if (tag == SUP_TAG_PROJ0_CLONING) {
        atomic_store_explicit(tag_ptr, SUP_TAG_BOTH, memory_order_release);
        SomaTask* task = (SomaTask*)sup->proj1;
        
        /* Wait for the clone task to complete and get result */
        SomaValue cloned = soma_par_run_task(task);
        sup->proj1 = (void*)cloned;
        return cloned;
    }

    /* Already accessed (PROJ1, PROJ1_CLONING, or BOTH) - return cached */
    return (SomaValue)sup->proj1;
}

/*
 * soma_era_free - Free a heap-allocated value (ERA node)
 *
 * Recursively frees the value and its children. After linearization,
 * every value is used exactly once, so when ERA fires we have exclusive
 * ownership - no reference counting needed.
 */
void soma_era_free(void* value) {
    if (value == NULL) return;
    
    uint8_t tag = *(uint8_t*)value;
    
    if (tag == NODE_CLOSURE) {
        SomaClosure* closure = (SomaClosure*)value;
        SomaValue* env = (SomaValue*)(closure + 1);
        
        /* Recursively free pointer-typed env slots */
        for (uint16_t i = 0; i < closure->env_size; i++) {
            if (SOMA_IS_PTR(env[i]) && env[i] != 0) {
                soma_era_free(SOMA_TO_PTR(env[i]));
            }
        }
        soma_pool_free_closure(value, closure->env_size);
        
    } else if (IS_SUP(tag)) {
        /* SUP being erased means it was never projected (in well-linearized code).
         * Just free the SUP node itself - cached projections should be NULL. */
        soma_pool_free_sup(value);
        
    } else {
        /* Unknown heap object - use regular free */
        free(value);
    }
}

/*
 * soma_alloc_closure - Allocate a closure with environment space
 */
void* soma_alloc_closure(void* func_ptr, uint8_t arity, uint16_t env_size) {
    SomaClosure* closure = (SomaClosure*)soma_pool_alloc_closure(env_size);

    closure->tag      = NODE_CLOSURE;
    closure->arity    = arity;
    closure->env_size = env_size;
    closure->func_ptr = func_ptr;

    return closure;
}

/*
 * soma_closure_set_env - Set a closure environment slot
 */
void soma_closure_set_env(void* closure_ptr, uint16_t index, SomaValue value) {
    SomaClosure* closure = (SomaClosure*)closure_ptr;
    SomaValue* env = (SomaValue*)(closure + 1);  /* env starts after header */
    env[index] = value;
}

/*
 * soma_closure_get_env - Get a closure environment slot
 */
SomaValue soma_closure_get_env(void* closure_ptr, uint16_t index) {
    SomaClosure* closure = (SomaClosure*)closure_ptr;
    SomaValue* env = (SomaValue*)(closure + 1);
    return env[index];
}

/*
 * soma_closure_get_func - Get function pointer from closure
 */
void* soma_closure_get_func(void* closure_ptr) {
    SomaClosure* closure = (SomaClosure*)closure_ptr;
    return closure->func_ptr;
}

/*
 * ============================================================================
 * SIMD-Optimized Bulk Operations
 * ============================================================================
 *
 * When cloning closures with many environment slots, SIMD can speed up
 * the copying. We use compiler intrinsics where available.
 */

#if defined(__AVX2__)
#include <immintrin.h>
#define SIMD_WIDTH 4  /* 4 x 64-bit = 256 bits */
#define HAS_SIMD 1
#elif defined(__SSE2__)
#include <emmintrin.h>
#define SIMD_WIDTH 2  /* 2 x 64-bit = 128 bits */
#define HAS_SIMD 1
#else
#define HAS_SIMD 0
#endif

/*
 * bulk_copy_env_slots - Copy environment slots with SIMD acceleration
 *
 * This copies slots that don't need SUP wrapping. For closure-typed slots,
 * the caller handles SUP wrapping after this bulk copy.
 */
static inline void bulk_copy_env_slots(SomaValue* dst, const SomaValue* src, uint16_t count) {
#if HAS_SIMD && defined(__AVX2__)
    /* AVX2: Process 4 slots at a time */
    uint16_t i = 0;
    for (; i + SIMD_WIDTH <= count; i += SIMD_WIDTH) {
        __m256i chunk = _mm256_loadu_si256((const __m256i*)(src + i));
        _mm256_storeu_si256((__m256i*)(dst + i), chunk);
    }
    /* Handle remaining slots */
    for (; i < count; i++) {
        dst[i] = src[i];
    }
#elif HAS_SIMD && defined(__SSE2__)
    /* SSE2: Process 2 slots at a time */
    uint16_t i = 0;
    for (; i + SIMD_WIDTH <= count; i += SIMD_WIDTH) {
        __m128i chunk = _mm_loadu_si128((const __m128i*)(src + i));
        _mm_storeu_si128((__m128i*)(dst + i), chunk);
    }
    /* Handle remaining slots */
    for (; i < count; i++) {
        dst[i] = src[i];
    }
#else
    /* Scalar fallback */
    for (uint16_t i = 0; i < count; i++) {
        dst[i] = src[i];
    }
#endif
}

/*
 * soma_clone_closure - Deep-clone a closure with HVM-style lazy nested cloning
 *
 * Copies the header and all environment slots. For slots that contain
 * closures or SUPs (detected at runtime via tag byte), wraps them in fresh
 * SUP nodes for lazy incremental cloning.
 *
 * This implements the DUP-LAM rule from HVM: when duplicating a closure,
 * nested closures become SUPs that are only fully cloned when both
 * projections are accessed.
 *
 * Optimizations:
 * - SIMD bulk copy for large environments
 * - Only wrap heap pointers to closures/SUPs, not primitives
 */
void* soma_clone_closure(void* closure_ptr) {
    SomaClosure* closure = (SomaClosure*)closure_ptr;
    uint16_t env_size = closure->env_size;

    /* Allocate new closure */
    void* new_closure = soma_pool_alloc_closure(env_size);
    
    /* Copy header (tag, arity, env_size, func_ptr) */
    memcpy(new_closure, closure, sizeof(SomaClosure));
    
    SomaValue* src_env = (SomaValue*)(closure + 1);
    SomaValue* dst_env = (SomaValue*)((SomaClosure*)new_closure + 1);
    
    /* For small environments, use scalar loop with SUP wrapping inline */
    if (env_size <= 8) {
        for (uint16_t i = 0; i < env_size; i++) {
            SomaValue val = src_env[i];
            
            /* Check if this is a heap pointer that might need lazy cloning */
            if (SOMA_IS_PTR(val) && val != 0) {
                uint8_t tag = *(uint8_t*)SOMA_TO_PTR(val);
                
                if (tag == NODE_CLOSURE || IS_SUP(tag)) {
                    /* Wrap in SUP for lazy nested cloning */
                    uint32_t fresh_label = soma_fresh_label();
                    void* sup = soma_dup(fresh_label, SOMA_TO_PTR(val));
                    dst_env[i] = SOMA_PTR(sup);
                    continue;
                }
            }
            
            /* Non-closure value: direct copy */
            dst_env[i] = val;
        }
    } else {
        /* For larger environments, bulk copy first then wrap closures */
        bulk_copy_env_slots(dst_env, src_env, env_size);
        
        /* Second pass: wrap closure/SUP slots in fresh SUPs */
        for (uint16_t i = 0; i < env_size; i++) {
            SomaValue val = src_env[i];
            
            if (SOMA_IS_PTR(val) && val != 0) {
                uint8_t tag = *(uint8_t*)SOMA_TO_PTR(val);
                
                if (tag == NODE_CLOSURE || IS_SUP(tag)) {
                    /* Wrap in SUP for lazy nested cloning */
                    uint32_t fresh_label = soma_fresh_label();
                    void* sup = soma_dup(fresh_label, SOMA_TO_PTR(val));
                    dst_env[i] = SOMA_PTR(sup);
                }
            }
        }
    }

    return new_closure;
}

/*
 * ============================================================================
 * Parallel Runtime Implementation
 * ============================================================================
 *
 * Work-stealing thread pool with demand-driven task spawning.
 * Key insight: only spawn parallel tasks when workers are hungry.
 *
 * Features:
 * - Per-thread memory pools (TLS)
 * - Adaptive spawning threshold based on worker hunger level
 * - Chase-Lev lock-free work-stealing deques
 */

#include <unistd.h>
#include <sched.h>

/* Global parallel runtime state */
SomaParRuntime soma_par = {0};
SomaParStats soma_par_stats = {0};

/* Thread-local current worker pointer */
__thread SomaWorker* soma_current_worker = NULL;

/*
 * ============================================================================
 * Adaptive Threshold Implementation
 * ============================================================================
 *
 * The work threshold for spawning tasks adapts based on worker hunger:
 * - If hungry count is small (< 25% of workers): workers are starving, 
 *   lower threshold to spawn more work
 * - If hungry count is high: workers are busy, raise threshold to be conservative
 * - Default threshold of 50 when parallelism is disabled or moderate hunger
 *
 * This prevents over-spawning when the system is already saturated and
 * ensures more aggressive spawning when workers need work.
 */

/* Adaptive threshold boundaries */
#define ADAPTIVE_THRESHOLD_MIN      10   /* Aggressive spawning when starving */
#define ADAPTIVE_THRESHOLD_DEFAULT  50   /* Normal operation */
#define ADAPTIVE_THRESHOLD_MAX      200  /* Conservative when busy */

/* Cached threshold to avoid recalculating on every call */
#define THRESHOLD_CACHE_INTERVAL 1000  /* Recalculate every 1000 calls */
static __thread uint32_t tls_cached_threshold = ADAPTIVE_THRESHOLD_DEFAULT;
static __thread uint32_t tls_threshold_call_count = 0;

static uint32_t compute_adaptive_threshold(void) {
    int num_workers = soma_par.num_workers;
    
    /* Count hungry workers by scanning per-worker flags */
    size_t hungry = 0;
    for (int i = 0; i < num_workers; i++) {
        if (atomic_load_explicit(&soma_par.workers[i].hungry, memory_order_relaxed)) {
            hungry++;
        }
    }
    
    if (num_workers == 0) {
        return ADAPTIVE_THRESHOLD_DEFAULT;
    }
    
    /* Calculate hunger ratio (0-100%) */
    int hunger_percent = (int)((hungry * 100) / (size_t)num_workers);
    
    /*
     * Adaptive logic:
     * - 75%+ hungry: workers are starving -> very low threshold (spawn aggressively)
     * - 50-75% hungry: moderate -> lower threshold
     * - 25-50% hungry: normal -> default threshold
     * - <25% hungry: workers are busy -> higher threshold (be conservative)
     */
    if (hunger_percent >= 75) {
        /* Starving: be very aggressive */
        return ADAPTIVE_THRESHOLD_MIN;
    } else if (hunger_percent >= 50) {
        /* Moderate hunger: lower threshold */
        return ADAPTIVE_THRESHOLD_MIN + 
               (ADAPTIVE_THRESHOLD_DEFAULT - ADAPTIVE_THRESHOLD_MIN) * 
               (75 - hunger_percent) / 25;
    } else if (hunger_percent >= 25) {
        /* Normal: use default */
        return ADAPTIVE_THRESHOLD_DEFAULT;
    } else {
        /* Busy: be conservative */
        return ADAPTIVE_THRESHOLD_DEFAULT + 
               (ADAPTIVE_THRESHOLD_MAX - ADAPTIVE_THRESHOLD_DEFAULT) * 
               (25 - hunger_percent) / 25;
    }
}

static inline uint32_t get_adaptive_threshold(void) {
    if (!soma_par_enabled()) {
        return ADAPTIVE_THRESHOLD_DEFAULT;
    }
    
    /* Use cached value most of the time */
    tls_threshold_call_count++;
    if (tls_threshold_call_count >= THRESHOLD_CACHE_INTERVAL) {
        tls_threshold_call_count = 0;
        tls_cached_threshold = compute_adaptive_threshold();
    }
    
    return tls_cached_threshold;
}

/*
 * Chase-Lev Deque Operations (lock-free work-stealing)
 *
 * Based on "Dynamic Circular Work-Stealing Deque" by Chase & Lev.
 * Owner pushes/pops from bottom (LIFO), thieves steal from top (FIFO).
 */

static void deque_init(SomaDeque* d) {
    atomic_store(&d->top, 0);
    atomic_store(&d->bottom, 0);
    for (int i = 0; i < SOMA_TASK_QUEUE_SIZE; i++) {
        atomic_store(&d->buffer[i], NULL);
    }
}

/* Push task onto bottom (owner only) */
static void deque_push(SomaDeque* d, SomaTask* task) {
    size_t b = atomic_load_explicit(&d->bottom, memory_order_relaxed);
    atomic_store_explicit(&d->buffer[b % SOMA_TASK_QUEUE_SIZE], task, memory_order_relaxed);
    atomic_thread_fence(memory_order_release);
    atomic_store_explicit(&d->bottom, b + 1, memory_order_relaxed);
}

/* Pop task from bottom (owner only) - returns NULL if empty */
static SomaTask* deque_pop(SomaDeque* d) {
    size_t b = atomic_load_explicit(&d->bottom, memory_order_relaxed) - 1;
    atomic_store_explicit(&d->bottom, b, memory_order_relaxed);
    atomic_thread_fence(memory_order_seq_cst);
    size_t t = atomic_load_explicit(&d->top, memory_order_relaxed);
    
    if (t <= b) {
        /* Non-empty */
        SomaTask* task = atomic_load_explicit(&d->buffer[b % SOMA_TASK_QUEUE_SIZE], 
                                               memory_order_relaxed);
        if (t == b) {
            /* Single element - need CAS to avoid race with steal */
            if (!atomic_compare_exchange_strong_explicit(
                    &d->top, &t, t + 1,
                    memory_order_seq_cst, memory_order_relaxed)) {
                /* Lost race to thief */
                task = NULL;
            }
            atomic_store_explicit(&d->bottom, b + 1, memory_order_relaxed);
        }
        return task;
    } else {
        /* Empty */
        atomic_store_explicit(&d->bottom, b + 1, memory_order_relaxed);
        return NULL;
    }
}

/* Steal task from top (thieves) - returns NULL if empty */
static SomaTask* deque_steal(SomaDeque* d) {
    size_t t = atomic_load_explicit(&d->top, memory_order_acquire);
    atomic_thread_fence(memory_order_seq_cst);
    size_t b = atomic_load_explicit(&d->bottom, memory_order_acquire);
    
    if (t < b) {
        /* Non-empty */
        SomaTask* task = atomic_load_explicit(&d->buffer[t % SOMA_TASK_QUEUE_SIZE],
                                               memory_order_relaxed);
        if (!atomic_compare_exchange_strong_explicit(
                &d->top, &t, t + 1,
                memory_order_seq_cst, memory_order_relaxed)) {
            /* Lost race */
            return NULL;
        }
        return task;
    }
    return NULL;
}

/*
 * Task Pool (simple free-list for task recycling)
 */

/* Use larger pool from header, or default to 65536 for massive parallelism */
#ifndef TASK_POOL_INITIAL_SIZE
#define TASK_POOL_INITIAL_SIZE SOMA_TASK_POOL_SIZE
#endif

/* Per-worker task free lists for lock-free allocation */
#define WORKER_POOL_SIZE 256
#define BATCH_ALLOC_SIZE 64  /* Grab 64 tasks at once from global array */

typedef struct {
    SomaTask* free_list;
    int count;
    /* Local batch from global array */
    SomaTask* batch_start;
    SomaTask* batch_end;
    SomaTask* batch_current;
} WorkerTaskPool;

static __thread WorkerTaskPool tls_task_pool = {NULL, 0, NULL, NULL, NULL};

/* Pre-allocated global task array for initial pool */
static SomaTask* global_task_array = NULL;
static _Atomic size_t global_task_index = 0;
static size_t global_task_capacity = 0;

SomaTask* soma_task_alloc(void) {
    /* Try thread-local free list first - no locks! */
    if (tls_task_pool.free_list != NULL) {
        SomaTask* task = tls_task_pool.free_list;
        tls_task_pool.free_list = *(SomaTask**)task;
        tls_task_pool.count--;
        return task;
    }
    
    /* Try local batch from global array - no atomics! */
    if (tls_task_pool.batch_current != NULL && 
        tls_task_pool.batch_current < tls_task_pool.batch_end) {
        SomaTask* task = tls_task_pool.batch_current;
        tls_task_pool.batch_current++;
        return task;
    }
    
    /* Grab a new batch from global array - one atomic for BATCH_ALLOC_SIZE tasks */
    if (global_task_array != NULL) {
        size_t idx = atomic_fetch_add(&global_task_index, BATCH_ALLOC_SIZE);
        if (idx + BATCH_ALLOC_SIZE <= global_task_capacity) {
            /* Got a full batch */
            tls_task_pool.batch_start = &global_task_array[idx];
            tls_task_pool.batch_end = &global_task_array[idx + BATCH_ALLOC_SIZE];
            tls_task_pool.batch_current = tls_task_pool.batch_start + 1;
            return tls_task_pool.batch_start;
        } else if (idx < global_task_capacity) {
            /* Partial batch at end of array */
            tls_task_pool.batch_start = &global_task_array[idx];
            tls_task_pool.batch_end = &global_task_array[global_task_capacity];
            tls_task_pool.batch_current = tls_task_pool.batch_start + 1;
            return tls_task_pool.batch_start;
        }
    }
    
    /* Fall back to global pool with lock (rare path) */
    pthread_mutex_lock(&soma_par.task_pool_lock);
    if (soma_par.task_pool != NULL) {
        SomaTask* task = soma_par.task_pool;
        soma_par.task_pool = *(SomaTask**)task;
        pthread_mutex_unlock(&soma_par.task_pool_lock);
        return task;
    }
    pthread_mutex_unlock(&soma_par.task_pool_lock);
    
    /* Allocate new */
    return (SomaTask*)malloc(sizeof(SomaTask));
}

void soma_task_free(SomaTask* task) {
    /* Check if task is from global array - don't free those, they're reused via index */
    if (global_task_array != NULL && 
        task >= global_task_array && 
        task < global_task_array + global_task_capacity) {
        /* From global array - add to thread-local pool for fast reuse */
        if (tls_task_pool.count < WORKER_POOL_SIZE) {
            *(SomaTask**)task = tls_task_pool.free_list;
            tls_task_pool.free_list = task;
            tls_task_pool.count++;
            return;
        }
        /* TLS pool full - return to global pool */
    }
    
    /* Return to global pool */
    pthread_mutex_lock(&soma_par.task_pool_lock);
    *(SomaTask**)task = soma_par.task_pool;
    soma_par.task_pool = task;
    pthread_mutex_unlock(&soma_par.task_pool_lock);
}

/*
 * Task Execution Helper
 */

/* Thread-local fork depth - declared later but needed here */
extern __thread uint8_t soma_fork_depth;

static inline SomaValue task_execute(SomaTask* task) {
    /* Set thread-local fork depth from task's depth.
     * This allows nested forks to know their depth in the fork tree. */
    uint8_t saved_depth = soma_fork_depth;
    soma_fork_depth = task->depth;
    
    SomaValue result;
    switch (task->kind) {
        case TASK_KIND_DIRECT:
            result = task->fn.direct(task->arg);
            break;
        case TASK_KIND_CLOSURE:
            result = task->fn.closure(task->env, task->arg);
            break;
        case TASK_KIND_TRAMPOLINE: {
            /* Trampoline call: the trampoline function handles type conversion.
             * The trampoline takes a pointer to the args array and returns SomaValue.
             * This is safe because the compiler generates the trampoline with the
             * correct argument unpacking and type conversions. */
            SomaValue* args = task->args_inline ? task->inline_args : (SomaValue*)task->env;
            result = task->fn.trampoline(args);
            
            /* Free heap-allocated args array if not inline */
            if (!task->args_inline && task->env != NULL) {
                free(task->env);
            }
            break;
        }
        case TASK_KIND_GENERIC:
        default:
            result = task->fn.generic(task->env);
            break;
    }
    
    /* Restore previous depth */
    soma_fork_depth = saved_depth;
    return result;
}

/*
 * Worker Thread
 */

/* Hungry state tracking - per-worker flag only, no global counter.
 * 
 * Each worker has its own hungry flag on its own cache line.
 * No global counter means no cache-line ping-pong between workers.
 * Spawning decisions scan per-worker flags directly.
 */
static inline void worker_set_hungry(SomaWorker* w, int hungry) {
    atomic_store_explicit(&w->hungry, hungry, memory_order_relaxed);
}

static void* worker_main(void* arg) {
    SomaWorker* self = (SomaWorker*)arg;
    soma_current_worker = self;
    
    /* Initialize per-thread memory pools */
    tls_pool_init();
    
    /* Exponential backoff state for failed steals */
    int backoff = 0;
    const int BACKOFF_MIN = 1;
    const int BACKOFF_MAX = 64;
    
    while (!atomic_load(&soma_par.shutdown)) {
        /* Try to pop from own deque first */
        SomaTask* task = deque_pop(&self->deque);
        
        if (task == NULL) {
            /* Mark as hungry and try to steal */
            worker_set_hungry(self, 1);
            
            /* First, try stealing from main thread's deque (most likely to have work) */
            task = deque_steal(&soma_par.main_deque);
            self->steal_attempts++;
            
            if (task == NULL) {
                /* Try stealing from ONE random victim, not all */
                int victim_id = (self->id + backoff) % soma_par.num_workers;
                if (victim_id == self->id) {
                    victim_id = (victim_id + 1) % soma_par.num_workers;
                }
                
                SomaWorker* victim = &soma_par.workers[victim_id];
                task = deque_steal(&victim->deque);
                self->steal_attempts++;
            }
            
            if (task != NULL) {
                /* Found work - reset backoff */
                self->tasks_stolen++;
                atomic_fetch_add(&soma_par_stats.tasks_stolen, 1);
                worker_set_hungry(self, 0);
                backoff = 0;
            } else {
                /* No work - exponential backoff before next steal attempt */
                if (backoff < BACKOFF_MIN) {
                    backoff = BACKOFF_MIN;
                } else if (backoff < BACKOFF_MAX) {
                    backoff *= 2;
                }
                
                /* Spin-wait with backoff instead of immediate retry */
                for (int i = 0; i < backoff; i++) {
#if defined(__x86_64__) || defined(__i386__)
                    __asm__ volatile("pause" ::: "memory");
#elif defined(__aarch64__)
                    __asm__ volatile("yield" ::: "memory");
#else
                    /* Generic: compiler barrier */
                    __asm__ volatile("" ::: "memory");
#endif
                }
                
                /* Occasionally yield to OS after many failed attempts */
                if (backoff >= BACKOFF_MAX) {
                    sched_yield();
                }
                continue;
            }
        } else {
            worker_set_hungry(self, 0);
            backoff = 0;  /* Reset backoff on successful pop */
        }
        
        /* Execute the task */
        int expected = TASK_PENDING;
        if (atomic_compare_exchange_strong(&task->state, &expected, TASK_RUNNING)) {
            task->result = task_execute(task);
            atomic_store(&task->state, TASK_DONE);
            atomic_fetch_sub(&soma_par.pending_tasks, 1);
            self->tasks_run++;
            atomic_fetch_add(&soma_par_stats.tasks_run, 1);
        }
    }
    
    /* Cleanup per-thread pools */
    tls_pool_cleanup();
    
    return NULL;
}

/*
 * Runtime Lifecycle
 */

void soma_par_init(int num_workers) {
    if (num_workers <= 0) {
        /* Auto-detect: use number of online CPUs - 1 (main thread counts) */
        num_workers = (int)sysconf(_SC_NPROCESSORS_ONLN) - 1;
        if (num_workers < 1) num_workers = 1;
    }
    if (num_workers > SOMA_MAX_WORKERS) {
        num_workers = SOMA_MAX_WORKERS;
    }
    
    soma_par.num_workers = num_workers;
    atomic_store(&soma_par.shutdown, 0);
    atomic_store(&soma_par.pending_tasks, 0);
    /* hungry_count removed - using per-worker flags instead */
    soma_par.task_pool = NULL;
    pthread_mutex_init(&soma_par.task_pool_lock, NULL);
    
    /* Initialize main thread's deque */
    deque_init(&soma_par.main_deque);
    
    /* Pre-allocate global task array for lock-free allocation */
    global_task_capacity = TASK_POOL_INITIAL_SIZE;
    global_task_array = (SomaTask*)calloc(global_task_capacity, sizeof(SomaTask));
    atomic_store(&global_task_index, 0);
    
    /* Start worker threads with larger stack for deep recursion */
    pthread_attr_t attr;
    pthread_attr_init(&attr);
    /* 512KB stack per worker thread */
    pthread_attr_setstacksize(&attr, 512 * 1024);
    
    for (int i = 0; i < num_workers; i++) {
        SomaWorker* w = &soma_par.workers[i];
        w->id = i;
        w->runtime = &soma_par;
        atomic_store(&w->active, 1);
        atomic_store(&w->hungry, 0);
        w->tasks_run = 0;
        w->tasks_stolen = 0;
        w->steal_attempts = 0;
        deque_init(&w->deque);
        pthread_create(&w->thread, &attr, worker_main, w);
    }
    
    pthread_attr_destroy(&attr);
}

void soma_par_shutdown(void) {
    if (soma_par.num_workers == 0) return;
    
    /* Signal shutdown */
    atomic_store(&soma_par.shutdown, 1);
    
    /* Join all workers */
    for (int i = 0; i < soma_par.num_workers; i++) {
        pthread_join(soma_par.workers[i].thread, NULL);
    }
    
    /* Free global task array */
    if (global_task_array != NULL) {
        free(global_task_array);
        global_task_array = NULL;
        global_task_capacity = 0;
    }
    
    /* Free overflow task pool */
    pthread_mutex_lock(&soma_par.task_pool_lock);
    while (soma_par.task_pool != NULL) {
        SomaTask* next = *(SomaTask**)soma_par.task_pool;
        free(soma_par.task_pool);
        soma_par.task_pool = next;
    }
    pthread_mutex_unlock(&soma_par.task_pool_lock);
    pthread_mutex_destroy(&soma_par.task_pool_lock);
    
    soma_par.num_workers = 0;
}

/*
 * Task Spawning
 */

void soma_par_spawn(SomaTask* task) {
    SomaWorker* w = soma_current_worker;
    
    atomic_store(&task->state, TASK_PENDING);
    atomic_fetch_add(&soma_par.pending_tasks, 1);
    atomic_fetch_add(&soma_par_stats.tasks_spawned, 1);
    
    if (w != NULL) {
        /* Push to current worker's deque */
        deque_push(&w->deque, task);
    } else {
        /* Main thread: push to main thread's own deque.
         * Workers will steal from this deque. */
        deque_push(&soma_par.main_deque, task);
    }
}

SomaTask* soma_par_pop(SomaWorker* worker) {
    return deque_pop(&worker->deque);
}

SomaTask* soma_par_steal(SomaWorker* thief, SomaWorker* victim) {
    (void)thief;  /* Unused - thief identity not needed for basic stealing */
    return deque_steal(&victim->deque);
}

SomaValue soma_par_run_task(SomaTask* task) {
    int expected = TASK_PENDING;
    if (atomic_compare_exchange_strong(&task->state, &expected, TASK_RUNNING)) {
        task->result = task_execute(task);
        atomic_store(&task->state, TASK_DONE);
        atomic_fetch_sub(&soma_par.pending_tasks, 1);
        return task->result;
    }
    
    /* Task was stolen or already running - wait for completion */
    while (atomic_load(&task->state) != TASK_DONE) {
        sched_yield();
    }
    return task->result;
}

/*
 * Fork-Join Parallelism
 *
 * Structured parallelism for independent computations.
 * Zero overhead when parallel runtime is not enabled.
 */

SomaTask* soma_fork(SomaTaskFn fn, void* env) {
    /* If parallel runtime not enabled, return NULL - caller should check */
    if (!soma_par_enabled()) {
        return NULL;
    }
    
    SomaTask* task = soma_task_alloc();
    if (!task) {
        return NULL;
    }
    
    task->kind = TASK_KIND_GENERIC;
    task->fn.generic = fn;
    task->env = env;
    task->arg = 0;
    task->work_estimate = 0;
    task->result = 0;
    
    soma_par_spawn(task);
    /* Note: tasks_spawned is incremented in soma_par_spawn */
    
    return task;
}

/* Non-inline wrapper for soma_par_enabled - callable from LLVM generated code */
int soma_par_enabled_export(void) {
    return soma_par_enabled();
}

SomaTask* soma_fork_direct(SomaDirectFn fn, SomaValue arg) {
    /* If parallel runtime not enabled, return NULL - caller should execute inline */
    if (!soma_par_enabled()) {
        return NULL;
    }
    
    int worker_id = soma_current_worker ? soma_current_worker->id : -1;
    uint8_t current_depth = soma_fork_depth;
    
    /* DEPTH-LIMITED NESTED FORKING:
     * Allow forking up to depth limit to enable exponential parallelism. */
    if (current_depth >= SOMA_MAX_FORK_DEPTH) {
        DEBUG_PRINT("[fork_direct] worker=%d depth=%d SKIPPING fork (depth limit)\n", 
                    worker_id, current_depth);
        return NULL;
    }
    
    SomaTask* task = soma_task_alloc();
    if (!task) {
        return NULL;
    }
    
    task->kind = TASK_KIND_DIRECT;
    task->fn.direct = fn;
    task->env = NULL;
    task->arg = arg;
    task->work_estimate = 0;
    task->result = 0;
    task->depth = current_depth + 1;  /* Child task is one level deeper */
    
    soma_par_spawn(task);
    /* Note: tasks_spawned is incremented in soma_par_spawn */
    
    return task;
}

SomaTask* soma_fork_closure(SomaClosureFn fn, void* closure, SomaValue arg) {
    /* If parallel runtime not enabled, return NULL - caller should execute inline */
    if (!soma_par_enabled()) {
        return NULL;
    }
    
    SomaTask* task = soma_task_alloc();
    if (!task) {
        return NULL;
    }
    
    task->kind = TASK_KIND_CLOSURE;
    task->fn.closure = fn;
    task->env = closure;
    task->arg = arg;
    task->work_estimate = 0;
    task->result = 0;
    
    soma_par_spawn(task);
    /* Note: tasks_spawned is incremented in soma_par_spawn */
    
    return task;
}

SomaTask* soma_fork_multi(void* fn, SomaValue* args, int num_args) {
    /* If parallel runtime not enabled, return NULL - caller should execute inline */
    if (!soma_par_enabled()) {
        return NULL;
    }
    
    int is_worker_thread = (soma_current_worker != NULL);
    int worker_id = is_worker_thread ? soma_current_worker->id : -1;
    uint8_t current_depth = soma_fork_depth;
    
    /* DEPTH-LIMITED NESTED FORKING:
     * Allow both main thread and workers to fork, but only up to a depth limit.
     * This enables exponential parallelism (2^depth tasks) while preventing
     * stack overflow by falling back to sequential execution at deep levels.
     * 
     * At depth 30, we can have up to ~1 billion parallel tasks. */
    if (current_depth >= SOMA_MAX_FORK_DEPTH) {
        DEBUG_PRINT("[fork_multi] worker=%d depth=%d SKIPPING fork (depth limit)\n", 
                    worker_id, current_depth);
        return NULL;  /* Caller will execute inline */
    }
    
    DEBUG_PRINT("[fork_multi] worker=%d depth=%d fn=%p num_args=%d\n", 
                worker_id, current_depth, fn, num_args);
    
    SomaTask* task = soma_task_alloc();
    if (!task) {
        return NULL;
    }
    
    /* Store args - use inline storage if possible to avoid malloc */
    task->num_args = (uint8_t)num_args;
    if (num_args <= SOMA_TASK_INLINE_ARGS) {
        /* Use inline storage - no malloc! */
        memcpy(task->inline_args, args, num_args * sizeof(SomaValue));
        task->args_inline = 1;
        task->env = NULL;
    } else {
        /* Too many args - fall back to heap allocation */
        SomaValue* args_copy = (SomaValue*)malloc(num_args * sizeof(SomaValue));
        if (!args_copy) {
            soma_task_free(task);
            return NULL;
        }
        memcpy(args_copy, args, num_args * sizeof(SomaValue));
        task->env = args_copy;
        task->args_inline = 0;
    }
    
    /* fn is now a trampoline function that takes a pointer to the args array.
     * The trampoline handles all type conversions (i64 -> native types) and
     * calls the real function with the correct argument types. */
    task->kind = TASK_KIND_TRAMPOLINE;
    task->fn.trampoline = (SomaTrampolineFn)fn;
    task->work_estimate = 0;
    task->result = 0;
    task->depth = current_depth + 1;  /* Child task is one level deeper */
    
    soma_par_spawn(task);
    
    DEBUG_PRINT("[fork_multi] worker=%d depth=%d spawned task=%p pending=%zu\n", 
                worker_id, current_depth, (void*)task, atomic_load(&soma_par.pending_tasks));
    
    return task;
}

/* Thread-local inline execution depth counter to prevent stack overflow */
__thread int soma_join_depth = 0;

/* Thread-local fork depth for depth-limited nested forking */
__thread uint8_t soma_fork_depth = 0;

/* Maximum inline execution depth for worker threads (main thread has no limit) */
#define SOMA_MAX_WORKER_JOIN_DEPTH 8

SomaValue soma_join(SomaTask* task) {
    /* If task is NULL, the computation was run inline (sequential mode) */
    if (task == NULL) {
        /* This shouldn't happen in normal use - caller should have
         * run the computation directly when soma_fork returned NULL */
        return 0;
    }
    
    SomaValue result;
    int state = atomic_load(&task->state);
    
    /* Check if we're on a worker thread or the main thread. */
    int is_worker_thread = (soma_current_worker != NULL);
    int worker_id = is_worker_thread ? soma_current_worker->id : -1;
    
    DEBUG_PRINT("[join] worker=%d depth=%d state=%d task=%p\n", 
                worker_id, soma_join_depth, state, (void*)task);
    
    if (state == TASK_PENDING) {
        /* Task hasn't started yet - give workers a brief chance to steal it. */
        for (int i = 0; i < 100; i++) {
            sched_yield();
            state = atomic_load(&task->state);
            if (state != TASK_PENDING) break;
        }
        
        DEBUG_PRINT("[join] worker=%d after yield state=%d\n", worker_id, state);
        
        /* If still pending and we're allowed to execute inline, do so.
         * Workers should execute inline to make progress.
         * Main thread only executes inline if workers aren't picking up work. */
        if (state == TASK_PENDING) {
            int expected = TASK_PENDING;
            if (atomic_compare_exchange_strong(&task->state, &expected, TASK_RUNNING)) {
                DEBUG_PRINT("[join] worker=%d executing inline depth=%d\n", worker_id, soma_join_depth);
                soma_join_depth++;
                task->result = task_execute(task);
                soma_join_depth--;
                atomic_store(&task->state, TASK_DONE);
                atomic_fetch_sub(&soma_par.pending_tasks, 1);
                atomic_fetch_add(&soma_par_stats.tasks_run_inline, 1);
                result = task->result;
                soma_task_free(task);
                DEBUG_PRINT("[join] worker=%d inline done result=%ld\n", worker_id, (long)result);
                return result;
            }
        }
    }
    
    /* Wait for task to complete (task was stolen or already running) */
    DEBUG_PRINT("[join] worker=%d waiting for task=%p state=%d\n", worker_id, (void*)task, atomic_load(&task->state));
    int wait_count = 0;
    while (atomic_load(&task->state) != TASK_DONE) {
        sched_yield();
        wait_count++;
        if (wait_count % 10000 == 0) {
            DEBUG_PRINT("[join] worker=%d still waiting count=%d state=%d pending=%zu\n", 
                        worker_id, wait_count, atomic_load(&task->state),
                        atomic_load(&soma_par.pending_tasks));
        }
    }
    
    result = task->result;
    soma_task_free(task);
    DEBUG_PRINT("[join] worker=%d wait done result=%ld\n", worker_id, (long)result);
    return result;
}

/*
 * Parallel SUP Projection with Speculative Cloning
 *
 * These functions are parallel-aware wrappers around soma_proj0/1.
 * When the first projection happens on a SUP containing a closure:
 * - If workers are hungry and the work estimate is high enough
 * - Speculatively spawn a task to clone the closure in the background
 * - The second projection can then use the pre-cloned value
 *
 * This overlaps cloning work with other computation, reducing latency.
 *
 * Uses adaptive threshold based on worker hunger level.
 */

/* Task function for speculative closure cloning */
static SomaValue soma_clone_task_fn(void* env) {
    void* closure_ptr = env;
    void* cloned = soma_clone_closure(closure_ptr);
    return SOMA_PTR(cloned);
}

/* Check if speculative cloning should be attempted (with adaptive threshold) */
static int should_speculative_clone(uint32_t work_hint, SomaValue value) {
    if (!soma_par_enabled()) return 0;
    
    /* Must be a closure to clone */
    if (!SOMA_IS_PTR(value) || value == 0) return 0;
    if (!is_heap_closure(value)) return 0;
    
    /* Check work threshold (adaptive) */
    uint32_t threshold = get_adaptive_threshold();
    uint32_t work = work_hint;
    SomaClosure* closure = (SomaClosure*)SOMA_TO_PTR(value);
    uint32_t runtime_est = closure->env_size * 10;  /* Estimate based on env size */
    if (runtime_est > work) work = runtime_est;
    
    if (work < threshold) {
        atomic_fetch_add(&soma_par_stats.spawn_skipped_trivial, 1);
        return 0;
    }
    
    /* Check if workers are hungry (redundant with adaptive, but explicit check) */
    if (!soma_par_workers_hungry()) {
        atomic_fetch_add(&soma_par_stats.spawn_skipped_no_hungry, 1);
        return 0;
    }
    
    /* Check if task queue is saturated */
    if (atomic_load(&soma_par.pending_tasks) >= SOMA_MAX_PENDING_TASKS) {
        atomic_fetch_add(&soma_par_stats.spawn_skipped_saturated, 1);
        return 0;
    }
    
    return 1;
}

SomaValue soma_par_proj0(SomaValue sup_val, uint32_t work_hint) {
    if (!SOMA_IS_PTR(sup_val) || sup_val == 0) {
        return soma_proj0(sup_val);
    }
    
    SomaSup* sup = (SomaSup*)SOMA_TO_PTR(sup_val);
    _Atomic uint8_t* tag_ptr = (_Atomic uint8_t*)&sup->tag;
    
    /* Single atomic load - HVM3 style */
    uint8_t tag = atomic_load_explicit(tag_ptr, memory_order_acquire);
    
    /* Only handle fresh SUPs for speculative cloning */
    if (tag != SUP_TAG_FRESH) {
        return soma_proj0(sup_val);
    }
    
    /* Atomic CAS to claim this SUP - prevents race with proj1 */
    uint8_t expected = SUP_TAG_FRESH;
    SomaValue value = (SomaValue)sup->value;
    
    /* Check for annihilation first */
    if (is_heap_sup(value)) {
        SomaSup* inner = (SomaSup*)SOMA_TO_PTR(value);
        if (inner->label == sup->label) {
            /* Annihilate: try to claim with CAS */
            if (atomic_compare_exchange_strong_explicit(tag_ptr, &expected, SUP_TAG_PROJ0,
                                                         memory_order_acq_rel, memory_order_acquire)) {
                sup->proj0 = inner->value;
                return (SomaValue)inner->value;
            }
            /* Lost race - fall through to regular proj0 */
            return soma_proj0(sup_val);
        }
    }
    
    /* Check if we should speculatively clone for proj1 */
    if (should_speculative_clone(work_hint, value)) {
        /* Try to claim with CAS for speculative cloning */
        if (atomic_compare_exchange_strong_explicit(tag_ptr, &expected, SUP_TAG_PROJ0_CLONING,
                                                     memory_order_acq_rel, memory_order_acquire)) {
            /* Spawn a clone task - result will go in proj1 */
            SomaTask* task = soma_task_alloc();
            if (task) {
                task->kind = TASK_KIND_GENERIC;
                task->fn.generic = soma_clone_task_fn;
                task->env = SOMA_TO_PTR(value);
                task->arg = 0;
                task->work_estimate = work_hint;
                
                /* Store task pointer in proj1 slot temporarily */
                sup->proj1 = task;
                sup->proj0 = (void*)value;
                
                /* Spawn the task */
                soma_par_spawn(task);
                atomic_fetch_add(&soma_par_stats.speculative_clones, 1);
                
                return value;
            }
            /* Task alloc failed - downgrade to normal PROJ0 */
            atomic_store_explicit(tag_ptr, SUP_TAG_PROJ0, memory_order_release);
            sup->proj0 = (void*)value;
            return value;
        }
        /* Lost race - fall through to regular proj0 */
        return soma_proj0(sup_val);
    }
    
    /* Normal path: try to claim with CAS */
    if (atomic_compare_exchange_strong_explicit(tag_ptr, &expected, SUP_TAG_PROJ0,
                                                 memory_order_acq_rel, memory_order_acquire)) {
        sup->proj0 = (void*)value;
        return value;
    }
    
    /* Lost race - fall through to regular proj0 */
    return soma_proj0(sup_val);
}

SomaValue soma_par_proj1(SomaValue sup_val, uint32_t work_hint) {
    if (!SOMA_IS_PTR(sup_val) || sup_val == 0) {
        return soma_proj1(sup_val);
    }
    
    SomaSup* sup = (SomaSup*)SOMA_TO_PTR(sup_val);
    _Atomic uint8_t* tag_ptr = (_Atomic uint8_t*)&sup->tag;
    
    /* Single atomic load - HVM3 style */
    uint8_t tag = atomic_load_explicit(tag_ptr, memory_order_acquire);
    
    /* Only handle fresh SUPs for speculative cloning */
    if (tag != SUP_TAG_FRESH) {
        return soma_proj1(sup_val);
    }
    
    /* Atomic CAS to claim this SUP - prevents race with proj0 */
    uint8_t expected = SUP_TAG_FRESH;
    SomaValue value = (SomaValue)sup->value;
    
    /* Check for annihilation first */
    if (is_heap_sup(value)) {
        SomaSup* inner = (SomaSup*)SOMA_TO_PTR(value);
        if (inner->label == sup->label) {
            /* Annihilate: try to claim with CAS */
            if (atomic_compare_exchange_strong_explicit(tag_ptr, &expected, SUP_TAG_PROJ1,
                                                         memory_order_acq_rel, memory_order_acquire)) {
                sup->proj1 = inner->value;
                return (SomaValue)inner->value;
            }
            /* Lost race - fall through to regular proj1 */
            return soma_proj1(sup_val);
        }
    }
    
    /* Check if we should speculatively clone for proj0 */
    if (should_speculative_clone(work_hint, value)) {
        /* Try to claim with CAS for speculative cloning */
        if (atomic_compare_exchange_strong_explicit(tag_ptr, &expected, SUP_TAG_PROJ1_CLONING,
                                                     memory_order_acq_rel, memory_order_acquire)) {
            /* Spawn a clone task - result will go in proj0 */
            SomaTask* task = soma_task_alloc();
            if (task) {
                task->kind = TASK_KIND_GENERIC;
                task->fn.generic = soma_clone_task_fn;
                task->env = SOMA_TO_PTR(value);
                task->arg = 0;
                task->work_estimate = work_hint;
                
                /* Store task pointer in proj0 slot temporarily */
                sup->proj0 = task;
                sup->proj1 = (void*)value;
                
                /* Spawn the task */
                soma_par_spawn(task);
                atomic_fetch_add(&soma_par_stats.speculative_clones, 1);
                
                return value;
            }
            /* Task alloc failed - downgrade to normal PROJ1 */
            atomic_store_explicit(tag_ptr, SUP_TAG_PROJ1, memory_order_release);
            sup->proj1 = (void*)value;
            return value;
        }
        /* Lost race - fall through to regular proj1 */
        return soma_proj1(sup_val);
    }
    
    /* Normal path: try to claim with CAS */
    if (atomic_compare_exchange_strong_explicit(tag_ptr, &expected, SUP_TAG_PROJ1,
                                                 memory_order_acq_rel, memory_order_acquire)) {
        sup->proj1 = (void*)value;
        return value;
    }
    
    /* Lost race - fall through to regular proj1 */
    return soma_proj1(sup_val);
}

/*
 * Statistics
 */

void soma_par_print_stats(void) {
    if (!soma_par_enabled()) {
        fprintf(stderr, "[soma_par] Parallel runtime not enabled\n");
        return;
    }
    
    fprintf(stderr, "[soma_par] Workers: %d\n", soma_par.num_workers);
    fprintf(stderr, "[soma_par] Tasks spawned: %lu\n", (unsigned long)atomic_load(&soma_par_stats.tasks_spawned));
    fprintf(stderr, "[soma_par] Tasks run (workers): %lu\n", (unsigned long)atomic_load(&soma_par_stats.tasks_run));
    fprintf(stderr, "[soma_par] Tasks run (inline): %lu\n", (unsigned long)atomic_load(&soma_par_stats.tasks_run_inline));
    fprintf(stderr, "[soma_par] Tasks stolen: %lu\n", (unsigned long)atomic_load(&soma_par_stats.tasks_stolen));
    fprintf(stderr, "[soma_par] Speculative clones: %lu\n", (unsigned long)atomic_load(&soma_par_stats.speculative_clones));
    fprintf(stderr, "[soma_par] Skipped (trivial): %lu\n", (unsigned long)atomic_load(&soma_par_stats.spawn_skipped_trivial));
    fprintf(stderr, "[soma_par] Skipped (not hungry): %lu\n", (unsigned long)atomic_load(&soma_par_stats.spawn_skipped_no_hungry));
    fprintf(stderr, "[soma_par] Skipped (saturated): %lu\n", (unsigned long)atomic_load(&soma_par_stats.spawn_skipped_saturated));
    fprintf(stderr, "[soma_par] Current adaptive threshold: %u\n", get_adaptive_threshold());
    
    /* Count hungry workers by scanning per-worker flags */
    int hungry_count = 0;
    for (int i = 0; i < soma_par.num_workers; i++) {
        if (atomic_load_explicit(&soma_par.workers[i].hungry, memory_order_relaxed)) {
            hungry_count++;
        }
    }
    fprintf(stderr, "[soma_par] Current hungry workers: %d/%d\n", 
            hungry_count, soma_par.num_workers);
    
    for (int i = 0; i < soma_par.num_workers; i++) {
        SomaWorker* w = &soma_par.workers[i];
        fprintf(stderr, "[soma_par] Worker %d: run=%lu stolen=%lu attempts=%lu\n",
                i, (unsigned long)w->tasks_run, (unsigned long)w->tasks_stolen, 
                (unsigned long)w->steal_attempts);
    }
    
    /* Pool stats */
    fprintf(stderr, "[soma_pool] SUP allocs: %lu, frees: %lu\n",
            (unsigned long)atomic_load(&soma_pool_stats.sup_allocs),
            (unsigned long)atomic_load(&soma_pool_stats.sup_frees));
    fprintf(stderr, "[soma_pool] Closure small: %lu/%lu, medium: %lu/%lu, large: %lu/%lu\n",
            (unsigned long)atomic_load(&soma_pool_stats.closure_small_allocs),
            (unsigned long)atomic_load(&soma_pool_stats.closure_small_frees),
            (unsigned long)atomic_load(&soma_pool_stats.closure_medium_allocs),
            (unsigned long)atomic_load(&soma_pool_stats.closure_medium_frees),
            (unsigned long)atomic_load(&soma_pool_stats.closure_large_allocs),
            (unsigned long)atomic_load(&soma_pool_stats.closure_large_frees));
    fprintf(stderr, "[soma_pool] Blocks allocated: %lu, bytes: %lu\n",
            (unsigned long)atomic_load(&soma_pool_stats.blocks_allocated),
            (unsigned long)atomic_load(&soma_pool_stats.bytes_allocated));
}

/*
 * Panic function - prints error message and aborts
 */
void soma_panic(const char* msg) {
    fprintf(stderr, "PANIC: %s\n", msg);
    soma_pool_cleanup();
    exit(1);
}

/*
 * Main entry point - wraps the user's soma_main function
 *
 * The compiler renames the user's `main` to `soma_main`, and this
 * function provides the actual entry point with proper initialization.
 */
extern int soma_main(void);

int main(void) {
    soma_pool_init();
    
    /* Initialize parallel runtime if SOMA_PARALLEL env var is set */
    const char* par_env = getenv("SOMA_PARALLEL");
    if (par_env != NULL) {
        int num_workers = atoi(par_env);
        soma_par_init(num_workers);
    }
    
    int result = soma_main();
    
    /* Print stats if SOMA_PAR_STATS is set */
    if (getenv("SOMA_PAR_STATS") != NULL) {
        soma_par_print_stats();
    }
    
    soma_par_shutdown();
    soma_pool_cleanup();
    return result;
}
