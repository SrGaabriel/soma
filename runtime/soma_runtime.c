#include "soma_runtime.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

#ifdef _WIN32
#include <windows.h>
#endif

#ifndef _WIN32
#include <unistd.h>
#endif

#include <sched.h>

/* Global memory pools */
SomaPools soma_pools;

#ifdef SOMA_POOL_STATS
SomaPoolStats soma_pool_stats;
#endif


/*
 * ============================================================================
 * Size-Class Pool Allocator (TLS)
 * ============================================================================
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
        SOMA_STAT_INC(blocks_allocated);
        SOMA_STAT_ADD(bytes_allocated, sizeof(SomaPoolBlock) + POOL_BLOCK_SIZE);
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
static inline void* pool_alloc(SomaPool* pool) {
    /* Check free list first */
    if (pool->free_list != NULL) {
        void* ptr = pool->free_list;
        pool->free_list = *(void**)ptr;
        return ptr;
    }

    /* Try current block */
    SomaPoolBlock* block = pool->blocks;
    const size_t item_size = pool->item_size;
    if (block->used + item_size <= POOL_BLOCK_SIZE) {
        void* ptr = block->data + block->used;
        block->used += item_size;
        return ptr;
    }

    /* Need new block */
    SomaPoolBlock* new_block = pool_alloc_block();
    if (!new_block) {
        return NULL;
    }
    new_block->next = pool->blocks;
    pool->blocks = new_block;

    void* ptr = new_block->data;
    new_block->used = item_size;
    return ptr;
}

/* Return to pool's free list */
static inline void pool_free(SomaPool* pool, void* ptr) {
    *(void**)ptr = pool->free_list;
    pool->free_list = ptr;
}

/* Initialize per-thread pools */
static void tls_pool_init(void) {
    if (tls_pools_initialized) return;

    tls_pools = (SomaPools*)malloc(sizeof(SomaPools));
    if (tls_pools) {
        pool_init(&tls_pools->pool_40, POOL_SIZE_40);
        pool_init(&tls_pools->pool_48, POOL_SIZE_48);
        pool_init(&tls_pools->pool_112, POOL_SIZE_112);
        tls_pools_initialized = 1;
    }
}

/* Cleanup per-thread pools */
static void tls_pool_cleanup(void) {
    if (!tls_pools_initialized || !tls_pools) return;

    pool_cleanup(&tls_pools->pool_40);
    pool_cleanup(&tls_pools->pool_48);
    pool_cleanup(&tls_pools->pool_112);
    free(tls_pools);
    tls_pools = NULL;
    tls_pools_initialized = 0;
}

/* Get this thread's pools */
static inline SomaPools* get_pools(void) {
    return tls_pools;
}

void soma_pool_init(void) {
#ifdef SOMA_POOL_STATS
    memset(&soma_pool_stats, 0, sizeof(soma_pool_stats));
#endif
    tls_pool_init();
}

void soma_pool_cleanup(void) {
    tls_pool_cleanup();
}

/*
 * Size-class routing: all object types share the same three pools.
 * Objects ≤48 bytes → pool_48, ≤112 bytes → pool_112, larger → malloc.
 */

void* soma_pool_alloc_closure(uint16_t env_size) {
    size_t needed = sizeof(SomaClosure) + (env_size * sizeof(void*));
    SomaPools* pools = get_pools();

    if (needed <= POOL_SIZE_48) {
        SOMA_STAT_INC(small_allocs);
        return pool_alloc(&pools->pool_48);
    }
    if (needed <= POOL_SIZE_112) {
        SOMA_STAT_INC(medium_allocs);
        return pool_alloc(&pools->pool_112);
    }

    SOMA_STAT_INC(large_allocs);
    return malloc(needed);
}

void soma_pool_free_closure(void* ptr, uint16_t env_size) {
    size_t needed = sizeof(SomaClosure) + (env_size * sizeof(void*));
    SomaPools* pools = get_pools();

    if (needed <= POOL_SIZE_48) {
        SOMA_STAT_INC(small_frees);
        pool_free(&pools->pool_48, ptr);
    } else if (needed <= POOL_SIZE_112) {
        SOMA_STAT_INC(medium_frees);
        pool_free(&pools->pool_112, ptr);
    } else {
        SOMA_STAT_INC(large_frees);
        free(ptr);
    }
}

void* soma_pool_alloc_string(size_t total_size) {
    SomaPools* pools = get_pools();

    if (total_size <= POOL_SIZE_48) {
        SOMA_STAT_INC(small_allocs);
        return pool_alloc(&pools->pool_48);
    }
    if (total_size <= POOL_SIZE_112) {
        SOMA_STAT_INC(medium_allocs);
        return pool_alloc(&pools->pool_112);
    }

    SOMA_STAT_INC(large_allocs);
    return malloc(total_size);
}

void soma_pool_free_string(void* ptr, size_t total_size) {
    SomaPools* pools = get_pools();

    if (total_size <= POOL_SIZE_48) {
        SOMA_STAT_INC(small_frees);
        pool_free(&pools->pool_48, ptr);
    } else if (total_size <= POOL_SIZE_112) {
        SOMA_STAT_INC(medium_frees);
        pool_free(&pools->pool_112, ptr);
    } else {
        SOMA_STAT_INC(large_frees);
        free(ptr);
    }
}

void* soma_pool_alloc_tagged(size_t total_size) {
    SomaPools* pools = get_pools();

    if (total_size <= POOL_SIZE_48) {
        SOMA_STAT_INC(small_allocs);
        return pool_alloc(&pools->pool_48);
    }
    if (total_size <= POOL_SIZE_112) {
        SOMA_STAT_INC(medium_allocs);
        return pool_alloc(&pools->pool_112);
    }

    SOMA_STAT_INC(large_allocs);
    return malloc(total_size);
}

void soma_pool_free_tagged(void* ptr, size_t total_size) {
    SomaPools* pools = get_pools();

    if (total_size <= POOL_SIZE_48) {
        SOMA_STAT_INC(small_frees);
        pool_free(&pools->pool_48, ptr);
    } else if (total_size <= POOL_SIZE_112) {
        SOMA_STAT_INC(medium_frees);
        pool_free(&pools->pool_112, ptr);
    } else {
        SOMA_STAT_INC(large_frees);
        free(ptr);
    }
}

/*
 * ============================================================================
 * SUP Pool Operations
 * ============================================================================
 */

void* soma_pool_alloc_sup(void) {
    SOMA_STAT_INC(sup_allocs);
    SomaPools* pools = get_pools();
    return pool_alloc(&pools->pool_40);
}

void soma_pool_free_sup(void* ptr) {
    SOMA_STAT_INC(sup_frees);
    SomaPools* pools = get_pools();
    pool_free(&pools->pool_40, ptr);
}


/*
 * soma_fresh_label — Generate a fresh unique duplication label
 */
uint32_t soma_fresh_label(void) {
    soma_panic("soma_fresh_label: dynamic runtime labels are disabled; labels must be compiler-assigned");
    return 0;
}

/* Check if a SomaValue is a heap pointer to a SUP node */
static inline int is_heap_sup(SomaValue value) {
    if (!SOMA_IS_PTR(value) || value == 0) return 0;
    SomaSup* sup = (SomaSup*)SOMA_TO_PTR(value);
    if (!IS_SUP(sup->tag)) return 0;
    return sup->_pad[0] == SOMA_SUP_PAD0 &&
           sup->_pad[1] == SOMA_SUP_PAD1 &&
           sup->_pad[2] == SOMA_SUP_PAD2;
}

/* Check if a SomaValue is a heap pointer to a closure */
static inline int is_heap_closure(SomaValue value) {
    if (!SOMA_IS_PTR(value) || value == 0) return 0;
    SomaClosure* closure = (SomaClosure*)SOMA_TO_PTR(value);
    return closure->tag == NODE_CLOSURE;
}

static SomaValue soma_clone_value_for_fork(SomaValue value);
static void* soma_clone_closure_for_fork(void* closure_ptr);

static SomaString* soma_clone_string_obj(SomaString* src) {
    if (src == NULL) return NULL;
    size_t data_bytes = (size_t)src->length + 1;
    size_t total = sizeof(SomaString) + data_bytes;
    SomaString* out = (SomaString*)soma_pool_alloc_string(total);
    if (out == NULL) {
        soma_panic("soma_clone_string_obj: out of memory");
        return NULL;
    }
    out->tag = NODE_STRING;
    out->_magic = SOMA_STRING_MAGIC;
    out->length = src->length;
    memcpy(out->data, src->data, data_bytes);
    return out;
}

void* soma_clone_flat_array_view(SomaFlatArrayView* src) {
    if (src == NULL) return NULL;

    /* Deep-copy the backing array */
    SomaFlatArray* srcBacking = (SomaFlatArray*)src->backing;
    SomaFlatArray* newBacking = NULL;
    void* newData = NULL;

    if (srcBacking != NULL) {
        size_t backingTotal = sizeof(SomaFlatArray) +
            (size_t)srcBacking->length * (size_t)srcBacking->elem_size;
        newBacking = (SomaFlatArray*)malloc(backingTotal);
        if (newBacking == NULL) {
            soma_panic("soma_clone_flat_array_view: out of memory");
            return NULL;
        }
        memcpy(newBacking, srcBacking, backingTotal);
        newBacking->_reserved = 0;

        /* Compute the data pointer offset within the backing */
        ptrdiff_t offset = (char*)src->data - (char*)(srcBacking + 1);
        newData = (char*)(newBacking + 1) + offset;
    }

    /* Allocate the new view */
    SomaFlatArrayView* dst = (SomaFlatArrayView*)malloc(sizeof(SomaFlatArrayView));
    if (dst == NULL) {
        soma_panic("soma_clone_flat_array_view: out of memory");
        return NULL;
    }
    dst->tag = NODE_FLAT_ARRAY_VIEW;
    memset(dst->_pad, 0, sizeof(dst->_pad));
    dst->_reserved = 0;
    dst->length = src->length;
    dst->data = newData;
    dst->backing = newBacking;
    return dst;
}

static SomaValue soma_clone_heap_value_for_dup(SomaValue value, uint32_t label) {
    if (!SOMA_IS_PTR(value) || value == 0) return value;

    void* ptr = SOMA_TO_PTR(value);
    uint8_t tag = *(uint8_t*)ptr;

    switch (tag) {
    case NODE_CLOSURE:
        return SOMA_PTR(soma_clone_closure(ptr, label));
    case NODE_STRING:
        return SOMA_PTR(soma_clone_string_obj((SomaString*)ptr));
    case NODE_TAGGED_PAYLOAD:
        return SOMA_PTR(soma_clone_tagged_payload(ptr, label));
    case NODE_FLAT_ARRAY_VIEW:
        return SOMA_PTR(soma_clone_flat_array_view((SomaFlatArrayView*)ptr));
    case NODE_FLAT_ARRAY: {
        /* Backing arrays should not be DUP'd directly in the new design,
         * but handle gracefully by deep-copying */
        SomaFlatArray* arr = (SomaFlatArray*)ptr;
        size_t total = sizeof(SomaFlatArray) +
            (size_t)arr->length * (size_t)arr->elem_size;
        SomaFlatArray* copy = (SomaFlatArray*)malloc(total);
        if (copy == NULL) {
            soma_panic("soma_clone_heap_value_for_dup: out of memory");
            return value;
        }
        memcpy(copy, arr, total);
        return SOMA_PTR(copy);
    }
    default:
        if (IS_SUP(tag)) {
            return soma_dup(label, value);
        }
        soma_panic("soma_clone_heap_value_for_dup: unsupported heap object tag");
        return value;
    }
}

void* soma_alloc_tagged_payload(uint64_t field_count) {
    size_t bytes = sizeof(SomaTaggedPayload) + field_count * sizeof(SomaValue);
    SomaTaggedPayload* payload = (SomaTaggedPayload*)soma_pool_alloc_tagged(bytes);
    if (payload == NULL) {
        soma_panic("soma_alloc_tagged_payload: out of memory");
        return NULL;
    }
    payload->tag = NODE_TAGGED_PAYLOAD;
    payload->_magic = SOMA_TAGGED_MAGIC;
    payload->count = (int64_t)field_count;
    return payload;
}


/*
 * soma_dup — Create a SUP node for lazy duplication
 *
 * The value is not cloned immediately; cloning is deferred until both
 * projections are accessed. If only one projection is ever used
 * (DUP-ERA annihilation), no cloning happens at all.
 */
SomaValue soma_dup(uint32_t label, SomaValue value) {
    SomaSup* sup = (SomaSup*)soma_pool_alloc_sup();
    sup->tag   = SUP_TAG_FRESH;
    sup->_pad[0] = SOMA_SUP_PAD0;
    sup->_pad[1] = SOMA_SUP_PAD1;
    sup->_pad[2] = SOMA_SUP_PAD2;
    sup->label = label;
    sup->value = (void*)value;
    sup->proj0 = NULL;
    sup->proj1 = NULL;
    return SOMA_PTR(sup);
}

/*
 * soma_proj0 — Extract first projection from a SUP
 *
 * Implements lazy duplication with label-based annihilation:
 *   Fresh: mark as proj0-accessed, return value
 *   Proj1 was first: clone the value (or annihilate if same-label inner SUP)
 *   Already accessed: return cached result
 */
SomaValue soma_proj0(SomaValue sup_val) {
    /* Non-pointer values pass through (no SUP wrapping) */
    if (!SOMA_IS_PTR(sup_val) || sup_val == 0) return sup_val;

    SomaSup* sup = (SomaSup*)SOMA_TO_PTR(sup_val);
    uint8_t tag = sup->tag;

    /* Fresh — first access via proj0 */
    if (tag == SUP_TAG_FRESH) {
        sup->tag = SUP_TAG_PROJ0;
        SomaValue value = (SomaValue)sup->value;

        /* Check for annihilation: is value a SUP with same label? */
        if (is_heap_sup(value)) {
            SomaSup* inner = (SomaSup*)SOMA_TO_PTR(value);
            if (inner->label == sup->label) {
                /* Same-label annihilation: return inner's first value directly */
                SomaValue result = (SomaValue)inner->value;
                sup->value = (void*)result;
                sup->proj0 = (void*)result;
                soma_pool_free_sup(inner);
                return result;
            }
        }

        /* No annihilation — cache and return value */
        sup->proj0 = (void*)value;
        return value;
    }

    /* Proj1 was accessed first — this is the second access, need to clone */
    if (tag == SUP_TAG_PROJ1) {
        sup->tag = SUP_TAG_BOTH;
        SomaValue value = (SomaValue)sup->value;

        /* Tagged values (int, bool, char) are value types — no cloning needed */
        if (!SOMA_IS_PTR(value) || value == 0) {
            sup->proj0 = (void*)value;
            return value;
        }

        /* Check for same-label annihilation */
        if (is_heap_sup(value)) {
            SomaSup* inner = (SomaSup*)SOMA_TO_PTR(value);
            if (inner->label == sup->label) {
                SomaValue result = (SomaValue)inner->value;
                sup->value = (void*)result;
                sup->proj0 = (void*)result;
                soma_pool_free_sup(inner);
                return result;
            }
        }

        /* Clone for second access — handles all heap types */
        SomaValue cloned = soma_clone_heap_value_for_dup(value, sup->label);
        sup->proj0 = (void*)cloned;
        return cloned;
    }

    /* Already accessed (PROJ0, BOTH, or cloning states) — return cached */
    return (SomaValue)sup->proj0;
}

/*
 * soma_proj1 — Extract second projection from a SUP
 *
 * Symmetric to soma_proj0.
 */
SomaValue soma_proj1(SomaValue sup_val) {
    /* Non-pointer values pass through */
    if (!SOMA_IS_PTR(sup_val) || sup_val == 0) return sup_val;

    SomaSup* sup = (SomaSup*)SOMA_TO_PTR(sup_val);
    uint8_t tag = sup->tag;

    /* Fresh — first access via proj1 */
    if (tag == SUP_TAG_FRESH) {
        sup->tag = SUP_TAG_PROJ1;
        SomaValue value = (SomaValue)sup->value;

        /* Check for annihilation */
        if (is_heap_sup(value)) {
            SomaSup* inner = (SomaSup*)SOMA_TO_PTR(value);
            if (inner->label == sup->label) {
                SomaValue result = (SomaValue)inner->value;
                sup->value = (void*)result;
                sup->proj1 = (void*)result;
                soma_pool_free_sup(inner);
                return result;
            }
        }

        /* No annihilation — cache and return */
        sup->proj1 = (void*)value;
        return value;
    }

    /* Proj0 was accessed first — second access, need to clone */
    if (tag == SUP_TAG_PROJ0) {
        sup->tag = SUP_TAG_BOTH;
        SomaValue value = (SomaValue)sup->value;

        /* Tagged values — no cloning */
        if (!SOMA_IS_PTR(value) || value == 0) {
            sup->proj1 = (void*)value;
            return value;
        }

        /* Same-label annihilation */
        if (is_heap_sup(value)) {
            SomaSup* inner = (SomaSup*)SOMA_TO_PTR(value);
            if (inner->label == sup->label) {
                SomaValue result = (SomaValue)inner->value;
                sup->value = (void*)result;
                sup->proj1 = (void*)result;
                soma_pool_free_sup(inner);
                return result;
            }
        }

        /* Clone for second access — handles all heap types */
        SomaValue cloned = soma_clone_heap_value_for_dup(value, sup->label);
        sup->proj1 = (void*)cloned;
        return cloned;
    }

    /* Already accessed — return cached */
    return (SomaValue)sup->proj1;
}

/*
 * ============================================================================
 * Closure Operations
 * ============================================================================
 */

void* soma_alloc_closure(void* func_ptr, uint8_t arity, uint16_t env_size) {
    SomaClosure* closure = (SomaClosure*)soma_pool_alloc_closure(env_size);

    closure->tag      = NODE_CLOSURE;
    closure->arity    = arity;
    closure->env_size = env_size;
    closure->env_kind = SOMA_ENV_DEFAULT;
    closure->_pad     = 0;
    closure->func_ptr = func_ptr;

    return closure;
}

void soma_closure_set_env(void* closure_ptr, uint16_t index, SomaValue value) {
    SomaClosure* closure = (SomaClosure*)closure_ptr;
    SomaValue* env = (SomaValue*)(closure + 1);
    env[index] = value;
}

SomaValue soma_closure_get_env(void* closure_ptr, uint16_t index) {
    SomaClosure* closure = (SomaClosure*)closure_ptr;
    SomaValue* env = (SomaValue*)(closure + 1);
    return env[index];
}

void* soma_closure_get_func(void* closure_ptr) {
    SomaClosure* closure = (SomaClosure*)closure_ptr;
    return closure->func_ptr;
}

/*
 * soma_call_with_args — Dispatch a call with a void* argument array.
 *
 * Supports up to SOMA_MAX_CALL_ARGS (16) arguments. Centralizes the variadic
 * dispatch used by soma_apply for saturated calls and over-application.
 */
#define SOMA_MAX_CALL_ARGS 16

static void* soma_call_with_args(void* (*fn)(), void** args, unsigned nargs) {
    switch (nargs) {
        case 0:  return fn();
        case 1:  return ((void*(*)(void*))fn)(args[0]);
        case 2:  return ((void*(*)(void*,void*))fn)(args[0], args[1]);
        case 3:  return ((void*(*)(void*,void*,void*))fn)(args[0], args[1], args[2]);
        case 4:  return ((void*(*)(void*,void*,void*,void*))fn)(
                     args[0], args[1], args[2], args[3]);
        case 5:  return ((void*(*)(void*,void*,void*,void*,void*))fn)(
                     args[0], args[1], args[2], args[3], args[4]);
        case 6:  return ((void*(*)(void*,void*,void*,void*,void*,void*))fn)(
                     args[0], args[1], args[2], args[3], args[4], args[5]);
        case 7:  return ((void*(*)(void*,void*,void*,void*,void*,void*,void*))fn)(
                     args[0], args[1], args[2], args[3], args[4], args[5],
                     args[6]);
        case 8:  return ((void*(*)(void*,void*,void*,void*,void*,void*,void*,void*))fn)(
                     args[0], args[1], args[2], args[3], args[4], args[5],
                     args[6], args[7]);
        case 9:  return ((void*(*)(void*,void*,void*,void*,void*,void*,void*,void*,
                          void*))fn)(
                     args[0], args[1], args[2], args[3], args[4], args[5],
                     args[6], args[7], args[8]);
        case 10: return ((void*(*)(void*,void*,void*,void*,void*,void*,void*,void*,
                          void*,void*))fn)(
                     args[0], args[1], args[2], args[3], args[4], args[5],
                     args[6], args[7], args[8], args[9]);
        case 11: return ((void*(*)(void*,void*,void*,void*,void*,void*,void*,void*,
                          void*,void*,void*))fn)(
                     args[0], args[1], args[2], args[3], args[4], args[5],
                     args[6], args[7], args[8], args[9], args[10]);
        case 12: return ((void*(*)(void*,void*,void*,void*,void*,void*,void*,void*,
                          void*,void*,void*,void*))fn)(
                     args[0], args[1], args[2], args[3], args[4], args[5],
                     args[6], args[7], args[8], args[9], args[10], args[11]);
        case 13: return ((void*(*)(void*,void*,void*,void*,void*,void*,void*,void*,
                          void*,void*,void*,void*,void*))fn)(
                     args[0], args[1], args[2], args[3], args[4], args[5],
                     args[6], args[7], args[8], args[9], args[10], args[11],
                     args[12]);
        case 14: return ((void*(*)(void*,void*,void*,void*,void*,void*,void*,void*,
                          void*,void*,void*,void*,void*,void*))fn)(
                     args[0], args[1], args[2], args[3], args[4], args[5],
                     args[6], args[7], args[8], args[9], args[10], args[11],
                     args[12], args[13]);
        case 15: return ((void*(*)(void*,void*,void*,void*,void*,void*,void*,void*,
                          void*,void*,void*,void*,void*,void*,void*))fn)(
                     args[0], args[1], args[2], args[3], args[4], args[5],
                     args[6], args[7], args[8], args[9], args[10], args[11],
                     args[12], args[13], args[14]);
        case 16: return ((void*(*)(void*,void*,void*,void*,void*,void*,void*,void*,
                          void*,void*,void*,void*,void*,void*,void*,void*))fn)(
                     args[0], args[1], args[2], args[3], args[4], args[5],
                     args[6], args[7], args[8], args[9], args[10], args[11],
                     args[12], args[13], args[14], args[15]);
        default:
            soma_panic("soma_call_with_args: too many arguments (max 16)");
            return NULL;
    }
}

/*
 * soma_apply — Apply one argument to a closure with partial application support
 *
 * Implements the eval/apply calling convention (Marlow & Peyton Jones 2004):
 *   arity == 0: over-application — call fn(env...) to get result closure, apply arg to it
 *   arity == 1: saturated call — call fn(env..., arg), return result
 *   arity >  1: PAP (partial application) — extend env with arg, decrement arity
 *
 * The env slots accumulate arguments across partial applications. When finally
 * saturated, all accumulated env slots are passed as leading arguments to the
 * original function, followed by the final arg.
 */
void* soma_apply(void* closure_ptr, void* arg) {
    SomaClosure* closure = (SomaClosure*)closure_ptr;
    uint8_t arity = closure->arity;
    uint16_t env_size = closure->env_size;
    void* (*fn)() = (void* (*)())closure->func_ptr;
    SomaValue* env = (SomaValue*)(closure + 1);

    if (arity == 0) {
        /* Over-application: fn already has all declared args in env.
         * Call fn(env...) → result closure, then apply arg to it. */
        void* args[SOMA_MAX_CALL_ARGS];
        for (uint16_t i = 0; i < env_size && i < SOMA_MAX_CALL_ARGS; i++)
            args[i] = (void*)env[i];
        void* result = soma_call_with_args(fn, args, env_size);
        return soma_apply(result, arg);
    } else if (arity == 1) {
        /* Saturated call: fn(env[0], ..., env[n-1], arg) */
        void* args[SOMA_MAX_CALL_ARGS];
        uint16_t n = 0;
        for (uint16_t i = 0; i < env_size && n < SOMA_MAX_CALL_ARGS; i++)
            args[n++] = (void*)env[i];
        if (n < SOMA_MAX_CALL_ARGS)
            args[n++] = arg;
        return soma_call_with_args(fn, args, n);
    } else {
        /* PAP: create new closure with arity-1 and env extended by arg */
        uint16_t new_env_size = env_size + 1;
        SomaClosure* pap = (SomaClosure*)soma_pool_alloc_closure(new_env_size);
        pap->tag      = NODE_CLOSURE;
        pap->arity    = arity - 1;
        pap->env_size = new_env_size;
        pap->env_kind = closure->env_kind;
        pap->_pad     = 0;
        pap->func_ptr = closure->func_ptr;

        SomaValue* pap_env = (SomaValue*)(pap + 1);
        for (uint16_t i = 0; i < env_size; i++)
            pap_env[i] = env[i];
        pap_env[env_size] = (SomaValue)(uintptr_t)arg;

        return pap;
    }
}

/*
 * soma_clone_closure — Clone a closure with lazy nested duplication
 *
 * Copies the header and all environment slots. For slots that contain
 * heap objects, clones them via the typed DUP helper which handles
 * closures, strings, tagged payloads, arrays, and nested SUPs.
 */
void* soma_clone_closure(void* closure_ptr, uint32_t label) {
    SomaClosure* closure = (SomaClosure*)closure_ptr;
    const uint16_t env_size = closure->env_size;

    void* new_closure = soma_pool_alloc_closure(env_size);
    memcpy(new_closure, closure, sizeof(SomaClosure));

    SomaValue* src_env = (SomaValue*)(closure + 1);
    SomaValue* dst_env = (SomaValue*)((SomaClosure*)new_closure + 1);

    switch (closure->env_kind) {
    case SOMA_ENV_FLAT:
        /* Flat scalars: bit-copy, no heap interaction */
        memcpy(dst_env, src_env, env_size * sizeof(SomaValue));
        break;
    case SOMA_ENV_TAGGED:
        /* Each env slot is a pointer to a heap-alloc'd {i32 tag, ptr payload}.
         * Clone: deep-copy the struct, clone the payload pointer inside. */
        for (uint16_t i = 0; i < env_size; i++) {
            SomaValue val = src_env[i];
            if (!SOMA_IS_PTR(val) || val == 0) { dst_env[i] = val; continue; }
            void* src_tu = SOMA_TO_PTR(val);
            int32_t vtag = *(int32_t*)src_tu;
            void* payload = *(void**)((char*)src_tu + 8);
            void* new_payload = (payload != NULL)
                ? soma_clone_tagged_payload(payload, label) : NULL;
            void* new_tu = malloc(16);
            *(int32_t*)new_tu = vtag;
            *(void**)((char*)new_tu + 8) = new_payload;
            dst_env[i] = SOMA_PTR(new_tu);
        }
        break;
    case SOMA_ENV_LIST:
        /* Deep-copy list views (interaction net ownership semantics) */
        for (uint16_t i = 0; i < env_size; i++) {
            if (SOMA_IS_PTR(src_env[i]) && src_env[i] != 0) {
                uint8_t etag = *(uint8_t*)SOMA_TO_PTR(src_env[i]);
                if (etag == NODE_FLAT_ARRAY_VIEW) {
                    dst_env[i] = SOMA_PTR(soma_clone_flat_array_view(
                        (SomaFlatArrayView*)SOMA_TO_PTR(src_env[i])));
                } else {
                    SomaFlatArray* arr = (SomaFlatArray*)SOMA_TO_PTR(src_env[i]);
                    size_t total = sizeof(SomaFlatArray) +
                        (size_t)arr->length * (size_t)arr->elem_size;
                    SomaFlatArray* copy = (SomaFlatArray*)malloc(total);
                    if (copy != NULL) memcpy(copy, arr, total);
                    dst_env[i] = SOMA_PTR(copy);
                }
            } else {
                dst_env[i] = src_env[i];
            }
        }
        break;
    default: /* SOMA_ENV_DEFAULT */
        /* Generic: runtime tag-based dispatch per env slot */
        for (uint16_t i = 0; i < env_size; i++) {
            dst_env[i] = soma_clone_heap_value_for_dup(src_env[i], label);
        }
        break;
    }

    return new_closure;
}

void* soma_clone_tagged_payload(void* payload, uint32_t label) {
    if (payload == NULL) return NULL;

    SomaTaggedPayload* src = (SomaTaggedPayload*)payload;
    int64_t count = src->count;
    if (count < 0) {
        soma_panic("soma_clone_tagged_payload: negative payload field count");
        return NULL;
    }

    SomaTaggedPayload* copy = (SomaTaggedPayload*)soma_alloc_tagged_payload((uint64_t)count);
    if (copy == NULL) {
        soma_panic("soma_clone_tagged_payload: out of memory");
        return NULL;
    }

    SomaValue* src_fields = (SomaValue*)(src + 1);
    SomaValue* dst_fields = (SomaValue*)(copy + 1);

    for (int64_t i = 0; i < count; i++) {
        dst_fields[i] = soma_clone_heap_value_for_dup(src_fields[i], label);
    }

    return copy;
}


static SomaValue soma_clone_value_for_fork(SomaValue value) {
    if (!SOMA_IS_PTR(value) || value == 0) return value;

    uint8_t tag = *(uint8_t*)SOMA_TO_PTR(value);

    if (IS_SUP(tag)) {
        SomaValue materialized = soma_proj0(value);
        return soma_clone_value_for_fork(materialized);
    }

    switch (tag) {
    case NODE_CLOSURE:
        return SOMA_PTR(soma_clone_closure_for_fork(SOMA_TO_PTR(value)));
    case NODE_STRING:
        return SOMA_PTR(soma_clone_string_obj((SomaString*)SOMA_TO_PTR(value)));
    case NODE_TAGGED_PAYLOAD:
        return SOMA_PTR(soma_clone_tagged_payload(SOMA_TO_PTR(value), 0));
    case NODE_FLAT_ARRAY_VIEW:
        return SOMA_PTR(soma_clone_flat_array_view(
            (SomaFlatArrayView*)SOMA_TO_PTR(value)));
    case NODE_FLAT_ARRAY: {
        /* Deep-copy backing array for fork isolation */
        SomaFlatArray* arr = (SomaFlatArray*)SOMA_TO_PTR(value);
        size_t total = sizeof(SomaFlatArray) +
            (size_t)arr->length * (size_t)arr->elem_size;
        SomaFlatArray* copy = (SomaFlatArray*)malloc(total);
        if (copy != NULL) memcpy(copy, arr, total);
        return SOMA_PTR(copy);
    }
    default:
        return value;
    }
}

static void* soma_clone_closure_for_fork(void* closure_ptr) {
    SomaClosure* closure = (SomaClosure*)closure_ptr;
    const uint16_t env_size = closure->env_size;

    void* new_closure = soma_pool_alloc_closure(env_size);
    memcpy(new_closure, closure, sizeof(SomaClosure));

    SomaValue* src_env = (SomaValue*)(closure + 1);
    SomaValue* dst_env = (SomaValue*)((SomaClosure*)new_closure + 1);

    switch (closure->env_kind) {
    case SOMA_ENV_FLAT:
        memcpy(dst_env, src_env, env_size * sizeof(SomaValue));
        break;
    case SOMA_ENV_TAGGED:
        for (uint16_t i = 0; i < env_size; i++) {
            SomaValue val = src_env[i];
            if (!SOMA_IS_PTR(val) || val == 0) { dst_env[i] = val; continue; }
            void* src_tu = SOMA_TO_PTR(val);
            int32_t vtag = *(int32_t*)src_tu;
            void* payload = *(void**)((char*)src_tu + 8);
            void* new_payload = (payload != NULL)
                ? soma_clone_tagged_payload(payload, 0) : NULL;
            void* new_tu = malloc(16);
            *(int32_t*)new_tu = vtag;
            *(void**)((char*)new_tu + 8) = new_payload;
            dst_env[i] = SOMA_PTR(new_tu);
        }
        break;
    case SOMA_ENV_LIST:
        for (uint16_t i = 0; i < env_size; i++) {
            if (SOMA_IS_PTR(src_env[i]) && src_env[i] != 0) {
                uint8_t etag = *(uint8_t*)SOMA_TO_PTR(src_env[i]);
                if (etag == NODE_FLAT_ARRAY_VIEW) {
                    dst_env[i] = SOMA_PTR(soma_clone_flat_array_view(
                        (SomaFlatArrayView*)SOMA_TO_PTR(src_env[i])));
                } else {
                    /* Legacy flat array — deep copy */
                    SomaFlatArray* arr = (SomaFlatArray*)SOMA_TO_PTR(src_env[i]);
                    size_t total = sizeof(SomaFlatArray) +
                        (size_t)arr->length * (size_t)arr->elem_size;
                    SomaFlatArray* copy = (SomaFlatArray*)malloc(total);
                    if (copy != NULL) memcpy(copy, arr, total);
                    dst_env[i] = SOMA_PTR(copy);
                }
            } else {
                dst_env[i] = src_env[i];
            }
        }
        break;
    default:
        for (uint16_t i = 0; i < env_size; i++) {
            dst_env[i] = soma_clone_value_for_fork(src_env[i]);
        }
        break;
    }

    return new_closure;
}

void soma_era_string(void* value) {
    if (value == NULL) return;
    SomaString* s = (SomaString*)value;
    size_t total = sizeof(SomaString) + (size_t)s->length + 1;
    soma_pool_free_string(value, total);
}

/*
 * soma_era_free — Free a heap-allocated value (ERA node)
 *
 * Uses an explicit worklist instead of recursion to avoid stack overflow
 * on deeply nested object graphs. A small inline stack handles the
 * common case without any allocation; only pathological graphs spill
 * to a heap-allocated worklist.
 */

#define ERA_STACK_INLINE 64

void soma_era_free(void* value) {
    if (value == NULL) return;

    void*  stack_buf[ERA_STACK_INLINE];
    void** stack = stack_buf;
    int    sp    = 0;
    int    cap   = ERA_STACK_INLINE;

    stack[sp++] = value;

    SomaPools* pools = get_pools();

    while (sp > 0) {
        void* cur = stack[--sp];
        if (cur == NULL) continue;

        uint8_t tag = *(uint8_t*)cur;

        /* --- leaf types: free immediately, no children --- */

        if (tag == NODE_STRING) {
            SomaString* s = (SomaString*)cur;
            size_t total = sizeof(SomaString) + (size_t)s->length + 1;
            if (total <= POOL_SIZE_48) {
                SOMA_STAT_INC(small_frees);
                pool_free(&pools->pool_48, cur);
            } else if (total <= POOL_SIZE_112) {
                SOMA_STAT_INC(medium_frees);
                pool_free(&pools->pool_112, cur);
            } else {
                SOMA_STAT_INC(large_frees);
                free(cur);
            }
            continue;
        }

        /* --- compound types: push children, then free the node --- */

        /* Macro: ensure worklist capacity for N more entries */
        #define ERA_ENSURE(n) do {                                     \
            if (sp + (n) > cap) {                                      \
                int new_cap = cap * 2;                                 \
                while (new_cap < sp + (n)) new_cap *= 2;              \
                if (stack == stack_buf) {                               \
                    stack = (void**)malloc(new_cap * sizeof(void*));    \
                    memcpy(stack, stack_buf, sp * sizeof(void*));       \
                } else {                                               \
                    stack = (void**)realloc(stack, new_cap * sizeof(void*)); \
                }                                                      \
                cap = new_cap;                                         \
            }                                                          \
        } while (0)

        if (tag == NODE_CLOSURE) {
            SomaClosure* closure = (SomaClosure*)cur;
            SomaValue* env = (SomaValue*)(closure + 1);
            uint16_t env_size = closure->env_size;

            switch (closure->env_kind) {
            case SOMA_ENV_FLAT:
                /* No heap children — nothing to push */
                break;
            case SOMA_ENV_TAGGED:
                /* Each env slot is a pointer to a heap-alloc'd {i32, ptr}.
                 * Push the payload pointer, then free the struct. */
                for (uint16_t i = 0; i < env_size; i++) {
                    if (!SOMA_IS_PTR(env[i]) || env[i] == 0) continue;
                    void* tu = SOMA_TO_PTR(env[i]);
                    void* payload = *(void**)((char*)tu + 8);
                    if (payload != NULL) {
                        ERA_ENSURE(1);
                        stack[sp++] = payload;
                    }
                    free(tu);
                }
                break;
            case SOMA_ENV_LIST:
                /* List views/arrays: push onto ERA worklist */
                ERA_ENSURE(env_size);
                for (uint16_t i = 0; i < env_size; i++) {
                    if (!SOMA_IS_PTR(env[i]) || env[i] == 0) continue;
                    stack[sp++] = SOMA_TO_PTR(env[i]);
                }
                break;
            default: /* SOMA_ENV_DEFAULT */
                ERA_ENSURE(env_size);
                for (uint16_t i = 0; i < env_size; i++) {
                    if (SOMA_IS_PTR(env[i]) && env[i] != 0) {
                        stack[sp++] = SOMA_TO_PTR(env[i]);
                    }
                }
                break;
            }

            size_t needed = sizeof(SomaClosure) + (env_size * sizeof(void*));
            if (needed <= POOL_SIZE_48) {
                SOMA_STAT_INC(small_frees);
                pool_free(&pools->pool_48, cur);
            } else if (needed <= POOL_SIZE_112) {
                SOMA_STAT_INC(medium_frees);
                pool_free(&pools->pool_112, cur);
            } else {
                SOMA_STAT_INC(large_frees);
                free(cur);
            }

        } else if (tag == NODE_TAGGED_PAYLOAD) {
            SomaTaggedPayload* p = (SomaTaggedPayload*)cur;
            int64_t count = p->count;
            SomaValue* fields = (SomaValue*)(p + 1);

            ERA_ENSURE(count);
            for (int64_t i = 0; i < count; i++) {
                if (SOMA_IS_PTR(fields[i]) && fields[i] != 0) {
                    stack[sp++] = SOMA_TO_PTR(fields[i]);
                }
            }

            size_t total = sizeof(SomaTaggedPayload) + (size_t)count * sizeof(SomaValue);
            if (total <= POOL_SIZE_48) {
                SOMA_STAT_INC(small_frees);
                pool_free(&pools->pool_48, cur);
            } else if (total <= POOL_SIZE_112) {
                SOMA_STAT_INC(medium_frees);
                pool_free(&pools->pool_112, cur);
            } else {
                SOMA_STAT_INC(large_frees);
                free(cur);
            }

        } else if (tag == NODE_FLAT_ARRAY_VIEW) {
            SomaFlatArrayView* view = (SomaFlatArrayView*)cur;
            /* Free the owned backing array, then free the view */
            if (view->backing != NULL) {
                free(view->backing);
            }
            free(cur);

        } else if (tag == NODE_FLAT_ARRAY) {
            /* Backing arrays freed directly (legacy or via view ERA) */
            free(cur);

        } else if (IS_SUP(tag)) {
            SomaSup* sup = (SomaSup*)cur;

            /*
             * Tag-aware child collection — the SUP tag tells us exactly
             * which fields are live and which alias each other:
             *
             *   FRESH  → only value is live (proj0/proj1 are NULL)
             *   PROJ0  → proj0 == value (aliased), both point to the same object
             *   PROJ1  → proj1 == value (aliased), both point to the same object
             *   BOTH   → value is the original; one of proj0/proj1 is a clone
             */
            SomaValue v = (SomaValue)sup->value;

            switch (sup->tag) {
            case SUP_TAG_FRESH:
            case SUP_TAG_PROJ0:
            case SUP_TAG_PROJ1:
                /* Single live value — free it once */
                if (SOMA_IS_PTR(v) && v != 0) {
                    ERA_ENSURE(1);
                    stack[sp++] = SOMA_TO_PTR(v);
                }
                break;

            case SUP_TAG_BOTH:
            default: {
                /* Original value + the clone (whichever proj differs from value) */
                SomaValue p0 = (SomaValue)sup->proj0;
                SomaValue p1 = (SomaValue)sup->proj1;
                ERA_ENSURE(2);

                if (SOMA_IS_PTR(v) && v != 0) {
                    stack[sp++] = SOMA_TO_PTR(v);
                }
                /* Exactly one of p0/p1 is a clone (differs from value) */
                if (p0 != v && SOMA_IS_PTR(p0) && p0 != 0) {
                    stack[sp++] = SOMA_TO_PTR(p0);
                }
                if (p1 != v && SOMA_IS_PTR(p1) && p1 != 0) {
                    stack[sp++] = SOMA_TO_PTR(p1);
                }
                break;
            }
            }

            SOMA_STAT_INC(sup_frees);
            pool_free(&pools->pool_40, cur);

        } else {
            /* Unknown heap object — use regular free */
            free(cur);
        }

        #undef ERA_ENSURE
    }

    if (stack != stack_buf) {
        free(stack);
    }
}

/*
 * soma_era_tagged_payload — Free a tagged union payload buffer
 *
 * Delegates to the iterative soma_era_free which handles tagged payloads
 * inline.  Kept as a separate entry point for callers that have already
 * identified the object type.
 */
void soma_era_tagged_payload(void* payload) {
    soma_era_free(payload);
}

/*
 * ============================================================================
 * String Operations
 * ============================================================================
 */

char* soma_to_cstring(SomaString* str) {
    if (str == NULL) {
        return NULL;
    }
    return str->data;
}

SomaString* soma_from_cstring(const char* cstr) {
    if (cstr == NULL) return NULL;

    size_t len = strlen(cstr);
    size_t total = sizeof(SomaString) + len + 1;
    SomaString* s = (SomaString*)soma_pool_alloc_string(total);
    if (s == NULL) {
        soma_panic("soma_from_cstring: out of memory");
        return NULL;
    }
    s->tag = NODE_STRING;
    s->_magic = SOMA_STRING_MAGIC;
    s->length = (int64_t)len;
    memcpy(s->data, cstr, len + 1);
    return s;
}

uint64_t soma_cstring_len(const char* cstr) {
    if (cstr == NULL) {
        return 0;
    }
    return (uint64_t)strlen(cstr);
}

SomaString* soma_strcat(SomaString* a, SomaString* b) {
    if (a == NULL) {
        if (b == NULL) return soma_from_cstring("");
        return soma_from_cstring(b->data);
    }
    if (b == NULL) return soma_from_cstring(a->data);

    size_t len_a = (size_t)a->length;
    size_t len_b = (size_t)b->length;
    size_t total_len = len_a + len_b;
    size_t total = sizeof(SomaString) + total_len + 1;

    SomaString* result = (SomaString*)soma_pool_alloc_string(total);
    if (result == NULL) {
        soma_panic("soma_strcat: out of memory");
        return NULL;
    }
    result->tag = NODE_STRING;
    result->_magic = SOMA_STRING_MAGIC;
    result->length = (int64_t)total_len;
    memcpy(result->data, a->data, len_a);
    memcpy(result->data + len_a, b->data, len_b);
    result->data[total_len] = '\0';
    return result;
}

SomaString* soma_int_to_string(int32_t val) {
    char buf[12];
    int len = snprintf(buf, sizeof(buf), "%d", val);

    size_t total = sizeof(SomaString) + len + 1;
    SomaString* s = (SomaString*)soma_pool_alloc_string(total);
    if (s == NULL) {
        soma_panic("soma_int_to_string: out of memory");
        return NULL;
    }
    s->tag = NODE_STRING;
    s->_magic = SOMA_STRING_MAGIC;
    s->length = (int64_t)len;
    memcpy(s->data, buf, len + 1);
    return s;
}

void soma_panic(const char* msg) {
    fprintf(stderr, "PANIC: %s\n", msg);
    soma_pool_cleanup();
    exit(1);
}

/*
 * ============================================================================
 * Parallel Runtime Implementation
 * ============================================================================
 */

SomaParRuntime soma_par = {0};
SomaParStats soma_par_stats = {0};

__thread SomaWorker* soma_current_worker = NULL;

/*
 * Chase-Lev Deque Operations
 */

static void deque_init(SomaDeque* d) {
    atomic_store(&d->top, 0);
    atomic_store(&d->bottom, 0);
    for (int i = 0; i < SOMA_TASK_QUEUE_SIZE; i++) {
        atomic_store(&d->buffer[i], NULL);
    }
}

static void deque_push(SomaDeque* d, SomaTask* task) {
    size_t b = atomic_load_explicit(&d->bottom, memory_order_relaxed);
    atomic_store_explicit(&d->buffer[b % SOMA_TASK_QUEUE_SIZE], task, memory_order_relaxed);
    atomic_thread_fence(memory_order_release);
    atomic_store_explicit(&d->bottom, b + 1, memory_order_relaxed);
}

static SomaTask* deque_pop(SomaDeque* d) {
    size_t b = atomic_load_explicit(&d->bottom, memory_order_relaxed) - 1;
    atomic_store_explicit(&d->bottom, b, memory_order_relaxed);
    atomic_thread_fence(memory_order_seq_cst);
    size_t t = atomic_load_explicit(&d->top, memory_order_relaxed);

    if (t <= b) {
        SomaTask* task = atomic_load_explicit(&d->buffer[b % SOMA_TASK_QUEUE_SIZE],
                                               memory_order_relaxed);
        if (t == b) {
            if (!atomic_compare_exchange_strong_explicit(
                    &d->top, &t, t + 1,
                    memory_order_seq_cst, memory_order_relaxed)) {
                task = NULL;
            }
            atomic_store_explicit(&d->bottom, b + 1, memory_order_relaxed);
        }
        return task;
    } else {
        atomic_store_explicit(&d->bottom, b + 1, memory_order_relaxed);
        return NULL;
    }
}

static SomaTask* deque_steal(SomaDeque* d) {
    size_t t = atomic_load_explicit(&d->top, memory_order_acquire);
    atomic_thread_fence(memory_order_seq_cst);
    size_t b = atomic_load_explicit(&d->bottom, memory_order_acquire);

    if (t < b) {
        SomaTask* task = atomic_load_explicit(&d->buffer[t % SOMA_TASK_QUEUE_SIZE],
                                               memory_order_relaxed);
        if (!atomic_compare_exchange_strong_explicit(
                &d->top, &t, t + 1,
                memory_order_seq_cst, memory_order_relaxed)) {
            return NULL;
        }
        return task;
    }
    return NULL;
}

/*
 * Task Pool
 */

#define TASK_POOL_INITIAL_SIZE 256

SomaTask* soma_task_alloc(void) {
    pthread_mutex_lock(&soma_par.task_pool_lock);
    if (soma_par.task_pool != NULL) {
        SomaTask* task = soma_par.task_pool;
        soma_par.task_pool = *(SomaTask**)task;
        pthread_mutex_unlock(&soma_par.task_pool_lock);
        return task;
    }
    pthread_mutex_unlock(&soma_par.task_pool_lock);

    return (SomaTask*)malloc(sizeof(SomaTask));
}

void soma_task_free(SomaTask* task) {
    pthread_mutex_lock(&soma_par.task_pool_lock);
    *(SomaTask**)task = soma_par.task_pool;
    soma_par.task_pool = task;
    pthread_mutex_unlock(&soma_par.task_pool_lock);
}

/*
 * Task Execution
 */

static inline SomaValue task_execute(SomaTask* task) {
    switch (task->kind) {
        case TASK_KIND_DIRECT:
            return task->fn.direct(task->arg);
        case TASK_KIND_CLOSURE:
            return task->fn.closure(task->env, task->arg);
        case TASK_KIND_TRAMPOLINE: {
            SomaValue* args = (SomaValue*)task->env;
            SomaValue result = task->fn.trampoline(args);
            free(args);
            return result;
        }
        case TASK_KIND_GENERIC:
        default:
            return task->fn.generic(task->env);
    }
}

/*
 * Worker Thread
 */

static void worker_set_hungry(SomaWorker* w, int hungry) {
    int was_hungry = atomic_exchange(&w->hungry, hungry);
    if (hungry && !was_hungry) {
        atomic_fetch_add(&soma_par.hungry_count, 1);
    } else if (!hungry && was_hungry) {
        atomic_fetch_sub(&soma_par.hungry_count, 1);
    }
}

static void* worker_main(void* arg) {
    SomaWorker* self = (SomaWorker*)arg;
    soma_current_worker = self;

    tls_pool_init();

    while (!atomic_load(&soma_par.shutdown)) {
        SomaTask* task = deque_pop(&self->deque);

        if (task == NULL) {
            worker_set_hungry(self, 1);

            int victim_id = (self->id + 1) % soma_par.num_workers;
            for (int attempts = 0; attempts < soma_par.num_workers; attempts++) {
                if (victim_id != self->id) {
                    SomaWorker* victim = &soma_par.workers[victim_id];
                    task = deque_steal(&victim->deque);
                    self->steal_attempts++;
                    if (task != NULL) {
                        self->tasks_stolen++;
                        atomic_fetch_add(&soma_par_stats.tasks_stolen, 1);
                        worker_set_hungry(self, 0);
                        break;
                    }
                }
                victim_id = (victim_id + 1) % soma_par.num_workers;
            }

            if (task == NULL) {
                sched_yield();
                continue;
            }
        } else {
            worker_set_hungry(self, 0);
        }

        int expected = TASK_PENDING;
        if (atomic_compare_exchange_strong(&task->state, &expected, TASK_RUNNING)) {
            task->result = task_execute(task);
            atomic_store(&task->state, TASK_DONE);
            atomic_fetch_sub(&soma_par.pending_tasks, 1);
            self->tasks_run++;
            atomic_fetch_add(&soma_par_stats.tasks_run, 1);
        }
    }

    tls_pool_cleanup();

    return NULL;
}

/*
 * Runtime Lifecycle
 */

static int get_num_cpus(void) {
#ifdef _WIN32
    SYSTEM_INFO sysinfo;
    GetSystemInfo(&sysinfo);
    return (int)sysinfo.dwNumberOfProcessors;
#else
    return (int)sysconf(_SC_NPROCESSORS_ONLN);
#endif
}

void soma_par_init(int num_workers) {
    if (num_workers <= 0) {
        num_workers = get_num_cpus() - 1;
        if (num_workers < 1) num_workers = 1;
    }
    if (num_workers > SOMA_MAX_WORKERS) {
        num_workers = SOMA_MAX_WORKERS;
    }

    soma_par.num_workers = num_workers;
    atomic_store(&soma_par.shutdown, 0);
    atomic_store(&soma_par.pending_tasks, 0);
    atomic_store(&soma_par.hungry_count, 0);
    soma_par.task_pool = NULL;
    pthread_mutex_init(&soma_par.task_pool_lock, NULL);

    for (int i = 0; i < TASK_POOL_INITIAL_SIZE; i++) {
        SomaTask* t = (SomaTask*)malloc(sizeof(SomaTask));
        soma_task_free(t);
    }

    pthread_attr_t attr;
    pthread_attr_init(&attr);
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

    atomic_store(&soma_par.shutdown, 1);

    for (int i = 0; i < soma_par.num_workers; i++) {
        pthread_join(soma_par.workers[i].thread, NULL);
    }

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

void soma_par_spawn(SomaTask* task) {
    SomaWorker* w = soma_current_worker;

    atomic_store(&task->state, TASK_PENDING);
    atomic_fetch_add(&soma_par.pending_tasks, 1);
    atomic_fetch_add(&soma_par_stats.tasks_spawned, 1);

    if (w != NULL) {
        deque_push(&w->deque, task);
    } else {
        deque_push(&soma_par.workers[0].deque, task);
    }
}

SomaTask* soma_par_pop(SomaWorker* worker) {
    return deque_pop(&worker->deque);
}

SomaTask* soma_par_steal(SomaWorker* thief, SomaWorker* victim) {
    (void)thief;
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

    while (atomic_load(&task->state) != TASK_DONE) {
        sched_yield();
    }
    return task->result;
}

/*
 * Fork-Join API
 */

SomaTask* soma_fork(SomaTaskFn fn, void* env) {
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
    if (env != NULL) {
        uint8_t tag = *(uint8_t*)env;
        if (tag == NODE_CLOSURE) {
            task->env = soma_clone_closure_for_fork(env);
        } else if (IS_SUP(tag)) {
            SomaValue isolated = soma_clone_value_for_fork(SOMA_PTR(env));
            task->env = SOMA_TO_PTR(isolated);
        }
    }
    task->arg = 0;
    task->result = 0;

    soma_par_spawn(task);

    return task;
}

int soma_par_enabled_export(void) {
    return soma_par_enabled();
}

SomaTask* soma_fork_direct(SomaDirectFn fn, SomaValue arg) {
    if (!soma_par_enabled()) {
        return NULL;
    }

    SomaTask* task = soma_task_alloc();
    if (!task) {
        return NULL;
    }

    task->kind = TASK_KIND_DIRECT;
    task->fn.direct = fn;
    task->env = NULL;
    task->arg = soma_clone_value_for_fork(arg);
    task->result = 0;

    soma_par_spawn(task);

    return task;
}

SomaTask* soma_fork_closure(SomaClosureFn fn, void* closure, SomaValue arg) {
    if (!soma_par_enabled()) {
        return NULL;
    }

    SomaTask* task = soma_task_alloc();
    if (!task) {
        return NULL;
    }

    task->kind = TASK_KIND_CLOSURE;
    task->fn.closure = fn;
    task->env = soma_clone_closure_for_fork(closure);
    task->arg = soma_clone_value_for_fork(arg);
    task->result = 0;

    soma_par_spawn(task);

    return task;
}

SomaTask* soma_fork_multi(void* fn, SomaValue* args, int num_args) {
    if (!soma_par_enabled()) {
        return NULL;
    }

    SomaTask* task = soma_task_alloc();
    if (!task) {
        return NULL;
    }

    SomaValue* args_copy = (SomaValue*)malloc(num_args * sizeof(SomaValue));
    if (!args_copy) {
        soma_task_free(task);
        return NULL;
    }
    for (int i = 0; i < num_args; i++) {
        args_copy[i] = soma_clone_value_for_fork(args[i]);
    }

    task->kind = TASK_KIND_TRAMPOLINE;
    task->fn.trampoline = (SomaTrampolineFn)fn;
    task->env = args_copy;
    task->arg = (SomaValue)num_args;
    task->result = 0;

    soma_par_spawn(task);

    return task;
}

SomaValue soma_join(SomaTask* task) {
    if (task == NULL) {
        return 0;
    }

    SomaValue result;
    int state = atomic_load(&task->state);

    if (state == TASK_PENDING) {
        for (int i = 0; i < 100; i++) {
            sched_yield();
            state = atomic_load(&task->state);
            if (state != TASK_PENDING) break;
        }

        if (state == TASK_PENDING) {
            int expected = TASK_PENDING;
            if (atomic_compare_exchange_strong(&task->state, &expected, TASK_RUNNING)) {
                task->result = task_execute(task);
                atomic_store(&task->state, TASK_DONE);
                atomic_fetch_sub(&soma_par.pending_tasks, 1);
                atomic_fetch_add(&soma_par_stats.tasks_run_inline, 1);
                result = task->result;
                soma_task_free(task);
                return result;
            }
        }
    }

    while (atomic_load(&task->state) != TASK_DONE) {
        SomaWorker* w = soma_current_worker;
        if (w != NULL) {
            SomaTask* other = deque_pop(&w->deque);
            if (other != NULL) {
                int exp = TASK_PENDING;
                if (atomic_compare_exchange_strong(&other->state, &exp, TASK_RUNNING)) {
                    other->result = task_execute(other);
                    atomic_store(&other->state, TASK_DONE);
                    atomic_fetch_sub(&soma_par.pending_tasks, 1);
                }
            }
        }
        sched_yield();
    }

    result = task->result;
    soma_task_free(task);
    return result;
}

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

    for (int i = 0; i < soma_par.num_workers; i++) {
        SomaWorker* w = &soma_par.workers[i];
        fprintf(stderr, "[soma_par] Worker %d: run=%lu stolen=%lu attempts=%lu\n",
                i, (unsigned long)w->tasks_run, (unsigned long)w->tasks_stolen,
                (unsigned long)w->steal_attempts);
    }

#ifdef SOMA_POOL_STATS
    fprintf(stderr, "[soma_pool] SUP allocs: %lu, frees: %lu\n",
            (unsigned long)atomic_load(&soma_pool_stats.sup_allocs),
            (unsigned long)atomic_load(&soma_pool_stats.sup_frees));
    fprintf(stderr, "[soma_pool] Small (48B): %lu/%lu, Medium (112B): %lu/%lu, Large: %lu/%lu\n",
            (unsigned long)atomic_load(&soma_pool_stats.small_allocs),
            (unsigned long)atomic_load(&soma_pool_stats.small_frees),
            (unsigned long)atomic_load(&soma_pool_stats.medium_allocs),
            (unsigned long)atomic_load(&soma_pool_stats.medium_frees),
            (unsigned long)atomic_load(&soma_pool_stats.large_allocs),
            (unsigned long)atomic_load(&soma_pool_stats.large_frees));
    fprintf(stderr, "[soma_pool] Blocks allocated: %lu, bytes: %lu\n",
            (unsigned long)atomic_load(&soma_pool_stats.blocks_allocated),
            (unsigned long)atomic_load(&soma_pool_stats.bytes_allocated));
#endif
}

#ifndef SOMA_NO_MAIN
extern int soma_main(void);

int main(void) {
    soma_pool_init();
    int result = soma_main();
    soma_pool_cleanup();
    return result;
}
#endif
