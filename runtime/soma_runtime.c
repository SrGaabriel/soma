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
SomaPoolStats soma_pool_stats;

/*
 * ============================================================================
 * Per-Thread Memory Pool Implementation (TLS)
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
 * ============================================================================
 * SUP Pool Operations
 * ============================================================================
 */

void* soma_pool_alloc_sup(void) {
    atomic_fetch_add(&soma_pool_stats.sup_allocs, 1);
    SomaPools* pools = get_pools();
    return pool_alloc(&pools->sup_pool);
}

void soma_pool_free_sup(void* ptr) {
    atomic_fetch_add(&soma_pool_stats.sup_frees, 1);
    SomaPools* pools = get_pools();
    pool_free(&pools->sup_pool, ptr);
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
    uint8_t tag = *(uint8_t*)SOMA_TO_PTR(value);
    return IS_SUP(tag);
}

/* Check if a SomaValue is a heap pointer to a closure */
static inline int is_heap_closure(SomaValue value) {
    if (!SOMA_IS_PTR(value) || value == 0) return 0;
    uint8_t tag = *(uint8_t*)SOMA_TO_PTR(value);
    return tag == NODE_CLOSURE;
}

static SomaValue soma_clone_value_for_fork(SomaValue value);
static void* soma_clone_closure_for_fork(void* closure_ptr);

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
            /* Different label — pass through (implicit commutation) */
            sup->proj0 = (void*)value;
            return value;
        }

        /* Closure — need to clone */
        if (is_heap_closure(value)) {
            void* cloned = soma_clone_closure(SOMA_TO_PTR(value), sup->label);
            sup->proj0 = cloned;
            return SOMA_PTR(cloned);
        }

        /* Other heap object — shallow copy */
        sup->proj0 = (void*)value;
        return value;
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
            /* Different label — pass through */
            sup->proj1 = (void*)value;
            return value;
        }

        /* Closure — clone */
        if (is_heap_closure(value)) {
            void* cloned = soma_clone_closure(SOMA_TO_PTR(value), sup->label);
            sup->proj1 = cloned;
            return SOMA_PTR(cloned);
        }

        /* Other heap object — shallow copy */
        sup->proj1 = (void*)value;
        return value;
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
 * soma_clone_closure — Clone a closure with lazy nested duplication
 *
 * Copies the header and all environment slots. For slots that contain
 * closures or SUPs (detected at runtime via tag byte), wraps them in
 * fresh SUP nodes for lazy incremental cloning — the nested values are
 * only actually cloned when both copies are accessed.
 */
void* soma_clone_closure(void* closure_ptr, uint32_t label) {
    SomaClosure* closure = (SomaClosure*)closure_ptr;
    const uint16_t env_size = closure->env_size;

    /* Allocate new closure */
    void* new_closure = soma_pool_alloc_closure(env_size);

    /* Copy header */
    memcpy(new_closure, closure, sizeof(SomaClosure));

    SomaValue* src_env = (SomaValue*)(closure + 1);
    SomaValue* dst_env = (SomaValue*)((SomaClosure*)new_closure + 1);

    /* Copy environment, wrapping heap objects in SUP(label, ·) for lazy cloning */
    for (uint16_t i = 0; i < env_size; i++) {
        SomaValue val = src_env[i];

        if (SOMA_IS_PTR(val) && val != 0) {
            uint8_t tag = *(uint8_t*)SOMA_TO_PTR(val);
            if (tag == NODE_CLOSURE || IS_SUP(tag)) {
                /* Preserve the caller's static DUP label through commutation. */
                SomaValue sup = soma_dup(label, val);
                dst_env[i] = sup;
                continue;
            }
        }
        dst_env[i] = val;
    }

    return new_closure;
}

static SomaValue soma_clone_value_for_fork(SomaValue value) {
    if (!SOMA_IS_PTR(value) || value == 0) return value;

    uint8_t tag = *(uint8_t*)SOMA_TO_PTR(value);

    if (IS_SUP(tag)) {
        SomaValue materialized = soma_proj0(value);
        return soma_clone_value_for_fork(materialized);
    }

    if (tag == NODE_CLOSURE) {
        void* cloned = soma_clone_closure_for_fork(SOMA_TO_PTR(value));
        return SOMA_PTR(cloned);
    }

    return value;
}

static void* soma_clone_closure_for_fork(void* closure_ptr) {
    SomaClosure* closure = (SomaClosure*)closure_ptr;
    const uint16_t env_size = closure->env_size;

    void* new_closure = soma_pool_alloc_closure(env_size);
    memcpy(new_closure, closure, sizeof(SomaClosure));

    SomaValue* src_env = (SomaValue*)(closure + 1);
    SomaValue* dst_env = (SomaValue*)((SomaClosure*)new_closure + 1);

    for (uint16_t i = 0; i < env_size; i++) {
      dst_env[i] = soma_clone_value_for_fork(src_env[i]);
    }

    return new_closure;
}

void soma_era_string(void* value) {
    if (value == NULL) return;

    SomaString* s = (SomaString*)value;
    if (s->data != NULL) {
        free(s->data);
    }
    free(s);
}

/*
 * soma_era_free — Free a heap-allocated value (ERA node)
 *
 * Recursively frees the value and its children. After linearization,
 * every value is used exactly once, so when ERA fires we have exclusive
 * ownership — no reference counting needed.
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
        SomaSup* sup = (SomaSup*)value;
        SomaValue candidates[3] = {
            (SomaValue)sup->value,
            (SomaValue)sup->proj0,
            (SomaValue)sup->proj1
        };

        for (int i = 0; i < 3; i++) {
            SomaValue child = candidates[i];
            if (!SOMA_IS_PTR(child) || child == 0) continue;
            if (SOMA_TO_PTR(child) == value) continue;

            int duplicate = 0;
            for (int j = 0; j < i; j++) {
                if (candidates[j] == child) {
                    duplicate = 1;
                    break;
                }
            }
            if (duplicate) continue;

            soma_era_free(SOMA_TO_PTR(child));
        }

        soma_pool_free_sup(value);

    } else {
        /* Unknown heap object — use regular free */
        free(value);
    }
}

/*
 * soma_era_tagged_payload — Free a tagged union payload buffer
 *
 * Payload layout: [count : i64, field0 : i64, field1 : i64, ...]
 * Each field is stored as a raw i64 (SomaValue). Fields that are heap pointers
 * (tag bits == TAG_PTR, non-null) are recursively freed via soma_era_free.
 * The count prefix tells us how many fields to walk.
 */
void soma_era_tagged_payload(void* payload) {
    if (payload == NULL) return;

    int64_t count = *(int64_t*)payload;
    SomaValue* fields = (SomaValue*)((int64_t*)payload + 1);

    for (int64_t i = 0; i < count; i++) {
        SomaValue val = fields[i];
        if (SOMA_IS_PTR(val) && val != 0) {
            soma_era_free(SOMA_TO_PTR(val));
        }
    }

    free(payload);
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
    if (cstr == NULL) {
        return NULL;
    }

    size_t len = strlen(cstr);

    SomaString* s = (SomaString*)malloc(sizeof(SomaString));
    if (s == NULL) {
        soma_panic("soma_from_cstring: out of memory");
        return NULL;
    }

    char* data = (char*)malloc(len + 1);
    if (data == NULL) {
        free(s);
        soma_panic("soma_from_cstring: out of memory");
        return NULL;
    }
    memcpy(data, cstr, len + 1);

    s->length = (int64_t)len;
    s->data = data;

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
        if (b == NULL) {
            return soma_from_cstring("");
        }
        return soma_from_cstring(b->data);
    }
    if (b == NULL) {
        return soma_from_cstring(a->data);
    }

    size_t len_a = (size_t)a->length;
    size_t len_b = (size_t)b->length;
    size_t total_len = len_a + len_b;

    SomaString* result = (SomaString*)malloc(sizeof(SomaString));
    if (result == NULL) {
        soma_panic("soma_strcat: out of memory");
        return NULL;
    }

    char* data = (char*)malloc(total_len + 1);
    if (data == NULL) {
        free(result);
        soma_panic("soma_strcat: out of memory");
        return NULL;
    }

    memcpy(data, a->data, len_a);
    memcpy(data + len_a, b->data, len_b);
    data[total_len] = '\0';

    result->length = (int64_t)total_len;
    result->data = data;

    return result;
}

SomaString* soma_int_to_string(int32_t val) {
    char buf[12];
    int len = snprintf(buf, sizeof(buf), "%d", val);

    SomaString* s = (SomaString*)malloc(sizeof(SomaString));
    if (s == NULL) {
        soma_panic("soma_int_to_string: out of memory");
        return NULL;
    }

    char* data = (char*)malloc(len + 1);
    if (data == NULL) {
        free(s);
        soma_panic("soma_int_to_string: out of memory");
        return NULL;
    }
    memcpy(data, buf, len + 1);

    s->length = (int64_t)len;
    s->data = data;

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

#ifndef SOMA_NO_MAIN
extern int soma_main(void);

int main(void) {
    soma_pool_init();
    int result = soma_main();
    soma_pool_cleanup();
    return result;
}
#endif
