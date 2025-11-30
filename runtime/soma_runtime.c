/*
 * Soma Interaction Net Runtime
 *
 * Implements lazy duplication with HVM-style label-based annihilation.
 */

#include "soma_runtime.h"
#include <stdlib.h>
#include <string.h>
#include <stdatomic.h>
#include <stdio.h>

/* Global label counter (atomic for future parallel support) */
_Atomic uint32_t soma_label_counter = 0;

/* Global memory pools */
SomaPools soma_pools;
SomaPoolStats soma_pool_stats;

/*
 * Memory Pool Implementation
 */

/* Allocate a new block for a pool */
static SomaPoolBlock* pool_alloc_block(void) {
    SomaPoolBlock* block = (SomaPoolBlock*)malloc(
        sizeof(SomaPoolBlock) + POOL_BLOCK_SIZE
    );
    if (block) {
        block->next = NULL;
        block->used = 0;
        soma_pool_stats.blocks_allocated++;
        soma_pool_stats.bytes_allocated += sizeof(SomaPoolBlock) + POOL_BLOCK_SIZE;
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
    soma_pool_stats.sup_allocs++;
    return pool_alloc(&soma_pools.sup_pool);
}

void* soma_pool_alloc_closure(uint16_t env_size) {
    size_t needed = sizeof(SomaClosure) + (env_size * sizeof(void*));

    if (needed <= POOL_CLOSURE_SMALL) {
        soma_pool_stats.closure_small_allocs++;
        return pool_alloc(&soma_pools.closure_small);
    }
    if (needed <= POOL_CLOSURE_MEDIUM) {
        soma_pool_stats.closure_medium_allocs++;
        return pool_alloc(&soma_pools.closure_medium);
    }

    /* Large closure - fall back to malloc */
    soma_pool_stats.closure_large_allocs++;
    return malloc(needed);
}

void soma_pool_free_sup(void* ptr) {
    soma_pool_stats.sup_frees++;
    pool_free(&soma_pools.sup_pool, ptr);
}

void soma_pool_free_closure(void* ptr, uint16_t env_size) {
    size_t needed = sizeof(SomaClosure) + (env_size * sizeof(void*));

    if (needed <= POOL_CLOSURE_SMALL) {
        soma_pool_stats.closure_small_frees++;
        pool_free(&soma_pools.closure_small, ptr);
    } else if (needed <= POOL_CLOSURE_MEDIUM) {
        soma_pool_stats.closure_medium_frees++;
        pool_free(&soma_pools.closure_medium, ptr);
    } else {
        soma_pool_stats.closure_large_frees++;
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
 * Note: Values can be tagged pointers (ints, bools, chars) which don't
 * need cloning, or heap pointers (closures, SUPs) which may need special handling.
 */
SomaValue soma_proj0(SomaValue sup_val) {
    SomaSup* sup = (SomaSup*)SOMA_TO_PTR(sup_val);
    uint8_t tag = sup->tag;

    /* Fresh - first access via proj0 */
    if (tag == SUP_TAG_FRESH) {
        sup->tag = SUP_TAG_PROJ0;
        SomaValue value = (SomaValue)sup->value;

        /* Check for annihilation: is value a SUP with same label? */
        if (is_heap_sup(value)) {
            SomaSup* inner = (SomaSup*)SOMA_TO_PTR(value);
            if (inner->label == sup->label) {
                /* Annihilate: return inner's value directly */
                sup->proj0 = inner->value;
                return (SomaValue)inner->value;
            }
        }

        /* No annihilation - cache and return value */
        sup->proj0 = (void*)value;
        return value;
    }

    /* proj1 was accessed first - need to handle second access */
    if (tag == SUP_TAG_PROJ1) {
        sup->tag = SUP_TAG_BOTH;
        SomaValue value = (SomaValue)sup->value;

        /* Tagged values (int, bool, char) don't need cloning */
        if (!SOMA_IS_PTR(value) || value == 0) {
            sup->proj0 = (void*)value;
            return value;
        }

        /* Check for annihilation */
        if (is_heap_sup(value)) {
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
        if (is_heap_closure(value)) {
            void* cloned = soma_clone_closure(SOMA_TO_PTR(value));
            sup->proj0 = cloned;
            return SOMA_PTR(cloned);
        }

        /* Unknown heap object - shallow copy */
        sup->proj0 = (void*)value;
        return value;
    }

    /* Already accessed (PROJ0 or BOTH) - return cached */
    return (SomaValue)sup->proj0;
}

/*
 * soma_proj1 - Get second projection from SUP
 *
 * Symmetric to soma_proj0.
 */
SomaValue soma_proj1(SomaValue sup_val) {
    SomaSup* sup = (SomaSup*)SOMA_TO_PTR(sup_val);
    uint8_t tag = sup->tag;

    /* Fresh - first access via proj1 */
    if (tag == SUP_TAG_FRESH) {
        sup->tag = SUP_TAG_PROJ1;
        SomaValue value = (SomaValue)sup->value;

        /* Check for annihilation */
        if (is_heap_sup(value)) {
            SomaSup* inner = (SomaSup*)SOMA_TO_PTR(value);
            if (inner->label == sup->label) {
                /* Annihilate: return inner's value */
                sup->proj1 = inner->value;
                return (SomaValue)inner->value;
            }
        }

        /* No annihilation - cache and return value */
        sup->proj1 = (void*)value;
        return value;
    }

    /* proj0 was accessed first - need to handle second access */
    if (tag == SUP_TAG_PROJ0) {
        sup->tag = SUP_TAG_BOTH;
        SomaValue value = (SomaValue)sup->value;

        /* Tagged values (int, bool, char) don't need cloning */
        if (!SOMA_IS_PTR(value) || value == 0) {
            sup->proj1 = (void*)value;
            return value;
        }

        /* Check for annihilation */
        if (is_heap_sup(value)) {
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
        if (is_heap_closure(value)) {
            void* cloned = soma_clone_closure(SOMA_TO_PTR(value));
            sup->proj1 = cloned;
            return SOMA_PTR(cloned);
        }

        /* Unknown heap object - shallow copy */
        sup->proj1 = (void*)value;
        return value;
    }

    /* Already accessed (PROJ1 or BOTH) - return cached */
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
 * soma_clone_closure - Deep-clone a closure
 *
 * Copies the header and all environment slots.
 * TODO: For HVM-style incremental cloning, wrap closure-typed
 * env slots in SUPs instead of copying directly.
 */
void* soma_clone_closure(void* closure_ptr) {
    SomaClosure* closure = (SomaClosure*)closure_ptr;
    uint16_t env_size = closure->env_size;
    size_t total_size = sizeof(SomaClosure) + (env_size * sizeof(void*));

    void* new_closure = soma_pool_alloc_closure(env_size);
    memcpy(new_closure, closure, total_size);

    return new_closure;
}

/*
 * ============================================================================
 * Parallel Runtime Implementation
 * ============================================================================
 *
 * Work-stealing thread pool with demand-driven task spawning.
 * Key insight: only spawn parallel tasks when workers are hungry.
 */

#include <unistd.h>
#include <sched.h>

/* Global parallel runtime state */
SomaParRuntime soma_par = {0};
SomaParStats soma_par_stats = {0};

/* Thread-local current worker pointer */
__thread SomaWorker* soma_current_worker = NULL;

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

#define TASK_POOL_INITIAL_SIZE 256

SomaTask* soma_task_alloc(void) {
    /* Try pool first */
    pthread_mutex_lock(&soma_par.task_pool_lock);
    if (soma_par.task_pool != NULL) {
        SomaTask* task = soma_par.task_pool;
        soma_par.task_pool = *(SomaTask**)task;  /* Next pointer stored in task */
        pthread_mutex_unlock(&soma_par.task_pool_lock);
        return task;
    }
    pthread_mutex_unlock(&soma_par.task_pool_lock);
    
    /* Allocate new */
    return (SomaTask*)malloc(sizeof(SomaTask));
}

void soma_task_free(SomaTask* task) {
    pthread_mutex_lock(&soma_par.task_pool_lock);
    *(SomaTask**)task = soma_par.task_pool;
    soma_par.task_pool = task;
    pthread_mutex_unlock(&soma_par.task_pool_lock);
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
    
    while (!atomic_load(&soma_par.shutdown)) {
        /* Try to pop from own deque first */
        SomaTask* task = deque_pop(&self->deque);
        
        if (task == NULL) {
            /* Mark as hungry and try to steal */
            worker_set_hungry(self, 1);
            
            /* Try stealing from random victim */
            int victim_id = (self->id + 1) % soma_par.num_workers;
            for (int attempts = 0; attempts < soma_par.num_workers; attempts++) {
                if (victim_id != self->id) {
                    SomaWorker* victim = &soma_par.workers[victim_id];
                    task = deque_steal(&victim->deque);
                    self->steal_attempts++;
                    if (task != NULL) {
                        self->tasks_stolen++;
                        worker_set_hungry(self, 0);
                        break;
                    }
                }
                victim_id = (victim_id + 1) % soma_par.num_workers;
            }
            
            if (task == NULL) {
                /* No work available, yield CPU */
                sched_yield();
                continue;
            }
        } else {
            worker_set_hungry(self, 0);
        }
        
        /* Execute the task */
        int expected = TASK_PENDING;
        if (atomic_compare_exchange_strong(&task->state, &expected, TASK_RUNNING)) {
            task->result = task->fn(task->env);
            atomic_store(&task->state, TASK_DONE);
            atomic_fetch_sub(&soma_par.pending_tasks, 1);
            self->tasks_run++;
            soma_par_stats.tasks_run++;
        }
    }
    
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
    atomic_store(&soma_par.hungry_count, 0);
    soma_par.task_pool = NULL;
    pthread_mutex_init(&soma_par.task_pool_lock, NULL);
    
    /* Pre-allocate task pool */
    for (int i = 0; i < TASK_POOL_INITIAL_SIZE; i++) {
        SomaTask* t = (SomaTask*)malloc(sizeof(SomaTask));
        soma_task_free(t);
    }
    
    /* Start worker threads */
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
        pthread_create(&w->thread, NULL, worker_main, w);
    }
}

void soma_par_shutdown(void) {
    if (soma_par.num_workers == 0) return;
    
    /* Signal shutdown */
    atomic_store(&soma_par.shutdown, 1);
    
    /* Join all workers */
    for (int i = 0; i < soma_par.num_workers; i++) {
        pthread_join(soma_par.workers[i].thread, NULL);
    }
    
    /* Free task pool */
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
    soma_par_stats.tasks_spawned++;
    
    if (w != NULL) {
        /* Push to current worker's deque */
        deque_push(&w->deque, task);
    } else {
        /* Main thread: push to worker 0's deque */
        deque_push(&soma_par.workers[0].deque, task);
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
        task->result = task->fn(task->env);
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
 * Parallel SUP Projection
 *
 * These functions are parallel-aware wrappers around soma_proj0/1.
 * They take a compile-time work_hint from the compiler and combine it
 * with runtime estimation to decide whether to track statistics.
 *
 * Note: Without thunk functions, we can't actually spawn the other branch
 * as a task here. The parallel benefit comes from:
 * 1. The workers being available to steal work spawned elsewhere
 * 2. Future: compiler could generate thunk closures for expensive branches
 *
 * For now, these functions just do the projection and track statistics
 * to help tune the parallel threshold.
 */

SomaValue soma_par_proj0(SomaValue sup_val, uint32_t work_hint) {
    /* Do the normal projection */
    SomaValue result = soma_proj0(sup_val);
    
    /* Track statistics for tuning */
    if (soma_par_enabled()) {
        /* Combine compile-time hint with runtime estimate */
        uint32_t work = work_hint;
        if (SOMA_IS_PTR(sup_val) && sup_val != 0) {
            SomaSup* sup = (SomaSup*)SOMA_TO_PTR(sup_val);
            uint32_t runtime_est = soma_estimate_sup_work(sup);
            /* Use max of hint and runtime estimate */
            if (runtime_est > work) work = runtime_est;
        }
        
        /* Track what would have happened */
        if (work < SOMA_WORK_THRESHOLD) {
            soma_par_stats.spawn_skipped_trivial++;
        } else if (!soma_par_workers_hungry()) {
            soma_par_stats.spawn_skipped_no_hungry++;
        } else if (atomic_load(&soma_par.pending_tasks) >= SOMA_MAX_PENDING_TASKS) {
            soma_par_stats.spawn_skipped_saturated++;
        }
        /* Note: actual task spawning requires thunk generation in compiler */
    }
    
    return result;
}

SomaValue soma_par_proj1(SomaValue sup_val, uint32_t work_hint) {
    SomaValue result = soma_proj1(sup_val);
    
    if (soma_par_enabled()) {
        uint32_t work = work_hint;
        if (SOMA_IS_PTR(sup_val) && sup_val != 0) {
            SomaSup* sup = (SomaSup*)SOMA_TO_PTR(sup_val);
            uint32_t runtime_est = soma_estimate_sup_work(sup);
            if (runtime_est > work) work = runtime_est;
        }
        
        if (work < SOMA_WORK_THRESHOLD) {
            soma_par_stats.spawn_skipped_trivial++;
        } else if (!soma_par_workers_hungry()) {
            soma_par_stats.spawn_skipped_no_hungry++;
        } else if (atomic_load(&soma_par.pending_tasks) >= SOMA_MAX_PENDING_TASKS) {
            soma_par_stats.spawn_skipped_saturated++;
        }
    }
    
    return result;
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
    fprintf(stderr, "[soma_par] Tasks spawned: %lu\n", soma_par_stats.tasks_spawned);
    fprintf(stderr, "[soma_par] Tasks run: %lu\n", soma_par_stats.tasks_run);
    fprintf(stderr, "[soma_par] Tasks stolen: %lu\n", soma_par_stats.tasks_stolen);
    fprintf(stderr, "[soma_par] Skipped (trivial): %lu\n", soma_par_stats.spawn_skipped_trivial);
    fprintf(stderr, "[soma_par] Skipped (not hungry): %lu\n", soma_par_stats.spawn_skipped_no_hungry);
    fprintf(stderr, "[soma_par] Skipped (saturated): %lu\n", soma_par_stats.spawn_skipped_saturated);
    
    for (int i = 0; i < soma_par.num_workers; i++) {
        SomaWorker* w = &soma_par.workers[i];
        fprintf(stderr, "[soma_par] Worker %d: run=%lu stolen=%lu attempts=%lu\n",
                i, w->tasks_run, w->tasks_stolen, w->steal_attempts);
    }
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
