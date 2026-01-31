/*
 * Soma Interaction Net Runtime
 * 
 * This runtime provides the core data structures and operations for
 * interaction net reduction with lazy duplication.
 *
 * Memory Layout:
 * 
 * SUP Node (40 bytes):
 *   [0]  u8   tag    (128=fresh, 129=proj0, 130=proj1, 131=both)
 *   [4]  u32  label  (duplication label for annihilation)
 *   [8]  ptr  value  (original value)
 *   [16] ptr  proj0  (cached first projection)
 *   [24] ptr  proj1  (cached second projection)
 *
 * Closure (16 + env_size*8 bytes):
 *   [0]  u8   tag       (NODE_CLOSURE = 1)
 *   [1]  u8   arity     (remaining parameters)
 *   [2]  u16  env_size  (captured variable count)
 *   [8]  ptr  func_ptr  (function pointer)
 *   [16] ptr  env[0]    (first captured value)
 *   [24] ptr  env[1]    (second captured value)
 *   ...
 *
 * Node Tags:
 *   0      = (reserved)
 *   1      = NODE_CLOSURE
 *   2-127  = (reserved for future node types)
 *   128-131 = SUP states (128 + access_state)
 */

#ifndef SOMA_RUNTIME_H
#define SOMA_RUNTIME_H

#include <stdint.h>
#include <stddef.h>

/* Node tag constants (stored in heap objects) */
#define NODE_CLOSURE    1
#define SUP_TAG_BASE    128
#define SUP_TAG_FRESH   128   /* Not yet accessed */
#define SUP_TAG_PROJ0   129   /* proj0 accessed first */
#define SUP_TAG_PROJ1   130   /* proj1 accessed first */
#define SUP_TAG_BOTH    131   /* Both accessed */
#define SUP_TAG_PROJ0_CLONING 132  /* proj0 accessed, speculative clone in progress */
#define SUP_TAG_PROJ1_CLONING 133  /* proj1 accessed, speculative clone in progress */

/* Check if a tag indicates a SUP node */
#define IS_SUP(tag) ((tag) >= SUP_TAG_BASE)

/*
 * Tagged Pointer Representation
 *
 * We use the low 3 bits of pointers for type tags (assuming 8-byte alignment).
 * This allows unboxed representation of small integers and distinguishing
 * value types without dereferencing.
 *
 * Pointer format (64-bit):
 *   [63:3] payload  [2:0] tag
 *
 * Tag values:
 *   000 = Heap pointer (closure, SUP, etc.) - must be 8-byte aligned
 *   001 = Small integer (63-bit signed, shifted right by 3)
 *   010 = Boolean/Unit (payload: 0=false, 1=true, 2=unit)
 *   011 = Character (payload: Unicode codepoint)
 *   100 = (reserved)
 *   101 = (reserved)
 *   110 = (reserved)
 *   111 = (reserved)
 */

#define TAG_BITS        3
#define TAG_MASK        0x7ULL
#define PAYLOAD_SHIFT   3

/* Tag values */
#define TAG_PTR         0   /* Heap pointer */
#define TAG_INT         1   /* Small integer */
#define TAG_BOOL        2   /* Boolean/Unit */
#define TAG_CHAR        3   /* Character */

/* Payload values for TAG_BOOL */
#define BOOL_FALSE      0
#define BOOL_TRUE       1
#define BOOL_UNIT       2

/* Type alias for tagged values */
typedef uintptr_t SomaValue;

/* Check tag */
#define SOMA_GET_TAG(v)      ((v) & TAG_MASK)
#define SOMA_IS_PTR(v)       (SOMA_GET_TAG(v) == TAG_PTR)
#define SOMA_IS_INT(v)       (SOMA_GET_TAG(v) == TAG_INT)
#define SOMA_IS_BOOL(v)      (SOMA_GET_TAG(v) == TAG_BOOL)
#define SOMA_IS_CHAR(v)      (SOMA_GET_TAG(v) == TAG_CHAR)

/* Extract pointer (assumes TAG_PTR) */
#define SOMA_TO_PTR(v)       ((void*)(v))

/* Create/extract small integer */
#define SOMA_INT(n)          ((((SomaValue)(int64_t)(n)) << PAYLOAD_SHIFT) | TAG_INT)
#define SOMA_TO_INT(v)       ((int64_t)(v) >> PAYLOAD_SHIFT)

/* Create/extract boolean */
#define SOMA_FALSE           ((SomaValue)(BOOL_FALSE << PAYLOAD_SHIFT) | TAG_BOOL)
#define SOMA_TRUE            ((SomaValue)(BOOL_TRUE << PAYLOAD_SHIFT) | TAG_BOOL)
#define SOMA_UNIT            ((SomaValue)(BOOL_UNIT << PAYLOAD_SHIFT) | TAG_BOOL)
#define SOMA_TO_BOOL(v)      ((int)(((v) >> PAYLOAD_SHIFT) & 1))

/* Create/extract character */
#define SOMA_CHAR(c)         ((((SomaValue)(c)) << PAYLOAD_SHIFT) | TAG_CHAR)
#define SOMA_TO_CHAR(v)      ((uint32_t)((v) >> PAYLOAD_SHIFT))

/* Create pointer value (for heap objects) */
#define SOMA_PTR(p)          ((SomaValue)(p))

/* SUP node structure */
typedef struct SomaSup {
    uint8_t  tag;
    uint8_t  _pad[3];  /* Padding for alignment */
    uint32_t label;
    void*    value;
    void*    proj0;
    void*    proj1;
} SomaSup;

/* Closure header structure (env follows) */
typedef struct SomaClosure {
    uint8_t  tag;
    uint8_t  arity;
    uint16_t env_size;
    uint32_t _pad;     /* Padding for alignment */
    void*    func_ptr;
    /* void* env[] follows */
} SomaClosure;

/* Global label counter for fresh label generation (atomic for thread-safety) */
#include <stdatomic.h>
extern _Atomic uint32_t soma_label_counter;

/*
 * Core runtime functions
 */

/* Create a lazy SUP node wrapping a value */
void* soma_dup(uint32_t label, void* value);

/* Get first projection from SUP (handles annihilation) */
SomaValue soma_proj0(SomaValue sup);

/* Get second projection from SUP (handles annihilation) */
SomaValue soma_proj1(SomaValue sup);

/* Free a heap-allocated value */
void soma_era_free(void* value);

/* Generate a fresh unique label (thread-safe) */
uint32_t soma_fresh_label(void);

/* Panic: print error message and abort */
void soma_panic(const char* msg);

/*
 * String operations
 *
 * Soma String representation (16 bytes, heap-allocated):
 *   [0]  int64_t length   (string length in bytes)
 *   [8]  char*   data     (pointer to null-terminated UTF-8 data)
 */

typedef struct SomaString {
    int64_t length;
    char*   data;
} SomaString;

/* Convert Soma String to C string (returns data pointer) */
char* soma_to_cstring(SomaValue str);

/* Convert C string to Soma String (allocates new String) */
SomaString* soma_from_cstring(const char* cstr);

/* Get C string length */
uint64_t soma_cstring_len(const char* cstr);

/* Concatenate two Soma Strings (allocates new String) */
SomaString* soma_strcat(SomaString* a, SomaString* b);

/* Convert int32 to Soma String (allocates new String) */
SomaString* soma_int_to_string(int32_t val);

/*
 * Closure operations
 */

/* Allocate a closure with space for env_size captured values */
void* soma_alloc_closure(void* func_ptr, uint8_t arity, uint16_t env_size);

/* Set a closure environment slot */
void soma_closure_set_env(void* closure, uint16_t index, SomaValue value);

/* Get a closure environment slot */
SomaValue soma_closure_get_env(void* closure, uint16_t index);

/* Get function pointer from closure */
void* soma_closure_get_func(void* closure);

/* Deep-clone a closure (memcpy-based) */
void* soma_clone_closure(void* closure);

/*
 * Memory Pool API
 * 
 * Arena-style allocation for reduced malloc overhead.
 * Each pool manages a linked list of fixed-size blocks.
 */

/* Block sizes for different allocation classes */
#define POOL_BLOCK_SIZE     (64 * 1024)  /* 64KB per block */
#define POOL_SUP_SIZE       40           /* sizeof(SomaSup), aligned */
#define POOL_CLOSURE_SMALL  48           /* Closure with 0-3 env slots */
#define POOL_CLOSURE_MEDIUM 112          /* Closure with 4-11 env slots */
/* Large closures (12+ env slots) use malloc */

/* Memory pool structure */
typedef struct SomaPoolBlock {
    struct SomaPoolBlock* next;
    size_t used;
    char data[];
} SomaPoolBlock;

typedef struct SomaPool {
    SomaPoolBlock* blocks;      /* Linked list of blocks */
    size_t item_size;           /* Size of each item in this pool */
    void* free_list;            /* Free list for recycled items */
} SomaPool;

/* Global pools (one per allocation class) */
typedef struct SomaPools {
    SomaPool sup_pool;          /* For SUP nodes */
    SomaPool closure_small;     /* For small closures */
    SomaPool closure_medium;    /* For medium closures */
} SomaPools;

/* Global pool instance */
extern SomaPools soma_pools;

/* Initialize memory pools (call once at startup) */
void soma_pool_init(void);

/* Clean up all pools (call at shutdown) */
void soma_pool_cleanup(void);

/* Allocate from SUP pool */
void* soma_pool_alloc_sup(void);

/* Allocate from closure pool (picks appropriate size class) */
void* soma_pool_alloc_closure(uint16_t env_size);

/* Return to pool's free list */
void soma_pool_free_sup(void* ptr);
void soma_pool_free_closure(void* ptr, uint16_t env_size);

/* Pool statistics (for debugging/profiling) - atomic for thread-safety */
typedef struct SomaPoolStats {
    _Atomic size_t sup_allocs;
    _Atomic size_t sup_frees;
    _Atomic size_t closure_small_allocs;
    _Atomic size_t closure_small_frees;
    _Atomic size_t closure_medium_allocs;
    _Atomic size_t closure_medium_frees;
    _Atomic size_t closure_large_allocs;
    _Atomic size_t closure_large_frees;
    _Atomic size_t blocks_allocated;
    _Atomic size_t bytes_allocated;
} SomaPoolStats;

extern SomaPoolStats soma_pool_stats;

/*
 * Parallel Reduction Support
 *
 * Interaction nets enable lock-free parallel reduction because linear ownership
 * guarantees that each value is consumed exactly once. Independent subgraphs
 * (identified by different DUP labels) can be reduced in parallel.
 *
 * KEY DESIGN PRINCIPLE: Lazy parallelism with demand-driven task spawning
 *
 * SUP = semantic independence, NOT automatic parallelism
 *
 * We spawn parallel tasks ONLY when:
 *   1. A worker is hungry (no local work available)
 *   2. The branch is expected to be expensive (work estimation)
 *   3. The thread pool is not saturated
 *   4. The SUP won't be immediately annihilated (label matching)
 *
 * We DON'T spawn tasks when:
 *   1. Branch is trivial (ERA, small constants, primitives)
 *   2. Worker has local work (no stealing needed)
 *   3. Runtime is overloaded (too many pending tasks)
 *   4. Escape analysis proves no duplication will occur
 *
 * Architecture:
 *   - Work-stealing thread pool with one worker per CPU core
 *   - Chase-Lev deque per worker (lock-free)
 *   - "Hungry" flag per worker signals need for work
 *   - Tasks are thunks: (fn, env) -> SomaValue
 *   - Futures are SUP nodes with pending computation
 */

#include <pthread.h>

/* Configuration */
#ifndef SOMA_MAX_WORKERS
#define SOMA_MAX_WORKERS 64
#endif

#ifndef SOMA_TASK_QUEUE_SIZE
#define SOMA_TASK_QUEUE_SIZE 4096
#endif

/* Work estimation thresholds */
#ifndef SOMA_WORK_THRESHOLD
#define SOMA_WORK_THRESHOLD 50  /* Minimum estimated work to consider parallelism */
#endif

#ifndef SOMA_MAX_PENDING_TASKS
#define SOMA_MAX_PENDING_TASKS 1024  /* Don't spawn if more than this pending */
#endif

/* Forward declarations */
typedef struct SomaTask SomaTask;
typedef struct SomaWorker SomaWorker;
typedef struct SomaParRuntime SomaParRuntime;

/* Task function signatures */
typedef SomaValue (*SomaTaskFn)(void* env);           /* Generic: env is opaque pointer */
typedef SomaValue (*SomaDirectFn)(SomaValue arg);     /* Direct: single i64 argument */
typedef SomaValue (*SomaClosureFn)(void* closure, SomaValue arg);  /* Closure: closure_self + arg */
typedef SomaValue (*SomaTrampolineFn)(SomaValue* args);  /* Trampoline: takes ptr to args array */

/* Task states */
#define TASK_PENDING    0
#define TASK_RUNNING    1
#define TASK_DONE       2
#define TASK_STOLEN     3

/* Task kind */
#define TASK_KIND_GENERIC   0   /* fn(env) - original API */
#define TASK_KIND_DIRECT    1   /* fn(arg) - direct i64 call */
#define TASK_KIND_CLOSURE   2   /* fn(closure, arg) - closure call */
#define TASK_KIND_TRAMPOLINE 3  /* fn(args_ptr) - trampoline with args array pointer */

/* Task structure */
struct SomaTask {
    _Atomic int state;
    uint8_t kind;               /* TASK_KIND_* */
    union {
        SomaTaskFn generic;     /* For TASK_KIND_GENERIC */
        SomaDirectFn direct;    /* For TASK_KIND_DIRECT */
        SomaClosureFn closure;  /* For TASK_KIND_CLOSURE */
        SomaTrampolineFn trampoline;  /* For TASK_KIND_TRAMPOLINE */
    } fn;
    void* env;                  /* env for generic, args array for trampoline */
    SomaValue arg;              /* arg for direct/closure, num_args for trampoline */
    SomaValue result;
    uint32_t work_estimate;     /* Estimated work units */
};

/* Chase-Lev work-stealing deque */
typedef struct {
    _Atomic size_t top;
    _Atomic size_t bottom;
    _Atomic(SomaTask*) buffer[SOMA_TASK_QUEUE_SIZE];
} SomaDeque;

/* Worker thread state */
struct SomaWorker {
    pthread_t thread;
    int id;
    SomaDeque deque;
    _Atomic int hungry;         /* 1 = looking for work to steal */
    _Atomic int active;
    SomaParRuntime* runtime;
    
    /* Per-worker stats */
    uint64_t tasks_run;
    uint64_t tasks_stolen;
    uint64_t steal_attempts;
};

/* Global runtime */
struct SomaParRuntime {
    int num_workers;
    SomaWorker workers[SOMA_MAX_WORKERS];
    _Atomic int shutdown;
    _Atomic size_t pending_tasks;
    _Atomic size_t hungry_count;  /* How many workers are hungry */
    
    /* Task pool for recycling */
    SomaTask* task_pool;
    _Atomic size_t task_pool_size;
    pthread_mutex_t task_pool_lock;
};

extern SomaParRuntime soma_par;

/*
 * Runtime Lifecycle
 */

/* Initialize parallel runtime (0 = auto-detect cores) */
void soma_par_init(int num_workers);

/* Shutdown and join all workers */
void soma_par_shutdown(void);

/* Check if parallel runtime is enabled */
static inline int soma_par_enabled(void) {
    return soma_par.num_workers > 0;
}

/*
 * Demand-Driven Task Spawning
 *
 * The key insight: only spawn tasks when workers are hungry.
 * This avoids the overhead of task creation when there's no benefit.
 */

/* Check if any worker is hungry (needs work) */
static inline int soma_par_workers_hungry(void) {
    return atomic_load_explicit(&soma_par.hungry_count, memory_order_relaxed) > 0;
}

/* Check if we should spawn a parallel task for given work estimate */
static inline int soma_par_should_spawn(uint32_t work_estimate) {
    if (!soma_par_enabled()) return 0;
    if (work_estimate < SOMA_WORK_THRESHOLD) return 0;
    if (!soma_par_workers_hungry()) return 0;
    if (atomic_load(&soma_par.pending_tasks) >= SOMA_MAX_PENDING_TASKS) return 0;
    return 1;
}

/*
 * Work Estimation
 *
 * Heuristic to estimate computational cost of a closure/thunk.
 * Used to decide whether parallelization is worthwhile.
 */

/* Estimate work for a closure (based on arity + env_size) */
static inline uint32_t soma_estimate_closure_work(void* ptr) {
    if (!SOMA_IS_PTR((SomaValue)ptr) || ptr == NULL) return 1;
    uint8_t tag = *(uint8_t*)ptr;
    if (tag != NODE_CLOSURE) return 1;
    SomaClosure* c = (SomaClosure*)ptr;
    /* Heuristic: more env slots = more complex captured state */
    /* More arity = more applications to come */
    return 10 + (c->env_size * 5) + (c->arity * 20);
}

/* Estimate work for a SUP's inner value */
static inline uint32_t soma_estimate_sup_work(SomaSup* sup) {
    void* value = sup->value;
    if (!SOMA_IS_PTR((SomaValue)value) || value == NULL) return 1;
    uint8_t tag = *(uint8_t*)value;
    if (tag == NODE_CLOSURE) {
        return soma_estimate_closure_work(value);
    }
    if (IS_SUP(tag)) {
        /* Nested SUP = potentially more parallel work */
        return 30;
    }
    return 5;
}

/*
 * Task API
 */

/* Allocate a task (from pool or malloc) */
SomaTask* soma_task_alloc(void);

/* Free a task (return to pool) */
void soma_task_free(SomaTask* task);

/* Spawn a task on current worker's deque */
void soma_par_spawn(SomaTask* task);

/* Try to pop a task from local deque (LIFO) */
SomaTask* soma_par_pop(SomaWorker* worker);

/* Try to steal a task from another worker (FIFO from victim's top) */
SomaTask* soma_par_steal(SomaWorker* thief, SomaWorker* victim);

/* Execute a task and return its result */
SomaValue soma_par_run_task(SomaTask* task);

/*
 * Parallel SUP Projection
 *
 * When projecting from a SUP where the other projection might benefit
 * from parallel execution, we can optionally spawn it as a task.
 *
 * This is the main integration point with the existing runtime.
 */

/* Parallel-aware projection with compile-time work hint
 * The work_hint is a compile-time estimate; runtime may also estimate dynamically.
 * If workers are hungry and work is above threshold, may spawn speculative tasks.
 */
SomaValue soma_par_proj0(SomaValue sup_val, uint32_t work_hint);
SomaValue soma_par_proj1(SomaValue sup_val, uint32_t work_hint);

/*
 * Fork-Join Parallelism API
 *
 * Structured parallelism for independent computations in compose blocks.
 * Zero overhead when SOMA_WORKERS is not set (compiles to direct calls).
 */

/* Fork a computation - spawns task and returns immediately
 * fn: function pointer taking env and returning SomaValue
 * env: captured environment (moved to task, caller loses ownership)
 * Returns: task handle (opaque pointer), or NULL if parallel disabled
 */
SomaTask* soma_fork(SomaTaskFn fn, void* env);

/* Fork a direct function call - for functions taking single i64 argument
 * fn: function pointer (SomaValue (*)(SomaValue))
 * arg: the argument value
 * Returns: task handle, or NULL if parallel disabled
 */
SomaTask* soma_fork_direct(SomaDirectFn fn, SomaValue arg);

/* Fork a closure call - for closures with single argument
 * fn: closure's function pointer (SomaValue (*)(void* closure, SomaValue arg))
 * closure: the closure pointer (passed as first arg)
 * arg: the argument value
 * Returns: task handle, or NULL if parallel disabled
 */
SomaTask* soma_fork_closure(SomaClosureFn fn, void* closure, SomaValue arg);

/* Fork with multiple arguments
 * fn: function pointer (takes N i64 args, returns i64)
 * args: array of arguments (copied by this function)
 * num_args: number of arguments
 * Returns: task handle, or NULL if parallel disabled
 */
SomaTask* soma_fork_multi(void* fn, SomaValue* args, int num_args);

/* Join a task - blocks until complete, returns result
 * task: handle from soma_fork*
 * Returns: the computation's result (ownership transferred to caller)
 * Note: task handle is freed after join
 * Note: if task is NULL, returns 0 (caller should have executed inline)
 */
SomaValue soma_join(SomaTask* task);

/*
 * Statistics - atomic for thread-safety
 */
typedef struct {
    _Atomic uint64_t tasks_spawned;
    _Atomic uint64_t tasks_run;              /* Run by worker threads */
    _Atomic uint64_t tasks_run_inline;       /* Run inline by joining thread */
    _Atomic uint64_t tasks_stolen;
    _Atomic uint64_t spawn_skipped_trivial;     /* Skipped: work too small */
    _Atomic uint64_t spawn_skipped_saturated;   /* Skipped: pool saturated */
    _Atomic uint64_t spawn_skipped_no_hungry;   /* Skipped: no hungry workers */
    _Atomic uint64_t speculative_clones;        /* Speculative clone tasks spawned */
} SomaParStats;

extern SomaParStats soma_par_stats;

void soma_par_print_stats(void);

/*
 * Thread-Local Worker Access
 */
extern __thread SomaWorker* soma_current_worker;

/* Get current worker (NULL if main thread or not in parallel context) */
static inline SomaWorker* soma_par_current_worker(void) {
    return soma_current_worker;
}

#endif /* SOMA_RUNTIME_H */