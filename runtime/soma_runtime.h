/*
 * Soma Runtime
 * 
 *
 * Memory Layout:
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
 *   0x80+  = SUP_TAG_* (superposition nodes for lazy duplication)
 */

#ifndef SOMA_RUNTIME_H
#define SOMA_RUNTIME_H

#include <stdint.h>
#include <stddef.h>
#include <stdatomic.h>

/* Node tag constants (stored in heap objects) */
#define NODE_CLOSURE    1

/* Runtime object validation sentinels */
#define SOMA_CLOSURE_MAGIC 0x534f4d41u /* 'SOMA' */
#define SOMA_SUP_PAD0 0x53u            /* 'S' */
#define SOMA_SUP_PAD1 0x55u            /* 'U' */
#define SOMA_SUP_PAD2 0x50u            /* 'P' */

/*
 * SUP (Superposition) Node Tags
 *
 * SUP nodes implement lazy duplication for Tier 3 values (recursive data).
 * Instead of eagerly cloning, a DUP creates a SUP wrapping the value.
 * When projections access the SUP, cloning is deferred until both sides
 * are needed. Same-label DUP-SUP pairs annihilate in O(1).
 *
 * Tag encodes the lifecycle state of the SUP:
 *   FRESH        → neither projection accessed yet
 *   PROJ0        → first projection (proj0) accessed
 *   PROJ1        → second projection (proj1) accessed
 *   BOTH         → both projections accessed, value cloned
 *   PROJ0_CLONING → proj0 accessed, speculative clone in flight for proj1
 *   PROJ1_CLONING → proj1 accessed, speculative clone in flight for proj0
 */
#define SUP_TAG_FRESH         0x80
#define SUP_TAG_PROJ0         0x81
#define SUP_TAG_PROJ1         0x82
#define SUP_TAG_BOTH          0x83
#define SUP_TAG_PROJ0_CLONING 0x84
#define SUP_TAG_PROJ1_CLONING 0x85

/* Check if a tag byte indicates a SUP node */
#define IS_SUP(tag)  (((tag) & 0x80) != 0)

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
 *   000 = Heap pointer (closure, etc.) - must be 8-byte aligned
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

/* Closure header structure (env follows) */
typedef struct SomaClosure {
    uint8_t  tag;
    uint8_t  arity;
    uint16_t env_size;
    uint32_t _pad;     /* Padding for alignment */
    void*    func_ptr;
    /* void* env[] follows */
} SomaClosure;

/*
 * SUP (Superposition) node structure (40 bytes, pool-allocated)
 *
 *   [0]  u8       tag     (SUP_TAG_*)
 *   [4]  u32      label   (duplication label for annihilation matching)
 *   [8]  void*    value   (the wrapped value)
 *   [16] void*    proj0   (cached first projection / clone task)
 *   [24] void*    proj1   (cached second projection / clone task)
 */
typedef struct SomaSup {
    uint8_t  tag;
    uint8_t  _pad[3];
    uint32_t label;
    void*    value;
    void*    proj0;
    void*    proj1;
} SomaSup;

/*
 * Core runtime functions
 */

/* Free a heap-allocated value */
void soma_era_free(void* value);

/* Free a Soma String object (header + owned data) */
void soma_era_string(void* value);

/* Free a tagged union payload buffer (count-prefixed array of fields) */
void soma_era_tagged_payload(void* payload);

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
char* soma_to_cstring(SomaString* str);

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

/* Clone a closure under a statically assigned DUP label */
void* soma_clone_closure(void* closure, uint32_t label);

/* Clone a tagged payload buffer, recursively cloning pointer fields */
void* soma_clone_tagged_payload(void* payload, uint32_t label);

/* Clone an array header { length, data_ptr } and recursively clone data pointer */
void* soma_clone_array_header(void* header, uint32_t label);

/*
 * SUP (Superposition) operations — Tier 3 lazy duplication
 */

/* Runtime fresh labels are disabled; labels must be compiler-assigned */
uint32_t soma_fresh_label(void);

/* Create a SUP node wrapping a value for lazy duplication */
SomaValue soma_dup(uint32_t label, SomaValue value);

/* Extract first projection from a SUP */
SomaValue soma_proj0(SomaValue sup_val);

/* Extract second projection from a SUP */
SomaValue soma_proj1(SomaValue sup_val);

/*
 * Memory Pool API
 * 
 * Arena-style allocation for reduced malloc overhead.
 * Each pool manages a linked list of fixed-size blocks.
 */

/* Block sizes for different allocation classes */
#define POOL_BLOCK_SIZE     (64 * 1024)  /* 64KB per block */
#define POOL_SUP_SIZE       40           /* SomaSup struct */
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

/* Return SUP to pool's free list */
void soma_pool_free_sup(void* ptr);

/* Allocate from closure pool (picks appropriate size class) */
void* soma_pool_alloc_closure(uint16_t env_size);

/* Return to pool's free list */
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


#include <pthread.h>

/* Configuration */
#ifndef SOMA_MAX_WORKERS
#define SOMA_MAX_WORKERS 64
#endif

#ifndef SOMA_TASK_QUEUE_SIZE
#define SOMA_TASK_QUEUE_SIZE 4096
#endif

/* Forward declarations */
typedef struct SomaTask SomaTask;
typedef struct SomaWorker SomaWorker;
typedef struct SomaParRuntime SomaParRuntime;

/* Task function signatures */
typedef SomaValue (*SomaTaskFn)(void* env);
typedef SomaValue (*SomaDirectFn)(SomaValue arg);
typedef SomaValue (*SomaClosureFn)(void* closure, SomaValue arg);
typedef SomaValue (*SomaTrampolineFn)(SomaValue* args);

/* Task states */
#define TASK_PENDING    0
#define TASK_RUNNING    1
#define TASK_DONE       2
#define TASK_STOLEN     3

/* Task kind */
#define TASK_KIND_GENERIC   0
#define TASK_KIND_DIRECT    1
#define TASK_KIND_CLOSURE   2
#define TASK_KIND_TRAMPOLINE 3

/* Task structure */
struct SomaTask {
    _Atomic int state;
    uint8_t kind;
    union {
        SomaTaskFn generic;
        SomaDirectFn direct;
        SomaClosureFn closure;
        SomaTrampolineFn trampoline;
    } fn;
    void* env;
    SomaValue arg;
    SomaValue result;
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
    _Atomic int hungry;
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
    _Atomic size_t hungry_count;
    
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
 * Task API
 */

SomaTask* soma_task_alloc(void);
void soma_task_free(SomaTask* task);
void soma_par_spawn(SomaTask* task);
SomaTask* soma_par_pop(SomaWorker* worker);
SomaTask* soma_par_steal(SomaWorker* thief, SomaWorker* victim);
SomaValue soma_par_run_task(SomaTask* task);

/*
 * Fork-Join API
 */

SomaTask* soma_fork(SomaTaskFn fn, void* env);
SomaTask* soma_fork_direct(SomaDirectFn fn, SomaValue arg);
SomaTask* soma_fork_closure(SomaClosureFn fn, void* closure, SomaValue arg);
SomaTask* soma_fork_multi(void* fn, SomaValue* args, int num_args);
SomaValue soma_join(SomaTask* task);

/*
 * Statistics
 */
typedef struct {
    _Atomic uint64_t tasks_spawned;
    _Atomic uint64_t tasks_run;
    _Atomic uint64_t tasks_run_inline;
    _Atomic uint64_t tasks_stolen;
} SomaParStats;

extern SomaParStats soma_par_stats;

void soma_par_print_stats(void);

/*
 * Thread-Local Worker Access
 */
extern __thread SomaWorker* soma_current_worker;

static inline SomaWorker* soma_par_current_worker(void) {
    return soma_current_worker;
}

#endif /* SOMA_RUNTIME_H */
