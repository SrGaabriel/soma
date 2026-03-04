/*
 * Soma Runtime
 *
 * All heap objects share a common 8-byte header:
 *   [0]  u8   tag       (NODE_* constant identifying the object type)
 *   [1]  u8[3]          (type-specific or padding)
 *   [4]  u32            (validation sentinel / type-specific)
 *
 * Memory Layout:
 *
 * Closure (16 + env_size*8 bytes):
 *   [0]  u8   tag       (NODE_CLOSURE = 1)
 *   [1]  u8   arity     (remaining parameters)
 *   [2]  u16  env_size  (captured variable count)
 *   [4]  u32  _pad      (SOMA_CLOSURE_MAGIC)
 *   [8]  ptr  func_ptr  (function pointer)
 *   [16] ptr  env[0]    ...
 *
 * String (16 + length + 1 bytes, contiguous):
 *   [0]  u8   tag       (NODE_STRING = 2)
 *   [1]  u8[3] _pad
 *   [4]  u32  _magic    (SOMA_STRING_MAGIC)
 *   [8]  i64  length
 *   [16] char data[]    (inline, null-terminated)
 *
 * Tagged Payload (16 + count*8 bytes):
 *   [0]  u8   tag       (NODE_TAGGED_PAYLOAD = 3)
 *   [1]  u8[3] _pad
 *   [4]  u32  _magic    (SOMA_TAGGED_MAGIC)
 *   [8]  i64  count     (number of fields)
 *   [16] i64  field[0]  ...
 *
 * SUP (40 bytes, pool-allocated):
 *   [0]  u8   tag       (SUP_TAG_* = 0x80+)
 *   [1]  u8[3] _pad     ('S','U','P')
 *   [4]  u32  label
 *   [8]  ptr  value
 *   [16] ptr  proj0
 *   [24] ptr  proj1
 *
 * Node Tags:
 *   0      = (reserved/invalid)
 *   1      = NODE_CLOSURE
 *   2      = NODE_STRING
 *   3      = NODE_TAGGED_PAYLOAD
 *   4      = NODE_FLAT_ARRAY
 *   5-127  = (reserved for future node types)
 *   0x80+  = SUP_TAG_* (superposition nodes for lazy duplication)
 */

#ifndef SOMA_RUNTIME_H
#define SOMA_RUNTIME_H

#include <stdint.h>
#include <stddef.h>
#include <stdatomic.h>

/* Node tag constants (stored at byte 0 of every heap object) */
#define NODE_CLOSURE          1
#define NODE_STRING           2
#define NODE_TAGGED_PAYLOAD   3
#define NODE_FLAT_ARRAY       4
/* Runtime object validation sentinels */
#define SOMA_CLOSURE_MAGIC 0x534f4d41u /* 'SOMA' */
#define SOMA_STRING_MAGIC  0x53545247u /* 'STRG' */
#define SOMA_TAGGED_MAGIC  0x54414750u /* 'TAGP' */
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

/* Free a Soma String object (contiguous header + inline data) */
void soma_era_string(void* value);

/* Free a tagged union payload buffer (count-prefixed array of fields) */
void soma_era_tagged_payload(void* payload);

/* Panic: print error message and abort */
void soma_panic(const char* msg);

/*
 * String operations
 */

typedef struct SomaString {
    uint8_t  tag;       /* NODE_STRING */
    uint8_t  _pad[3];
    uint32_t _magic;    /* SOMA_STRING_MAGIC */
    int64_t  length;
    char     data[];    /* flexible array member: string data inline */
} SomaString;

/*
 * Tagged payload (variable-size, count-prefixed field array)
 */

typedef struct SomaTaggedPayload {
    uint8_t  tag;       /* NODE_TAGGED_PAYLOAD */
    uint8_t  _pad[3];
    uint32_t _magic;    /* SOMA_TAGGED_MAGIC */
    int64_t  count;
    /* SomaValue fields[] follows at offset 16 */
} SomaTaggedPayload;

/*
 * Flat array (compiler-generated, for church-encoded lists)
 *
 * Reference-counted immutable array. DUP increments the refcount and
 * shares the pointer (O(1), zero allocation). ERA decrements the refcount
 * and frees when it reaches zero. Safe because Soma is pure — arrays are
 * never mutated, so sharing is always correct.
 *
 * Layout:
 *   [0]  u8   tag         (NODE_FLAT_ARRAY = 4)
 *   [1]  u8   elem_size   (bytes per element: 1/2/4/8)
 *   [2]  u8[2] _pad
 *   [4]  u32  refcount    (atomic reference count, starts at 1)
 *   [8]  i64  length      (number of elements)
 *   [16] data             (length * elem_size bytes of contiguous element data)
 */
typedef struct SomaFlatArray {
    uint8_t   tag;         /* NODE_FLAT_ARRAY */
    uint8_t   elem_size;   /* bytes per element */
    uint8_t   _pad[2];
    _Atomic uint32_t refcount;  /* reference count */
    int64_t   length;
    /* element data follows at offset 16 */
} SomaFlatArray;


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

/* Allocate a tagged payload buffer with count prefix initialized */
void* soma_alloc_tagged_payload(uint64_t field_count);


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

/*
 * Size-class pool allocator.
 *
 * Three pools cover all fixed-size heap objects:
 *   pool_40  — SUP nodes (40 bytes)
 *   pool_48  — small objects ≤48 bytes:
 *              closures (0-4 env), strings (≤31 chars), tagged payloads (≤4 fields),
 *              array headers (24 bytes)
 *   pool_112 — medium objects ≤112 bytes:
 *              closures (5-12 env), strings (≤95 chars), tagged payloads (≤12 fields)
 *
 * Larger objects fall through to malloc.
 * Pools are TLS-local for lock-free allocation on worker threads.
 */

#define POOL_BLOCK_SIZE  (64 * 1024)  /* 64KB per block */
#define POOL_SIZE_40     40           /* SUP nodes */
#define POOL_SIZE_48     48           /* Small objects */
#define POOL_SIZE_112    112          /* Medium objects */

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

/* Global pools (one per size class) */
typedef struct SomaPools {
    SomaPool pool_40;           /* SUP nodes */
    SomaPool pool_48;           /* Small objects */
    SomaPool pool_112;          /* Medium objects */
} SomaPools;

/* Global pool instance */
extern SomaPools soma_pools;

/* Initialize memory pools (call once at startup) */
void soma_pool_init(void);

/* Clean up all pools (call at shutdown) */
void soma_pool_cleanup(void);

/* SUP pool */
void* soma_pool_alloc_sup(void);
void soma_pool_free_sup(void* ptr);

/* Closure pool (routes to appropriate size class) */
void* soma_pool_alloc_closure(uint16_t env_size);
void soma_pool_free_closure(void* ptr, uint16_t env_size);

/* String pool (routes to appropriate size class, falls back to malloc) */
void* soma_pool_alloc_string(size_t total_size);
void soma_pool_free_string(void* ptr, size_t total_size);

/* Tagged payload pool (routes to appropriate size class, falls back to malloc) */
void* soma_pool_alloc_tagged(size_t total_size);
void soma_pool_free_tagged(void* ptr, size_t total_size);

/*
 * Pool statistics — opt-in via -DSOMA_POOL_STATS.
 * When enabled, every alloc/free increments an atomic counter.
 * When disabled (default), zero overhead on hot paths.
 */
#ifdef SOMA_POOL_STATS
typedef struct SomaPoolStats {
    _Atomic size_t sup_allocs;
    _Atomic size_t sup_frees;
    _Atomic size_t small_allocs;
    _Atomic size_t small_frees;
    _Atomic size_t medium_allocs;
    _Atomic size_t medium_frees;
    _Atomic size_t large_allocs;
    _Atomic size_t large_frees;
    _Atomic size_t blocks_allocated;
    _Atomic size_t bytes_allocated;
} SomaPoolStats;

extern SomaPoolStats soma_pool_stats;

#define SOMA_STAT_INC(field) atomic_fetch_add(&soma_pool_stats.field, 1)
#define SOMA_STAT_ADD(field, n) atomic_fetch_add(&soma_pool_stats.field, (n))
#else
#define SOMA_STAT_INC(field) ((void)0)
#define SOMA_STAT_ADD(field, n) ((void)0)
#endif


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
