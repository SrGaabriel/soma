/*
 * Soma Runtime
 *
 * === Headerless Heap Objects ===
 *
 * After monomorphization, the compiler knows every type at every point.
 * Heap objects carry NO runtime headers — no tag byte, no magic sentinel,
 * no count field. Object identity and layout are determined entirely at
 * compile time via type-specialized erase/clone functions.
 *
 * Tagged Payload (count*8 bytes):
 *   [0]  i64  field[0]
 *   [8]  i64  field[1]  ...
 *   Pure data — the compiler-generated eraser knows field count/types.
 *
 * Closure (16 + env_size*8 bytes):
 *   [0]  u8   arity     (needed by soma_apply for PAP detection)
 *   [1]  u8   _pad[1]   (env_size low byte — used by soma_apply internally)
 *   [2]  u8   _pad[2]   (env_size high byte)
 *   [3-7] u8  _pad[3-7] (alignment)
 *   [8]  ptr  func_ptr  (function pointer)
 *   [16] i64  env[0]    ...
 *
 * String (8 + length + 1 bytes):
 *   [0]  i64  length    (byte count, excluding null terminator)
 *   [8]  char data[]    (inline, null-terminated)
 *
 * SUP (48 bytes, pool-allocated — keeps header for state machine):
 *   [0]  u8   tag        (SUP_TAG_*)
 *   [1]  u8[3] _pad      ('S','U','P')
 *   [4]  u32  label
 *   [8]  ptr  value
 *   [16] ptr  proj0
 *   [24] ptr  proj1
 *   [32] ptr  type_desc
 *
 * Flat Array View (32 bytes — keeps header for tag dispatch):
 *   [0]  u8   tag         (NODE_FLAT_ARRAY_VIEW = 5)
 *   [1]  u8[3] _pad
 *   [4]  u32  _reserved
 *   [8]  i64  length
 *   [16] ptr  data
 *   [24] ptr  backing
 */

#ifndef SOMA_RUNTIME_H
#define SOMA_RUNTIME_H

#include <stdint.h>
#include <stddef.h>
#include <stdatomic.h>

/* Node tag constants */
#define NODE_CLOSURE          1   /* stored in closure _pad[0] for runtime identification */
#define NODE_FLAT_ARRAY       4
#define NODE_FLAT_ARRAY_VIEW  5

/* SUP padding bytes for identification */
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
 * Low 3 bits of pointers for type tags (assuming 8-byte alignment).
 *
 * Pointer format (64-bit):
 *   [63:3] payload  [2:0] tag
 *
 * Tag values:
 *   000 = Heap pointer (closure, etc.) - must be 8-byte aligned
 *   001 = Small integer (63-bit signed, shifted right by 3)
 *   010 = Boolean/Unit (payload: 0=false, 1=true, 2=unit)
 *   011 = Character (payload: Unicode codepoint)
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

/*
 * Closure structure (env follows at offset 16)
 *
 * _pad[0] = NODE_CLOSURE sentinel for runtime identification by soma_era_free.
 * _pad[1..2] = env_size as little-endian u16 (needed by soma_apply for PAP
 *   creation and by soma_era_closure for dynamic env traversal).
 */
typedef struct SomaClosure {
    uint8_t  arity;       /* remaining args (needed by soma_apply) */
    uint8_t  _pad[7];     /* [0]=NODE_CLOSURE, [1..2]=env_size LE16, [3..6]=reserved */
    void*    func_ptr;    /* function pointer */
    /* SomaValue env[] follows at offset 16 */
} SomaClosure;

/*
 * Type-specialized function pointers for clone and erase.
 *
 * The compiler generates one clone and one erase function per concrete type.
 * A SomaTypeDesc bundles both into a single struct so SUP nodes only need
 * one pointer (8 bytes) instead of two (16 bytes). The TypeDesc structs are
 * emitted as static LLVM globals — no runtime allocation.
 */
typedef SomaValue (*SomaCloneFn)(SomaValue value, uint32_t label);
typedef void      (*SomaEraseFn)(SomaValue value);

typedef struct SomaTypeDesc {
    SomaCloneFn  clone_fn;
    SomaEraseFn  erase_fn;
} SomaTypeDesc;

/*
 * SUP (Superposition) node structure (48 bytes, pool-allocated)
 */
typedef struct SomaSup {
    uint8_t       tag;
    uint8_t       _pad[3];
    uint32_t      label;
    void*         value;
    void*         proj0;
    void*         proj1;
    SomaTypeDesc* type_desc;
} SomaSup;

/*
 * String structure (length + inline data, no header overhead)
 *
 * The MSB of `length` is a static sentinel: static string globals
 * emitted by the compiler have bit 63 set, preventing soma_era_string
 * from freeing read-only memory.  All length readers use
 * soma_string_len() which masks the sentinel bit.
 */
#define SOMA_STRING_STATIC_BIT ((int64_t)1 << 63)

typedef struct SomaString {
    int64_t  length;    /* byte count; bit 63 = static sentinel */
    char     data[];    /* flexible array member: string data inline */
} SomaString;

static inline int64_t soma_string_len(const SomaString* s) {
    return s->length & ~SOMA_STRING_STATIC_BIT;
}

/*
 * Flat array backing storage (compiler-generated, not user-facing)
 */
typedef struct SomaFlatArray {
    uint8_t   tag;         /* NODE_FLAT_ARRAY */
    uint8_t   elem_size;   /* bytes per element */
    uint8_t   _pad[2];
    uint32_t  _reserved;
    int64_t   length;
    /* element data follows at offset 16 */
} SomaFlatArray;

/*
 * Flat array view (user-facing list representation)
 */
typedef struct SomaFlatArrayView {
    uint8_t   tag;         /* NODE_FLAT_ARRAY_VIEW */
    uint8_t   _pad[3];
    uint32_t  _reserved;
    int64_t   length;
    void*     data;        /* pointer to first visible element */
    void*     backing;     /* owned backing SomaFlatArray (or NULL) */
} SomaFlatArrayView;


/*
 * Core runtime functions
 */

/* Free a heap-allocated SUP/view/array by tag dispatch */
void soma_era_free(void* value);

/* Panic: print error message and abort */
void soma_panic(const char* msg);

/*
 * String operations
 */

/* Convert Soma String to C string (returns data pointer) */
char* soma_to_cstring(SomaString* str);

/* Convert C string to Soma String (allocates new String) */
SomaString* soma_from_cstring(const char* cstr);

/* Get C string length */
uint64_t soma_cstring_len(const char* cstr);

/* Concatenate two Soma Strings */
SomaString* soma_strcat(SomaString* a, SomaString* b);

/* Convert int32 to Soma String */
SomaString* soma_int_to_string(int32_t val);

/* Free a string (length + data) */
void soma_era_string(void* value);

/*
 * Flat array view operations
 */

/* Clone a flat array view (deep-copies the backing array) */
void* soma_clone_flat_array_view(SomaFlatArrayView* src);

/*
 * Closure operations
 */

/* Allocate a closure with space for env_size captured values */
void* soma_alloc_closure(void* func_ptr, uint8_t arity, uint16_t env_size);

/* Apply one argument to a closure via eval/apply (Marlow & Peyton Jones 2004) */
void* soma_apply(void* closure, void* arg);

/* Set a closure environment slot */
void soma_closure_set_env(void* closure, uint16_t index, SomaValue value);

/* Get a closure environment slot */
SomaValue soma_closure_get_env(void* closure, uint16_t index);

/* Get function pointer from closure */
void* soma_closure_get_func(void* closure);

/* Erase a closure: traverse and erase all env slots, then free */
void soma_era_closure(void* closure);

/* Clone a closure under a statically assigned DUP label */
void* soma_clone_closure(void* closure, uint32_t label);

/* Generic heap value clone — handles SUPs, views, arrays, and closures */
SomaValue soma_clone_heap_value_for_dup(SomaValue value, uint32_t label);

/*
 * SUP (Superposition) operations — Tier 3 lazy duplication
 */

/* Create a SUP node with a type descriptor for specialized clone/erase */
SomaValue soma_dup_typed(uint32_t label, SomaValue value,
                         SomaTypeDesc* type_desc);

/* Extract first projection from a SUP */
SomaValue soma_proj0(SomaValue sup_val);

/* Extract second projection from a SUP */
SomaValue soma_proj1(SomaValue sup_val);

/*
 * Memory Pool API
 *
 * Two size-class pools cover all fixed-size heap objects:
 *   pool_48  — small objects ≤48 bytes (SUPs, small closures, small strings)
 *   pool_112 — medium objects ≤112 bytes
 * Larger objects fall through to malloc.
 */

#define POOL_BLOCK_SIZE  (64 * 1024)  /* 64KB per block */
#define POOL_SIZE_48     48           /* Small objects + SUP nodes */
#define POOL_SIZE_112    112          /* Medium objects */

/* Memory pool structure */
typedef struct SomaPoolBlock {
    struct SomaPoolBlock* next;
    size_t used;
    char data[];
} SomaPoolBlock;

typedef struct SomaPool {
    SomaPoolBlock* blocks;
    size_t item_size;
    void* free_list;
} SomaPool;

typedef struct SomaPools {
    SomaPool pool_48;
    SomaPool pool_112;
} SomaPools;

extern SomaPools soma_pools;

void soma_pool_init(void);
void soma_pool_cleanup(void);

/* SUP pool */
void* soma_pool_alloc_sup(void);
void soma_pool_free_sup(void* ptr);

/* Generic size-class pool allocation */
void* soma_pool_alloc_raw(size_t byte_size);
void  soma_pool_free_raw(void* ptr, size_t byte_size);

/* Flat array view pool (32 bytes → pool_48) */
void* soma_alloc_view(void);
void soma_free_view(void* ptr);

/*
 * Pool statistics — opt-in via -DSOMA_POOL_STATS.
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

void soma_par_init(int num_workers);
void soma_par_shutdown(void);

static inline int soma_par_enabled(void) {
    return soma_par.num_workers > 0;
}

SomaTask* soma_task_alloc(void);
void soma_task_free(SomaTask* task);
void soma_par_spawn(SomaTask* task);
SomaTask* soma_par_pop(SomaWorker* worker);
SomaTask* soma_par_steal(SomaWorker* thief, SomaWorker* victim);
SomaValue soma_par_run_task(SomaTask* task);

SomaTask* soma_fork(SomaTaskFn fn, void* env);
SomaTask* soma_fork_direct(SomaDirectFn fn, SomaValue arg);
SomaTask* soma_fork_closure(SomaClosureFn fn, void* closure, SomaValue arg);
SomaTask* soma_fork_multi(void* fn, SomaValue* args, int num_args);
SomaValue soma_join(SomaTask* task);

typedef struct {
    _Atomic uint64_t tasks_spawned;
    _Atomic uint64_t tasks_run;
    _Atomic uint64_t tasks_run_inline;
    _Atomic uint64_t tasks_stolen;
} SomaParStats;

extern SomaParStats soma_par_stats;

void soma_par_print_stats(void);

extern __thread SomaWorker* soma_current_worker;

static inline SomaWorker* soma_par_current_worker(void) {
    return soma_current_worker;
}

#endif /* SOMA_RUNTIME_H */
