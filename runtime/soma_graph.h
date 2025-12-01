/*
 * Soma Graph Reduction Runtime
 * 
 * HVM-inspired graph reduction for massive parallelism.
 * This is an alternative execution model to fork-join, designed for
 * fine-grained parallelism where task overhead would dominate.
 *
 * Key Design:
 * - 16-byte nodes with 32-bit indices (cache-friendly)
 * - Wavefront parallel reduction (batch redexes, barrier sync)
 * - CALL nodes for known functions (CBV optimization)
 * - APP-LAM only for closures/higher-order
 *
 * Enable with SOMA_GRAPH=N environment variable (N = number of workers)
 */

#ifndef SOMA_GRAPH_H
#define SOMA_GRAPH_H

/* _GNU_SOURCE must be defined before any includes for futex support */
#ifdef __linux__
#define _GNU_SOURCE
#include <unistd.h>
#include <sys/syscall.h>
#include <linux/futex.h>
#endif

#include <stdint.h>
#include <stddef.h>
#include <stdatomic.h>
#include <pthread.h>

/*
 * Node Tags
 *
 * Values (leaf nodes):
 *   NUM  - 64-bit signed integer
 *   ERA  - Erased value (no data)
 *
 * Binary operations (reducible when both children are NUM):
 *   ADD, SUB, MUL, DIV, MOD
 *   EQ, NE, LT, LE, GT, GE  (comparisons, result is NUM 0 or 1)
 *
 * Function-related:
 *   CALL - Direct call to known function (up to 3 args)
 *   APP  - Application of unknown function
 *   LAM  - Lambda abstraction
 *   REF  - Function reference (index into function table)
 *   PAP  - Partial application (closure-like)
 *
 * Interaction net constructs:
 *   SUP  - Superposition (duplication result)
 *   DUP  - Duplication node
 *
 * ADT support:
 *   CON  - Constructor (tag + fields)
 *   MAT  - Pattern match node
 */

/* Value nodes */
#define GTAG_NUM    0x00
#define GTAG_ERA    0x01

/* Binary arithmetic */
#define GTAG_ADD    0x10
#define GTAG_SUB    0x11
#define GTAG_MUL    0x12
#define GTAG_DIV    0x13
#define GTAG_MOD    0x14

/* Binary comparison */
#define GTAG_EQ     0x18
#define GTAG_NE     0x19
#define GTAG_LT     0x1A
#define GTAG_LE     0x1B
#define GTAG_GT     0x1C
#define GTAG_GE     0x1D

/* Function nodes */
#define GTAG_CALL   0x20
#define GTAG_APP    0x21
#define GTAG_LAM    0x22
#define GTAG_REF    0x23
#define GTAG_PAP    0x24

/* Interaction net */
#define GTAG_SUP    0x30
#define GTAG_DUP    0x31

/* ADT */
#define GTAG_CON    0x40
#define GTAG_MAT    0x41

/* Indirection (for substitution links) */
#define GTAG_IND    0x50

/* Node status (for parallel reduction) */
#define GSTAT_FREE      0x00   /* Not allocated */
#define GSTAT_ACTIVE    0x01   /* Allocated, may be reducible */
#define GSTAT_REDUCING  0x02   /* Being reduced by a worker */
#define GSTAT_DONE      0x03   /* Reduced to a value (NUM, ERA) */
#define GSTAT_WAITING   0x04   /* Waiting for children to reduce */

/*
 * Node Representation (16 bytes)
 *
 * This fits 4 nodes per 64-byte cache line, enabling efficient
 * sequential and parallel access.
 *
 * Layout:
 *   [0]  u8   tag     - Node type (GTAG_*)
 *   [1]  u8   status  - Reduction status (GSTAT_*)
 *   [2]  u16  label   - DUP/SUP label for annihilation
 *   [4]  u32  aux     - Auxiliary data (arity, tag, etc.)
 *   [8]  union (8 bytes):
 *        - num: i64 value
 *        - pair: (l: u32, r: u32) for binary ops
 *        - lam: (var: u32, body: u32)
 *        - call: (fn: u16, arity: u16, args: see below)
 *        - ref: u32 function index
 *
 * For CALL nodes with >2 args, aux points to overflow storage.
 */

/* Special index values */
#define GIDX_NULL   0xFFFFFFFF   /* Null/invalid index */
#define GIDX_ERA    0xFFFFFFFE   /* Inline erasure (no node needed) */

/*
 * Parent Link Encoding (for direct pointer updates - HVM3 style)
 * 
 * Instead of using IND nodes, we directly update the parent's child pointer
 * when a node is reduced. To do this, we need to know:
 *   1. Parent node index
 *   2. Which slot in the parent points to us (left, right, body, etc.)
 *
 * We encode this in a single 32-bit value:
 *   - Bits 0-27:  Parent index (256M nodes max)
 *   - Bits 28-31: Slot type (0=left, 1=right, 2=body, 3=arg0, etc.)
 *
 * This allows atomic CAS on the parent's child pointer without IND chains.
 */
#define PLINK_INDEX_MASK   0x0FFFFFFF
#define PLINK_SLOT_SHIFT   28
#define PLINK_SLOT_MASK    0xF0000000

#define PLINK_SLOT_LEFT    0   /* pair.l, lam.var, etc. */
#define PLINK_SLOT_RIGHT   1   /* pair.r */
#define PLINK_SLOT_BODY    2   /* lam.body */
#define PLINK_SLOT_ARG0    3   /* First CALL arg (inline) */
#define PLINK_SLOT_ARGN    4   /* CALL args in pool (aux = arg index) */
#define PLINK_SLOT_TARGET  5   /* DUP target */

#define PLINK_MAKE(parent_idx, slot) \
    (((uint32_t)(slot) << PLINK_SLOT_SHIFT) | ((parent_idx) & PLINK_INDEX_MASK))

#define PLINK_GET_INDEX(plink) ((plink) & PLINK_INDEX_MASK)
#define PLINK_GET_SLOT(plink)  (((plink) & PLINK_SLOT_MASK) >> PLINK_SLOT_SHIFT)

/* 
 * Node structure - 16 bytes
 * 
 * We store the parent index in a separate array to keep nodes cache-friendly.
 * The main node data fits in 16 bytes (4 nodes per 64-byte cache line).
 *
 * IMPORTANT: The first 8 bytes (header) can be accessed atomically as a single
 * uint64_t for lock-free state transitions. This is the key to HVM-style
 * performance - single CAS to transition node state.
 */
typedef struct GNode {
    /* Header - 8 bytes, atomically accessible as uint64_t */
    union {
        struct {
            uint8_t  tag;       /* GTAG_* */
            uint8_t  status;    /* GSTAT_* */
            uint16_t label;     /* DUP/SUP label */
            uint32_t aux;       /* Type-specific: arity for CALL, tag for CON, etc. */
        };
        uint64_t header;        /* Atomic access to all header fields */
    };
    /* Payload - 8 bytes */
    union {
        int64_t num;    /* NUM: the integer value */
        struct {        /* ADD, SUB, MUL, APP, SUP, DUP, etc. */
            uint32_t l;
            uint32_t r;
        } pair;
        struct {        /* LAM: lambda */
            uint32_t var;   /* Variable slot (index in substitution) */
            uint32_t body;  /* Body expression */
        } lam;
        struct {        /* CALL: direct function call */
            uint16_t fn;    /* Function index */
            uint16_t arity; /* Number of arguments */
            uint32_t args;  /* Index to first arg (or inline if arity <= 1) */
        } call;
        struct {        /* CON: constructor */
            uint16_t tag;   /* Constructor tag */
            uint16_t arity; /* Number of fields */
            uint32_t fields;/* Index to first field */
        } con;
        uint32_t ref;   /* REF: function index */
    } data;
} GNode;

_Static_assert(sizeof(GNode) == 16, "GNode must be 16 bytes");

/* Helper macros for building/reading packed headers */
#define GNODE_MAKE_HEADER(tag, status, label, aux) \
    ((uint64_t)(tag) | ((uint64_t)(status) << 8) | ((uint64_t)(label) << 16) | ((uint64_t)(aux) << 32))

#define GNODE_GET_TAG(header)    ((uint8_t)((header) & 0xFF))
#define GNODE_GET_STATUS(header) ((uint8_t)(((header) >> 8) & 0xFF))
#define GNODE_GET_LABEL(header)  ((uint16_t)(((header) >> 16) & 0xFFFF))
#define GNODE_GET_AUX(header)    ((uint32_t)(((header) >> 32) & 0xFFFFFFFF))

/*
 * Function Table Entry
 *
 * Maps function indices to actual implementations.
 * Functions can either:
 *   1. Execute directly and return a value (for non-recursive base cases)
 *   2. Build graph nodes and return the root (for recursive cases)
 */
typedef struct GFunc {
    const char* name;           /* Function name (for debugging) */
    uint8_t arity;              /* Number of parameters */
    uint8_t flags;              /* GFUNC_* flags */
    uint16_t _pad;
    void* impl;                 /* Function pointer */
} GFunc;

/* Function flags */
#define GFUNC_DIRECT    0x01   /* Returns value directly (no graph building) */
#define GFUNC_RECURSIVE 0x02   /* May call itself (needs graph for parallelism) */
#define GFUNC_PURE      0x04   /* No side effects (can be memoized) */

/*
 * Graph Runtime
 *
 * Single instance managing node pool and reduction state.
 */

#ifndef GRAPH_NODE_POOL_SIZE
#define GRAPH_NODE_POOL_SIZE (1 << 26)   /* 64M nodes = 1GB */
#endif

#ifndef GRAPH_REDEX_BUF_SIZE
#define GRAPH_REDEX_BUF_SIZE (1 << 22)   /* 4M redexes per buffer */
#endif

#ifndef GRAPH_MAX_WORKERS
#define GRAPH_MAX_WORKERS 64
#endif

#ifndef GRAPH_ARG_POOL_SIZE
#define GRAPH_ARG_POOL_SIZE (1 << 20)    /* 1M u32 slots for CALL args overflow */
#endif

/* Cache line size for padding (avoid false sharing) */
#define CACHE_LINE_SIZE 64

/* Per-worker deque for work-stealing */
#define WORKER_DEQUE_SIZE (1 << 16)  /* 64K entries per worker */
#define WORKER_LOCAL_BUF_SIZE (1 << 16)  /* 64K local buffer per worker */

/* Worker state for parallel reduction */
typedef struct GWorker {
    pthread_t thread;
    int id;
    atomic_int active;
    
    /* Per-worker deque (chase-lev work-stealing deque) */
    uint32_t* deque;
    atomic_uint_fast32_t deque_bottom;  /* Only owner pushes/pops here */
    atomic_uint_fast32_t deque_top;     /* Thieves steal from here */
    
    /* Per-worker local output buffer (no atomics needed!) */
    uint32_t* local_buf;
    uint32_t local_count;
    
    /* Per-worker statistics */
    uint64_t reductions;
    uint64_t steals;  /* Times we stole from another worker */
    
    /* Padding to avoid false sharing between workers */
    char _pad[CACHE_LINE_SIZE - ((sizeof(pthread_t) + sizeof(int) + sizeof(atomic_int) + 
               sizeof(uint32_t*) * 2 + sizeof(atomic_uint_fast32_t) * 2 +
               sizeof(uint32_t) + sizeof(uint64_t) * 2) % CACHE_LINE_SIZE)];
} GWorker;

/* Simple barrier using futex for efficient waiting */
typedef struct GBarrier {
    atomic_int count;
    atomic_int generation;
    int num_threads;
} GBarrier;

/* Futex operations (Linux) */
#ifdef __linux__
#include <linux/futex.h>
#include <sys/syscall.h>
#include <unistd.h>
#include <limits.h>

static inline void futex_wait(atomic_int* addr, int expected) {
    syscall(SYS_futex, addr, FUTEX_WAIT_PRIVATE, expected, NULL, NULL, 0);
}

static inline void futex_wake(atomic_int* addr, int count) {
    syscall(SYS_futex, addr, FUTEX_WAKE_PRIVATE, count, NULL, NULL, 0);
}

static inline void futex_wake_all(atomic_int* addr) {
    futex_wake(addr, INT_MAX);
}
#else
/* Fallback for non-Linux: spin with yield */
static inline void futex_wait(atomic_int* addr, int expected) {
    while (atomic_load(addr) == expected) {
        sched_yield();
    }
}
static inline void futex_wake(atomic_int* addr, int count) {
    (void)addr; (void)count;
}
static inline void futex_wake_all(atomic_int* addr) {
    (void)addr;
}
#endif

/* Graph runtime state */
typedef struct GraphRuntime {
    /* Node pool */
    GNode* nodes;
    uint32_t* parents;  /* Separate parent array for worklist optimization */
    atomic_uint_fast32_t next_alloc;
    uint32_t pool_size;
    
    /* Free list for node recycling (lock-free stack) */
    _Atomic uint32_t free_list_head;  /* Index of first free node, GIDX_NULL if empty */
    atomic_uint_fast64_t nodes_recycled;  /* Statistics: times a node was recycled */
    atomic_uint_fast64_t nodes_reused;    /* Statistics: times a node was taken from free list */
    
    /* Argument overflow pool (for CALL nodes with >2 args) */
    uint32_t* arg_pool;
    atomic_uint_fast32_t next_arg;
    uint32_t arg_pool_size;
    
    /* Function table */
    GFunc* functions;
    uint32_t num_functions;
    uint32_t functions_capacity;
    
    /* Double-buffered redex lists for wavefront reduction */
    uint32_t* redex_buf[2];
    
    /* Padded to avoid false sharing between redex_count entries */
    struct {
        atomic_uint_fast32_t count;
        char _pad[CACHE_LINE_SIZE - sizeof(atomic_uint_fast32_t)];
    } redex_count_padded[2];
    
    int current_buf;
    
    /* Worklist for optimized reduction (lock-free MPMC queue) */
    uint32_t* worklist;
    uint32_t worklist_capacity;
    atomic_uint_fast32_t worklist_head;  /* Next index to read */
    atomic_uint_fast32_t worklist_tail;  /* Next index to write */
    
    /* Worker threads */
    GWorker workers[GRAPH_MAX_WORKERS];
    int num_workers;
    atomic_int shutdown;
    atomic_int workers_done;  /* Count of workers that have finished */
    
    /* Root node for parallel reduction */
    uint32_t parallel_root;
    
    /* Synchronization */
    GBarrier barrier;
    
    /* Padded to avoid false sharing - heavily contended in parallel */
    struct {
        atomic_uint_fast32_t value;
        char _pad[CACHE_LINE_SIZE - sizeof(atomic_uint_fast32_t)];
    } next_redex_padded;
    
    /* Statistics */
    atomic_uint_fast64_t total_reductions;
    atomic_uint_fast64_t total_nodes;
    atomic_uint_fast64_t wavefront_iterations;
} GraphRuntime;

/* Global runtime instance */
extern GraphRuntime* g_graph_rt;

/*
 * Lifecycle API
 */

/* Initialize graph runtime (num_workers=0 for single-threaded) */
GraphRuntime* soma_graph_init(int num_workers);

/* Shutdown and free all resources */
void soma_graph_shutdown(GraphRuntime* rt);

/*
 * Node Allocation API
 *
 * All allocation functions return a 32-bit index.
 * GIDX_NULL indicates allocation failure.
 */

/* Allocate a raw node (caller sets fields) */
uint32_t soma_graph_alloc(GraphRuntime* rt);

/* Free a node (add to free list for recycling) */
void soma_graph_free(GraphRuntime* rt, uint32_t idx);

/* Allocate and initialize a NUM node */
uint32_t soma_graph_num(GraphRuntime* rt, int64_t value);

/* Allocate and initialize an ERA node */
uint32_t soma_graph_era(GraphRuntime* rt);

/* Binary operation nodes */
uint32_t soma_graph_add(GraphRuntime* rt, uint32_t left, uint32_t right);
uint32_t soma_graph_sub(GraphRuntime* rt, uint32_t left, uint32_t right);
uint32_t soma_graph_mul(GraphRuntime* rt, uint32_t left, uint32_t right);
uint32_t soma_graph_div(GraphRuntime* rt, uint32_t left, uint32_t right);
uint32_t soma_graph_mod(GraphRuntime* rt, uint32_t left, uint32_t right);

/* Comparison nodes */
uint32_t soma_graph_eq(GraphRuntime* rt, uint32_t left, uint32_t right);
uint32_t soma_graph_ne(GraphRuntime* rt, uint32_t left, uint32_t right);
uint32_t soma_graph_lt(GraphRuntime* rt, uint32_t left, uint32_t right);
uint32_t soma_graph_le(GraphRuntime* rt, uint32_t left, uint32_t right);
uint32_t soma_graph_gt(GraphRuntime* rt, uint32_t left, uint32_t right);
uint32_t soma_graph_ge(GraphRuntime* rt, uint32_t left, uint32_t right);

/* Function-related nodes */
uint32_t soma_graph_call(GraphRuntime* rt, uint16_t fn_idx, uint32_t* args, int arity);
uint32_t soma_graph_call1(GraphRuntime* rt, uint16_t fn_idx, uint32_t arg0);
uint32_t soma_graph_call2(GraphRuntime* rt, uint16_t fn_idx, uint32_t arg0, uint32_t arg1);
uint32_t soma_graph_ref(GraphRuntime* rt, uint16_t fn_idx);
uint32_t soma_graph_app(GraphRuntime* rt, uint32_t fn, uint32_t arg);
uint32_t soma_graph_lam(GraphRuntime* rt, uint32_t var_slot, uint32_t body);

/* Interaction net nodes */
uint32_t soma_graph_sup(GraphRuntime* rt, uint16_t label, uint32_t left, uint32_t right);
uint32_t soma_graph_dup(GraphRuntime* rt, uint16_t label, uint32_t target);

/* ADT nodes */
uint32_t soma_graph_con(GraphRuntime* rt, uint16_t tag, uint32_t* fields, int arity);

/*
 * Function Table API
 */

/* Register a function, returns its index */
uint16_t soma_graph_register_func(GraphRuntime* rt, const char* name, 
                                   uint8_t arity, uint8_t flags, void* impl);

/* Get function entry by index */
GFunc* soma_graph_get_func(GraphRuntime* rt, uint16_t idx);

/*
 * Reduction API
 */

/* Follow indirection chain to get the real node index.
 * NOTE: With direct pointer updates, IND nodes should be rare. 
 * They only exist temporarily during reduction. */
static inline uint32_t soma_graph_deref(GraphRuntime* rt, uint32_t idx) {
    while (idx != GIDX_NULL && idx != GIDX_ERA && idx < rt->next_alloc) {
        uint8_t tag = atomic_load((_Atomic uint8_t*)&rt->nodes[idx].tag);
        if (tag != GTAG_IND) break;
        /* Read IND target atomically */
        idx = atomic_load((_Atomic uint32_t*)&rt->nodes[idx].data.pair.l);
    }
    return idx;
}

/*
 * Direct Pointer Update (HVM3-style, no indirection chains)
 * 
 * When a node is reduced to a result, we directly update the parent's
 * child pointer to point to the result, bypassing indirection nodes.
 * 
 * This is the key optimization: instead of creating IND chains that must
 * be traversed on every access, we update pointers in-place.
 *
 * Returns: pointer to the child slot in parent (for atomic CAS if needed)
 */
static inline _Atomic uint32_t* soma_graph_get_child_slot(GraphRuntime* rt, uint32_t plink) {
    uint32_t parent_idx = PLINK_GET_INDEX(plink);
    uint32_t slot = PLINK_GET_SLOT(plink);
    
    if (parent_idx == GIDX_NULL || parent_idx >= rt->next_alloc) {
        return NULL;
    }
    
    GNode* parent = &rt->nodes[parent_idx];
    
    switch (slot) {
        case PLINK_SLOT_LEFT:
            return (_Atomic uint32_t*)&parent->data.pair.l;
        case PLINK_SLOT_RIGHT:
            return (_Atomic uint32_t*)&parent->data.pair.r;
        case PLINK_SLOT_BODY:
            return (_Atomic uint32_t*)&parent->data.lam.body;
        case PLINK_SLOT_ARG0:
            /* Inline arg for CALL with arity=1 */
            return (_Atomic uint32_t*)&parent->data.call.args;
        case PLINK_SLOT_TARGET:
            /* DUP target is in pair.l */
            return (_Atomic uint32_t*)&parent->data.pair.l;
        default:
            return NULL;
    }
}

/* Update parent's child pointer to point to new_child.
 * Uses atomic store for thread safety. 
 * Also updates new_child's parent link to point to the same parent slot. */
static inline void soma_graph_update_parent(GraphRuntime* rt, uint32_t plink, uint32_t new_child) {
    _Atomic uint32_t* slot = soma_graph_get_child_slot(rt, plink);
    if (slot != NULL) {
        atomic_store_explicit(slot, new_child, memory_order_release);
        
        /* Update new child's parent link */
        if (new_child != GIDX_NULL && new_child != GIDX_ERA && new_child < rt->next_alloc) {
            atomic_store_explicit((_Atomic uint32_t*)&rt->parents[new_child], plink, memory_order_relaxed);
        }
    }
}

/* Check if a node is a value (NUM or ERA), following indirections */
static inline int soma_graph_is_value(GraphRuntime* rt, uint32_t idx) {
    if (idx == GIDX_NULL || idx == GIDX_ERA) return 1;
    idx = soma_graph_deref(rt, idx);
    if (idx == GIDX_NULL || idx == GIDX_ERA) return 1;
    if (idx >= rt->next_alloc) return 0;
    uint8_t tag = rt->nodes[idx].tag;
    return tag == GTAG_NUM || tag == GTAG_ERA;
}

/* Get the integer value from a NUM node (undefined if not NUM) */
static inline int64_t soma_graph_get_num(GraphRuntime* rt, uint32_t idx) {
    return rt->nodes[idx].data.num;
}

/* Reduce a single node (single-threaded) 
 * Returns: 1 if reduction occurred, 0 if already a value or blocked */
int soma_graph_reduce_node(GraphRuntime* rt, uint32_t idx);

/* Reduce until root is a value (single-threaded, tree traversal - legacy)
 * Returns: the final integer value */
int64_t soma_graph_reduce(GraphRuntime* rt, uint32_t root);

/* Reduce until root is a value (single-threaded, worklist-based - fast)
 * Returns: the final integer value */
int64_t soma_graph_reduce_fast(GraphRuntime* rt, uint32_t root);

/* Reduce with parallel wavefront (multi-threaded)
 * Returns: the final integer value */
int64_t soma_graph_reduce_parallel(GraphRuntime* rt, uint32_t root);
int64_t soma_graph_reduce_taskpar(GraphRuntime* rt, uint32_t root);

/* Fork-join parallel reduction (separate runtimes per subtask)
 * This approach spawns independent runtimes for top-level parallelizable nodes,
 * avoiding contention on shared data structures. Best for coarse-grained parallelism.
 * Returns: the final integer value */
int64_t soma_graph_reduce_forkjoin(GraphRuntime* rt, uint32_t root);

/*
 * Debugging / Statistics
 */

/* Print a node (for debugging) */
void soma_graph_print_node(GraphRuntime* rt, uint32_t idx);

/* Print reduction statistics */
void soma_graph_print_stats(GraphRuntime* rt);

/* Dump the graph to stderr (for debugging small graphs) */
void soma_graph_dump(GraphRuntime* rt, uint32_t root, int max_depth);

#endif /* SOMA_GRAPH_H */
