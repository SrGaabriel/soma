/*
 * Soma HVM-Style Graph Reduction Runtime
 * 
 * Based on HVM2's parallel reduction architecture:
 * - Partitioned heap: each thread owns a slice of memory
 * - Per-thread redex bags: local work queues, no contention
 * - Work stealing: idle threads steal from others
 * - Relaxed atomics: minimal synchronization overhead
 *
 * Key difference from original soma_graph.c:
 * - No atomic allocation counter (major bottleneck)
 * - No parent pointer arrays (substitution via "sub" bit)
 * - No barriers during reduction
 */

#ifndef SOMA_HVM_H
#define SOMA_HVM_H

#include <stdint.h>
#include <stdatomic.h>
#include <pthread.h>
#include <stdbool.h>

/*
 * Term encoding (64-bit):
 *   [ 63 ............... 32 ][ 31 .. 8 ][ 7 ][ 6 .. 0 ]
 *        location (32b)         aux(24b)  S     tag(7b)
 *
 *   - tag: 7-bit node type
 *   - S: substitution bit (1 = value has been substituted here)
 *   - aux: auxiliary data (label, arity, operator type)
 *   - loc: heap location (32-bit, supports 4B nodes)
 */
typedef uint64_t Term;
typedef uint32_t Loc;
typedef uint8_t  Tag;
typedef uint32_t Lab;

/* Atomic types */
typedef _Atomic(uint64_t) ATerm;
typedef _Atomic(uint32_t) ALoc;
typedef _Atomic(uint8_t)  ATag;

/* Term encoding */
#define TERM_TAG_MASK   0x7FULL
#define TERM_SUB_BIT    (1ULL << 7)
#define TERM_AUX_SHIFT  8
#define TERM_AUX_MASK   0xFFFFFFULL
#define TERM_LOC_SHIFT  32

static inline Term term_new(Tag tag, Lab aux, Loc loc) {
    return ((Term)tag) | ((Term)aux << TERM_AUX_SHIFT) | ((Term)loc << TERM_LOC_SHIFT);
}

static inline Tag term_tag(Term t) { return (Tag)(t & TERM_TAG_MASK); }
static inline Lab term_aux(Term t) { return (Lab)((t >> TERM_AUX_SHIFT) & TERM_AUX_MASK); }
static inline Loc term_loc(Term t) { return (Loc)(t >> TERM_LOC_SHIFT); }
static inline bool term_is_sub(Term t) { return (t & TERM_SUB_BIT) != 0; }
static inline Term term_set_sub(Term t) { return t | TERM_SUB_BIT; }
static inline Term term_rem_sub(Term t) { return t & ~TERM_SUB_BIT; }

/* Node tags */
#define TAG_VAR  0x00  /* Variable (substitution target) */
#define TAG_REF  0x01  /* Function reference */
#define TAG_ERA  0x02  /* Eraser */
#define TAG_NUM  0x03  /* Number (32-bit in aux+loc) */
#define TAG_CON  0x04  /* Constructor / pair */
#define TAG_DUP  0x05  /* Duplicator */
#define TAG_OPX  0x06  /* Binary op, waiting for first arg */
#define TAG_OPY  0x07  /* Binary op, waiting for second arg */
#define TAG_APP  0x08  /* Application */
#define TAG_LAM  0x09  /* Lambda */

/* Operators (stored in aux for OPX/OPY) */
#define OP_ADD 0x00
#define OP_SUB 0x01
#define OP_MUL 0x02
#define OP_DIV 0x03
#define OP_MOD 0x04
#define OP_EQ  0x05
#define OP_NE  0x06
#define OP_LT  0x07
#define OP_GT  0x08
#define OP_LE  0x09
#define OP_GE  0x0A

/* Special values */
#define TERM_NULL  0ULL
#define TERM_FREE  0ULL  /* Free slot marker */

/* Configuration */
#ifndef HVM_THREADS_L2
#define HVM_THREADS_L2 2  /* Log2 of thread count: 2 = 4 threads */
#endif
#define HVM_THREADS (1 << HVM_THREADS_L2)

#define HVM_HEAP_SIZE   (1ULL << 28)  /* 256M terms per thread = 2GB each */
#define HVM_RBAG_SIZE   (1ULL << 20)  /* 1M redexes per thread */
#define HVM_STACK_SIZE  (1ULL << 16)  /* 64K stack entries */

/*
 * Redex: a pair of terms to interact
 */
typedef struct {
    Term a;
    Term b;
} Redex;

typedef _Atomic(Redex) ARedex;

/*
 * Thread-local memory
 */
typedef struct ThreadMem {
    uint32_t tid;           /* Thread ID */
    uint32_t nput;          /* Next node allocation index (within partition) */
    uint64_t itrs;          /* Interaction count */
    
    /* Local redex bag */
    uint32_t rbag_lo;       /* Low priority redex count */
    uint32_t rbag_hi;       /* High priority redex count */
    Redex*   rbag;          /* Redex buffer (low priority) */
    Redex*   hbag;          /* High priority redex buffer */
    
    /* Reduction stack */
    Term*    stack;
    uint32_t spos;
    
    /* Steal state */
    uint32_t sidx;          /* Current steal index */
    
    /* Debug stats */
    uint64_t steals;        /* Successful steals */
    uint64_t steal_attempts;/* Steal attempts */
    uint64_t pushes;        /* Total redex pushes */
    uint64_t max_rbag;      /* Max redex bag size seen */
} ThreadMem;

/*
 * Forward declarations
 */
typedef struct HvmNet HvmNet;

/*
 * Function definition
 */
typedef Term (*HvmFunc)(HvmNet* net, ThreadMem* tm, Term ref);

typedef struct {
    char     name[64];
    uint16_t arity;
    HvmFunc  func;
} FuncDef;

/*
 * Global network state
 */
struct HvmNet {
    /* Partitioned heap: heap[tid * HVM_HEAP_SIZE ... (tid+1) * HVM_HEAP_SIZE) */
    ATerm*   heap;          /* Global heap (partitioned by thread) */
    
    /* Per-thread redex bags (for stealing) */
    ARedex*  rbag_buf;      /* Global redex buffer (partitioned by thread) */
    _Atomic(uint32_t)* rbag_cnt;  /* Per-thread redex counts */
    
    /* Synchronization */
    _Atomic(uint64_t) itrs; /* Total interaction count */
    _Atomic(uint32_t) idle; /* Idle thread counter */
    _Atomic(int)      done; /* Termination flag */
    
    /* Function table */
    FuncDef  funcs[256];
    uint32_t num_funcs;
    
    /* Thread state */
    ThreadMem* tms[HVM_THREADS];
    pthread_t  threads[HVM_THREADS];
    
    /* Root variable location */
    Loc root_var;
};

/*
 * API
 */

/* Initialize/shutdown */
HvmNet* hvm_init(int num_threads);
void    hvm_free(HvmNet* net);

/* Register function */
void hvm_register_func(HvmNet* net, const char* name, uint16_t arity, HvmFunc func);

/* Node construction (thread-local, no atomics!) */
Loc  hvm_alloc(HvmNet* net, ThreadMem* tm);
void hvm_set(HvmNet* net, Loc loc, Term val);
Term hvm_get(HvmNet* net, Loc loc);

/* Create terms */
static inline Term hvm_num(int64_t n) {
    /* Store number in aux (low 24 bits) + loc (32 bits) = 56 bits */
    uint64_t u = (uint64_t)(n & 0x00FFFFFFFFFFFFFFULL);
    return term_new(TAG_NUM, (Lab)(u & 0xFFFFFF), (Loc)(u >> 24));
}

static inline int64_t hvm_get_num(Term t) {
    uint64_t u = ((uint64_t)term_aux(t)) | ((uint64_t)term_loc(t) << 24);
    /* Sign extend from 56 bits */
    if (u & (1ULL << 55)) u |= 0xFF00000000000000ULL;
    return (int64_t)u;
}

Term hvm_con(HvmNet* net, ThreadMem* tm, Term a, Term b);
Term hvm_opx(HvmNet* net, ThreadMem* tm, Lab op, Term a, Term b);
Term hvm_app(HvmNet* net, ThreadMem* tm, Term fun, Term arg);
Term hvm_lam(HvmNet* net, ThreadMem* tm, Term body);
Term hvm_ref(uint16_t func_idx, Term arg);

/* Redex management */
void hvm_push_redex(HvmNet* net, ThreadMem* tm, Term a, Term b);
bool hvm_pop_redex(HvmNet* net, ThreadMem* tm, Redex* out);
bool hvm_steal_redex(HvmNet* net, ThreadMem* tm, Redex* out, int num_threads);

/* Reduction */
void    hvm_link(HvmNet* net, ThreadMem* tm, Term a, Term b);
int64_t hvm_reduce(HvmNet* net, Term root);

/* Debug */
void hvm_print_term(HvmNet* net, Term t);
void hvm_print_stats(HvmNet* net);

#endif /* SOMA_HVM_H */
