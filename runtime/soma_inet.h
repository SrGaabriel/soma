/*
 * Soma Interaction Net Runtime - Maximum Parallelism
 * 
 * Pure redex-driven reduction based on HVM2/HVM3 architecture.
 * 
 * KEY INSIGHT: Never eagerly reduce. Every interaction either:
 *   1. Produces a value (substitution)
 *   2. Produces new redexes (more work to steal)
 * 
 * This spreads work across all available threads continuously,
 * rather than having one thread do all the work in reduce_whnf().
 *
 * ARCHITECTURE:
 * - Terms are 64-bit: [loc:32][aux:16][sub:1][tag:7]
 * - Heap is partitioned by thread (no atomic allocation)
 * - Each thread has a local redex deque (Chase-Lev style)
 * - Work stealing from other threads' deques
 * - Substitution via atomic exchange (no IND nodes)
 */

#ifndef SOMA_INET_H
#define SOMA_INET_H

#include <stdint.h>
#include <stdbool.h>
#include <stdatomic.h>
#include <pthread.h>

/*============================================================================
 * Term Encoding (64-bit)
 *
 *   [ 63 ............ 32 ][ 31 ...... 16 ][ 15 ][ 14 .. 8 ][ 7 .. 0 ]
 *        location (32b)       aux (16b)     SUB    reserved   tag (8b)
 *
 *   - tag: 8-bit node type
 *   - SUB: substitution bit (value has been written here)
 *   - aux: operator type, function index, label, etc.
 *   - loc: heap location (32-bit, 4B nodes max)
 *
 * For NUM nodes, we pack the 48-bit value into aux+loc.
 *===========================================================================*/

typedef uint64_t Term;
typedef uint32_t Loc;
typedef uint16_t Lab;
typedef uint8_t  Tag;

/* Atomic types */
typedef _Atomic(uint64_t) ATerm;
typedef _Atomic(uint32_t) ALoc;

/* Term encoding constants */
#define TERM_TAG_BITS    8
#define TERM_TAG_MASK    0xFFULL
#define TERM_SUB_BIT     (1ULL << 15)
#define TERM_AUX_SHIFT   16
#define TERM_AUX_MASK    0xFFFFULL
#define TERM_LOC_SHIFT   32

/* Term constructors/accessors */
static inline Term term_new(Tag tag, Lab aux, Loc loc) {
    return ((Term)tag) | ((Term)aux << TERM_AUX_SHIFT) | ((Term)loc << TERM_LOC_SHIFT);
}

static inline Tag  term_tag(Term t) { return (Tag)(t & TERM_TAG_MASK); }
static inline Lab  term_aux(Term t) { return (Lab)((t >> TERM_AUX_SHIFT) & TERM_AUX_MASK); }
static inline Loc  term_loc(Term t) { return (Loc)(t >> TERM_LOC_SHIFT); }
static inline bool term_is_sub(Term t) { return (t & TERM_SUB_BIT) != 0; }
static inline Term term_set_sub(Term t) { return t | TERM_SUB_BIT; }
static inline Term term_clr_sub(Term t) { return t & ~TERM_SUB_BIT; }

/*============================================================================
 * Node Tags
 * 
 * We use a polarized design where nodes are either:
 *   - Constructors (positive): LAM, CON, NUM, ERA, SUP
 *   - Eliminators (negative): APP, OPR, DUP, MAT
 * 
 * An interaction happens when a constructor meets an eliminator.
 *===========================================================================*/

/* Special values */
#define TAG_NIL  0x00  /* Null/empty slot */
#define TAG_SUB  0x01  /* Substitution (value stored at location) */

/* Constructors (positive polarity) */
#define TAG_LAM  0x10  /* Lambda: \x.body (arity 0 closure) */
#define TAG_CLO  0x11  /* Closure: func_ptr + environment */
#define TAG_CON  0x12  /* Constructor/Pair: (a, b) */
#define TAG_NUM  0x13  /* Number (48-bit in aux+loc) */
#define TAG_ERA  0x14  /* Eraser */
#define TAG_SUP  0x15  /* Superposition: {a b} with label */
#define TAG_REF  0x16  /* Function reference (known at compile time) */

/* Eliminators (negative polarity) */
#define TAG_APP  0x20  /* Application: (f x) */
#define TAG_OPR  0x21  /* Binary operator: waiting for 2 nums */
#define TAG_DUP  0x22  /* Duplicator: !{a b} with label */
#define TAG_MAT  0x23  /* Pattern match/case */

/* Intermediate states */
#define TAG_OP1  0x30  /* Operator with first arg: (op x _) */
#define TAG_PAP  0x31  /* Partial application: closure waiting for more args */

/* Operators (stored in aux for OPR/OP1) */
#define OP_ADD  0x00
#define OP_SUB  0x01
#define OP_MUL  0x02
#define OP_DIV  0x03
#define OP_MOD  0x04
#define OP_EQ   0x05
#define OP_NE   0x06
#define OP_LT   0x07
#define OP_GT   0x08
#define OP_LE   0x09
#define OP_GE   0x0A

/*============================================================================
 * Number Encoding
 * 
 * Numbers use aux (16 bits) + loc (32 bits) = 48 bits.
 * We treat this as a signed 48-bit integer.
 *===========================================================================*/

static inline Term inet_num(int64_t n) {
    uint64_t bits = (uint64_t)n & 0xFFFFFFFFFFFFULL;  /* Mask to 48 bits */
    Lab aux = (Lab)(bits & 0xFFFF);
    Loc loc = (Loc)(bits >> 16);
    return term_new(TAG_NUM, aux, loc);
}

static inline int64_t inet_get_num(Term t) {
    uint64_t bits = ((uint64_t)term_aux(t)) | ((uint64_t)term_loc(t) << 16);
    /* Sign extend from 48 bits */
    if (bits & (1ULL << 47)) {
        bits |= 0xFFFF000000000000ULL;
    }
    return (int64_t)bits;
}

/*============================================================================
 * Configuration
 *===========================================================================*/

#define INET_MAX_THREADS    16
#define INET_HEAP_SIZE      (1ULL << 27)  /* 128M terms per thread = 1GB each */
#define INET_RBAG_SIZE      (1ULL << 20)  /* 1M redexes per thread */
#define INET_STACK_SIZE     (1ULL << 16)  /* 64K stack entries */

/* Cache line size for padding */
#define CACHE_LINE 64

/*============================================================================
 * Redex: A pair of terms to interact
 *===========================================================================*/

typedef struct {
    Term a;  /* First term (usually positive/constructor) */
    Term b;  /* Second term (usually negative/eliminator) */
} Redex;

typedef _Atomic(Redex) ARedex;

/*============================================================================
 * Thread-Local State
 * 
 * Each thread has:
 *   - Its own heap partition (no atomic allocation!)
 *   - A local redex deque (Chase-Lev work-stealing)
 *   - Statistics
 *===========================================================================*/

typedef struct ThreadMem {
    /* Identity */
    uint32_t tid;
    
    /* Heap allocation (within our partition) */
    uint32_t alloc;  /* Next allocation offset */
    
    /* Chase-Lev deque for redexes */
    Redex*   deque;           /* Redex buffer */
    _Atomic(int64_t) bottom;  /* Owner's end (push/pop) */
    _Atomic(int64_t) top;     /* Thieves' end (steal) */
    
    /* Statistics */
    uint64_t interactions;
    uint64_t steals;
    uint64_t steal_fails;
    uint64_t pushes;
    
    /* Padding to prevent false sharing */
    char _pad[CACHE_LINE];
} ThreadMem;

/*============================================================================
 * Function Definition
 *===========================================================================*/

struct INet;  /* Forward declaration */

typedef Term (*INetFunc)(struct INet* net, ThreadMem* tm, Term arg);

typedef struct {
    char     name[32];
    uint16_t arity;
    INetFunc impl;
} FuncDef;

/*============================================================================
 * Global Network State
 *===========================================================================*/

typedef struct INet {
    /* Partitioned heap: thread i owns [i*HEAP_SIZE, (i+1)*HEAP_SIZE) */
    ATerm* heap;
    
    /* Synchronization */
    _Atomic(uint64_t) interactions;  /* Total interaction count */
    _Atomic(uint32_t) idle_count;    /* Number of idle threads */
    _Atomic(int)      done;          /* Termination flag */
    
    /* Function table */
    FuncDef funcs[256];
    uint32_t num_funcs;
    
    /* Thread state */
    ThreadMem* threads[INET_MAX_THREADS];
    pthread_t  pthreads[INET_MAX_THREADS];
    int num_threads;
    
    /* Root location for result */
    Loc root_loc;
} INet;

/*============================================================================
 * API
 *===========================================================================*/

/* Lifecycle */
INet* inet_init(int num_threads);
void  inet_free(INet* net);

/* Function registration */
void inet_register_func(INet* net, const char* name, uint16_t arity, INetFunc impl);

/* Heap operations (thread-local, no atomics!) */
Loc  inet_alloc(INet* net, ThreadMem* tm, uint32_t count);
void inet_set(INet* net, Loc loc, Term val);
Term inet_get(INet* net, Loc loc);
Term inet_exchange(INet* net, Loc loc, Term val);

/* Substitution */
void inet_subst(INet* net, Loc loc, Term val);

/* Node construction */
Term inet_lam(INet* net, ThreadMem* tm, Loc var_loc, Term body);
Term inet_app(INet* net, ThreadMem* tm, Term fun, Term arg);
Term inet_con(INet* net, ThreadMem* tm, Term fst, Term snd);
Term inet_sup(INet* net, ThreadMem* tm, Lab label, Term a, Term b);
Term inet_dup(INet* net, ThreadMem* tm, Lab label, Term target);
Term inet_opr(INet* net, ThreadMem* tm, Lab op, Term a, Term b);
Term inet_ref(INet* net, ThreadMem* tm, uint16_t func_idx, Term arg);

/*
 * Closure construction and manipulation
 * 
 * Closure layout in heap:
 *   [0]: func_idx (as Term with TAG_REF) - which function to call
 *   [1]: arity (as NUM) - how many args needed
 *   [2]: env_size (as NUM) - number of captured variables
 *   [3..3+env_size): captured environment values
 *
 * When applied:
 *   - If arity > 1: create PAP (partial application) with arg added to env
 *   - If arity == 1: call function with full environment
 */
Term inet_closure(INet* net, ThreadMem* tm, uint16_t func_idx, uint16_t arity, 
                  Term* env, uint16_t env_size);

/* Clone a closure (shallow copy) - used for DUP */
Term inet_clone_closure(INet* net, ThreadMem* tm, Term clo);

/* Redex deque operations (Chase-Lev) */
void inet_push(INet* net, ThreadMem* tm, Term a, Term b);
bool inet_pop(INet* net, ThreadMem* tm, Redex* out);
bool inet_steal(INet* net, ThreadMem* tm, ThreadMem* victim, Redex* out);

/* Link: connect two terms (may create redex or substitute) */
void inet_link(INet* net, ThreadMem* tm, Term a, Term b);

/* Reduction */
int64_t inet_reduce(INet* net, Term root);

/* Debug */
void inet_print_term(INet* net, Term t);
void inet_print_stats(INet* net);

#endif /* SOMA_INET_H */
