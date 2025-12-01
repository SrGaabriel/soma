/*
 * Soma Interaction Net Runtime - Maximum Parallelism
 * 
 * Hybrid approach: stack-based reduction with work-stealing parallelism.
 * 
 * Key insight: Use a stack to track pending work within a thread,
 * but push independent subtrees as redexes for other threads to steal.
 */

#define _GNU_SOURCE
#include "soma_inet.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sched.h>
#include <sys/mman.h>

/*============================================================================
 * Debug
 *===========================================================================*/

#ifdef INET_DEBUG
#define IDEBUG(...) fprintf(stderr, "[INET] " __VA_ARGS__)
#else
#define IDEBUG(...)
#endif

/*============================================================================
 * Memory Allocation
 *===========================================================================*/

static void* alloc_huge(size_t size) {
    void* ptr = mmap(NULL, size, PROT_READ | PROT_WRITE,
                     MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
    if (ptr == MAP_FAILED) {
        perror("mmap");
        return NULL;
    }
    return ptr;
}

static ThreadMem* thread_new(uint32_t tid) {
    ThreadMem* tm = aligned_alloc(CACHE_LINE, sizeof(ThreadMem));
    memset(tm, 0, sizeof(ThreadMem));
    
    tm->tid = tid;
    tm->alloc = 1;  /* 0 is reserved for NULL */
    
    /* Allocate Chase-Lev deque */
    tm->deque = aligned_alloc(CACHE_LINE, INET_RBAG_SIZE * sizeof(Redex));
    atomic_store(&tm->bottom, 0);
    atomic_store(&tm->top, 0);
    
    return tm;
}

static void thread_free(ThreadMem* tm) {
    if (!tm) return;
    free(tm->deque);
    free(tm);
}

INet* inet_init(int num_threads) {
    if (num_threads <= 0) num_threads = 1;
    if (num_threads > INET_MAX_THREADS) num_threads = INET_MAX_THREADS;
    
    INet* net = aligned_alloc(CACHE_LINE, sizeof(INet));
    memset(net, 0, sizeof(INet));
    
    /* Allocate partitioned heap */
    size_t heap_size = (size_t)INET_HEAP_SIZE * INET_MAX_THREADS * sizeof(Term);
    net->heap = alloc_huge(heap_size);
    if (!net->heap) {
        free(net);
        return NULL;
    }
    
    /* Initialize atomics */
    atomic_store(&net->interactions, 0);
    atomic_store(&net->idle_count, 0);
    atomic_store(&net->done, 0);
    
    /* Initialize threads */
    net->num_threads = num_threads;
    for (int i = 0; i < num_threads; i++) {
        net->threads[i] = thread_new(i);
    }
    
    net->num_funcs = 0;
    net->root_loc = 0;
    
    return net;
}

void inet_free(INet* net) {
    if (!net) return;
    
    for (int i = 0; i < INET_MAX_THREADS; i++) {
        thread_free(net->threads[i]);
    }
    
    if (net->heap) {
        munmap((void*)net->heap, (size_t)INET_HEAP_SIZE * INET_MAX_THREADS * sizeof(Term));
    }
    
    free(net);
}

void inet_register_func(INet* net, const char* name, uint16_t arity, INetFunc impl) {
    if (net->num_funcs >= 256) return;
    FuncDef* f = &net->funcs[net->num_funcs++];
    strncpy(f->name, name, 31);
    f->arity = arity;
    f->impl = impl;
}

/*============================================================================
 * Heap Operations
 *===========================================================================*/

Loc inet_alloc(INet* net, ThreadMem* tm, uint32_t count) {
    (void)net;
    Loc base = (Loc)tm->tid * INET_HEAP_SIZE;
    Loc offset = tm->alloc;
    tm->alloc += count;
    return base + offset;
}

void inet_set(INet* net, Loc loc, Term val) {
    atomic_store_explicit(&net->heap[loc], val, memory_order_relaxed);
}

Term inet_get(INet* net, Loc loc) {
    return atomic_load_explicit(&net->heap[loc], memory_order_relaxed);
}

Term inet_exchange(INet* net, Loc loc, Term val) {
    return atomic_exchange_explicit(&net->heap[loc], val, memory_order_relaxed);
}

void inet_subst(INet* net, Loc loc, Term val) {
    inet_set(net, loc, term_set_sub(val));
}

/*============================================================================
 * Node Construction
 *===========================================================================*/

Term inet_lam(INet* net, ThreadMem* tm, Loc var_loc, Term body) {
    Loc loc = inet_alloc(net, tm, 2);
    inet_set(net, loc, term_new(TAG_NIL, 0, var_loc));
    inet_set(net, loc + 1, body);
    return term_new(TAG_LAM, 0, loc);
}

Term inet_app(INet* net, ThreadMem* tm, Term fun, Term arg) {
    Loc loc = inet_alloc(net, tm, 2);
    inet_set(net, loc, fun);
    inet_set(net, loc + 1, arg);
    return term_new(TAG_APP, 0, loc);
}

Term inet_con(INet* net, ThreadMem* tm, Term fst, Term snd) {
    Loc loc = inet_alloc(net, tm, 2);
    inet_set(net, loc, fst);
    inet_set(net, loc + 1, snd);
    return term_new(TAG_CON, 0, loc);
}

Term inet_sup(INet* net, ThreadMem* tm, Lab label, Term a, Term b) {
    Loc loc = inet_alloc(net, tm, 2);
    inet_set(net, loc, a);
    inet_set(net, loc + 1, b);
    return term_new(TAG_SUP, label, loc);
}

Term inet_dup(INet* net, ThreadMem* tm, Lab label, Term target) {
    Loc loc = inet_alloc(net, tm, 3);
    inet_set(net, loc, target);
    inet_set(net, loc + 1, term_new(TAG_NIL, 0, 0));
    inet_set(net, loc + 2, term_new(TAG_NIL, 0, 0));
    return term_new(TAG_DUP, label, loc);
}

Term inet_opr(INet* net, ThreadMem* tm, Lab op, Term a, Term b) {
    Loc loc = inet_alloc(net, tm, 2);
    inet_set(net, loc, a);
    inet_set(net, loc + 1, b);
    return term_new(TAG_OPR, op, loc);
}

Term inet_ref(INet* net, ThreadMem* tm, uint16_t func_idx, Term arg) {
    Loc loc = inet_alloc(net, tm, 1);
    inet_set(net, loc, arg);
    return term_new(TAG_REF, func_idx, loc);
}

/*============================================================================
 * Chase-Lev Work-Stealing Deque
 *===========================================================================*/

void inet_push(INet* net, ThreadMem* tm, Term a, Term b) {
    (void)net;
    int64_t b_idx = atomic_load_explicit(&tm->bottom, memory_order_relaxed);
    
    tm->deque[b_idx % INET_RBAG_SIZE] = (Redex){a, b};
    
    atomic_thread_fence(memory_order_release);
    atomic_store_explicit(&tm->bottom, b_idx + 1, memory_order_relaxed);
    
    tm->pushes++;
}

bool inet_pop(INet* net, ThreadMem* tm, Redex* out) {
    (void)net;
    int64_t b_idx = atomic_load_explicit(&tm->bottom, memory_order_relaxed) - 1;
    atomic_store_explicit(&tm->bottom, b_idx, memory_order_relaxed);
    
    atomic_thread_fence(memory_order_seq_cst);
    
    int64_t t_idx = atomic_load_explicit(&tm->top, memory_order_relaxed);
    
    if (t_idx <= b_idx) {
        *out = tm->deque[b_idx % INET_RBAG_SIZE];
        
        if (t_idx == b_idx) {
            if (!atomic_compare_exchange_strong_explicit(
                    &tm->top, &t_idx, t_idx + 1,
                    memory_order_seq_cst, memory_order_relaxed)) {
                atomic_store_explicit(&tm->bottom, t_idx + 1, memory_order_relaxed);
                return false;
            }
            atomic_store_explicit(&tm->bottom, t_idx + 1, memory_order_relaxed);
        }
        return true;
    } else {
        atomic_store_explicit(&tm->bottom, t_idx, memory_order_relaxed);
        return false;
    }
}

bool inet_steal(INet* net, ThreadMem* tm, ThreadMem* victim, Redex* out) {
    (void)net;
    (void)tm;
    
    int64_t t_idx = atomic_load_explicit(&victim->top, memory_order_acquire);
    atomic_thread_fence(memory_order_seq_cst);
    int64_t b_idx = atomic_load_explicit(&victim->bottom, memory_order_acquire);
    
    if (t_idx < b_idx) {
        *out = victim->deque[t_idx % INET_RBAG_SIZE];
        
        if (atomic_compare_exchange_strong_explicit(
                &victim->top, &t_idx, t_idx + 1,
                memory_order_seq_cst, memory_order_relaxed)) {
            return true;
        }
    }
    return false;
}

static inline int64_t deque_size(ThreadMem* tm) {
    int64_t b = atomic_load_explicit(&tm->bottom, memory_order_relaxed);
    int64_t t = atomic_load_explicit(&tm->top, memory_order_relaxed);
    return b - t;
}

/*============================================================================
 * Compute binary operation
 *===========================================================================*/

static inline int64_t compute_op(Lab op, int64_t x, int64_t y) {
    switch (op) {
        case OP_ADD: return x + y;
        case OP_SUB: return x - y;
        case OP_MUL: return x * y;
        case OP_DIV: return y != 0 ? x / y : 0;
        case OP_MOD: return y != 0 ? x % y : 0;
        case OP_EQ:  return x == y ? 1 : 0;
        case OP_NE:  return x != y ? 1 : 0;
        case OP_LT:  return x < y ? 1 : 0;
        case OP_GT:  return x > y ? 1 : 0;
        case OP_LE:  return x <= y ? 1 : 0;
        case OP_GE:  return x >= y ? 1 : 0;
        default:     return 0;
    }
}

/*============================================================================
 * Stack-based Evaluator
 * 
 * This is the core reduction engine. It uses a local stack to track
 * pending work (eliminators waiting for values) and pushes independent
 * subtrees as redexes for parallel reduction.
 * 
 * Key insight: We reduce the LEFT child of binary operators on-stack,
 * and push the RIGHT child as a redex (parallel work).
 *===========================================================================*/

/* Stack frame for pending operations */
typedef struct {
    uint8_t  op;      /* Operation type */
    uint8_t  state;   /* 0=waiting for first, 1=have first waiting for second */
    Lab      aux;     /* Operator code or label */
    Loc      loc;     /* Location in heap */
    int64_t  val;     /* First operand value (when state=1) */
    Loc      out;     /* Where to write result */
} Frame;

#define MAX_STACK 65536

/*
 * reduce_term: Reduce a term to a value (NUM or ERA)
 * 
 * Returns the reduced term.
 * Pushes parallel work as redexes.
 */
static Term reduce_term(INet* net, ThreadMem* tm, Term term) {
    Frame stack[MAX_STACK];
    int sp = 0;
    
    while (1) {
        /* Follow substitutions */
        while (term_is_sub(term)) {
            term = term_clr_sub(term);
        }
        
        Tag tag = term_tag(term);
        
        /* If it's a value, unwind stack */
        if (tag == TAG_NUM || tag == TAG_ERA) {
            while (sp > 0) {
                Frame* f = &stack[--sp];
                
                if (f->op == TAG_OPR) {
                    if (f->state == 0) {
                        /* Got first operand, now need second */
                        f->val = inet_get_num(term);
                        f->state = 1;
                        
                        /* Get second operand and reduce it */
                        term = inet_get(net, f->loc + 1);
                        while (term_is_sub(term)) term = term_clr_sub(term);
                        sp++;  /* Keep frame on stack */
                        break;  /* Continue reducing */
                    } else {
                        /* Got second operand, compute result */
                        int64_t result = compute_op(f->aux, f->val, inet_get_num(term));
                        term = inet_num(result);
                        tm->interactions++;
                        /* Continue unwinding */
                    }
                } else if (f->op == TAG_REF) {
                    /* Function call completed - shouldn't happen here */
                    /* Functions expand inline, don't return through stack */
                }
            }
            
            if (sp == 0) {
                return term;  /* Done! */
            }
            continue;
        }
        
        /* Handle different node types */
        switch (tag) {
            case TAG_OPR: {
                /* Binary operator - push frame, reduce first operand */
                Loc loc = term_loc(term);
                Lab op = term_aux(term);
                
                if (sp >= MAX_STACK - 1) {
                    fprintf(stderr, "Stack overflow in reduce_term\n");
                    return inet_num(0);
                }
                
                stack[sp].op = TAG_OPR;
                stack[sp].state = 0;
                stack[sp].aux = op;
                stack[sp].loc = loc;
                stack[sp].out = 0;
                sp++;
                
                /* Reduce first operand */
                term = inet_get(net, loc);
                break;
            }
            
            case TAG_REF: {
                /* Function call - inline expansion */
                uint16_t func_idx = term_aux(term);
                Loc loc = term_loc(term);
                
                if (func_idx >= net->num_funcs || !net->funcs[func_idx].impl) {
                    term = term_new(TAG_ERA, 0, 0);
                    break;
                }
                
                Term arg = inet_get(net, loc);
                term = net->funcs[func_idx].impl(net, tm, arg);
                tm->interactions++;
                break;
            }
            
            case TAG_NIL:
            case TAG_SUB: {
                /* Variable - read its value */
                Loc loc = term_loc(term);
                term = inet_get(net, loc);
                break;
            }
            
            default:
                /* Unknown - treat as ERA */
                IDEBUG("Unknown tag in reduce_term: %02x\n", tag);
                term = term_new(TAG_ERA, 0, 0);
                break;
        }
    }
}

/*
 * reduce_parallel: Reduce with work-stealing parallelism
 * 
 * Similar to reduce_term but pushes right subtrees as redexes
 * that can be stolen by other threads.
 */
typedef struct {
    uint8_t  op;
    uint8_t  state;
    Lab      aux;
    Loc      loc;
    int64_t  val;
    Loc      result_slot;  /* Where the second operand result will be written */
} PFrame;

static Term reduce_parallel(INet* net, ThreadMem* tm, Term term, int depth) {
    PFrame stack[MAX_STACK];
    int sp = 0;
    
    /* Depth limit for pushing parallel work */
    const int PARALLEL_DEPTH = 4;
    
    while (1) {
        while (term_is_sub(term)) {
            term = term_clr_sub(term);
        }
        
        Tag tag = term_tag(term);
        
        if (tag == TAG_NUM || tag == TAG_ERA) {
            while (sp > 0) {
                PFrame* f = &stack[--sp];
                
                if (f->op == TAG_OPR) {
                    if (f->state == 0) {
                        f->val = inet_get_num(term);
                        f->state = 1;
                        
                        if (f->result_slot != 0) {
                            /* Second operand was pushed as parallel work */
                            /* Wait for it by reading the slot */
                            Term slot_val = inet_get(net, f->result_slot);
                            while (!term_is_sub(slot_val)) {
                                /* Spin-wait or do other work */
                                Redex r;
                                if (inet_pop(net, tm, &r)) {
                                    /* Do some other work while waiting */
                                    Term res = reduce_parallel(net, tm, r.a, depth + 1);
                                    inet_subst(net, term_loc(r.b), res);
                                }
                                slot_val = inet_get(net, f->result_slot);
                            }
                            term = term_clr_sub(slot_val);
                            sp++;
                            break;
                        } else {
                            /* Reduce second operand locally */
                            term = inet_get(net, f->loc + 1);
                            while (term_is_sub(term)) term = term_clr_sub(term);
                            sp++;
                            break;
                        }
                    } else {
                        int64_t result = compute_op(f->aux, f->val, inet_get_num(term));
                        term = inet_num(result);
                        tm->interactions++;
                    }
                }
            }
            
            if (sp == 0) {
                return term;
            }
            continue;
        }
        
        switch (tag) {
            case TAG_OPR: {
                Loc loc = term_loc(term);
                Lab op = term_aux(term);
                
                if (sp >= MAX_STACK - 1) {
                    fprintf(stderr, "Stack overflow\n");
                    return inet_num(0);
                }
                
                stack[sp].op = TAG_OPR;
                stack[sp].state = 0;
                stack[sp].aux = op;
                stack[sp].loc = loc;
                stack[sp].result_slot = 0;
                
                /* Push right subtree as parallel work if shallow enough */
                Term right = inet_get(net, loc + 1);
                if (depth < PARALLEL_DEPTH && !term_is_sub(right) && term_tag(right) != TAG_NUM) {
                    /* Allocate slot for result */
                    Loc slot = inet_alloc(net, tm, 1);
                    inet_set(net, slot, term_new(TAG_NIL, 0, 0));
                    stack[sp].result_slot = slot;
                    
                    /* Push as redex: (right_subtree, result_slot) */
                    inet_push(net, tm, right, term_new(TAG_NIL, 0, slot));
                }
                
                sp++;
                term = inet_get(net, loc);  /* Reduce left */
                depth++;
                break;
            }
            
            case TAG_REF: {
                uint16_t func_idx = term_aux(term);
                Loc loc = term_loc(term);
                
                if (func_idx >= net->num_funcs || !net->funcs[func_idx].impl) {
                    term = term_new(TAG_ERA, 0, 0);
                    break;
                }
                
                Term arg = inet_get(net, loc);
                term = net->funcs[func_idx].impl(net, tm, arg);
                tm->interactions++;
                break;
            }
            
            case TAG_NIL:
            case TAG_SUB: {
                Loc loc = term_loc(term);
                term = inet_get(net, loc);
                break;
            }
            
            default:
                IDEBUG("Unknown tag: %02x\n", tag);
                term = term_new(TAG_ERA, 0, 0);
                break;
        }
    }
}

/*============================================================================
 * Worker Thread
 *===========================================================================*/

typedef struct {
    INet*      net;
    ThreadMem* tm;
    int        num_threads;
} WorkerArg;

static void* worker_thread(void* arg) {
    WorkerArg* wa = (WorkerArg*)arg;
    INet* net = wa->net;
    ThreadMem* tm = wa->tm;
    int num_threads = wa->num_threads;
    
    uint32_t idle_spins = 0;
    const uint32_t MAX_IDLE_SPINS = 1000;
    
    while (!atomic_load_explicit(&net->done, memory_order_relaxed)) {
        Redex r;
        
        /* Try local pop */
        if (inet_pop(net, tm, &r)) {
            Term result = reduce_parallel(net, tm, r.a, 0);
            /* r.b is the slot to write result */
            if (term_tag(r.b) == TAG_NIL) {
                inet_subst(net, term_loc(r.b), result);
            }
            idle_spins = 0;
            continue;
        }
        
        /* Try stealing */
        bool stolen = false;
        for (int i = 1; i < num_threads && !stolen; i++) {
            int victim_id = (tm->tid + i) % num_threads;
            ThreadMem* victim = net->threads[victim_id];
            
            if (inet_steal(net, tm, victim, &r)) {
                tm->steals++;
                Term result = reduce_parallel(net, tm, r.a, 0);
                if (term_tag(r.b) == TAG_NIL) {
                    inet_subst(net, term_loc(r.b), result);
                }
                stolen = true;
                idle_spins = 0;
            } else {
                tm->steal_fails++;
            }
        }
        
        if (!stolen) {
            idle_spins++;
            
            if (idle_spins > MAX_IDLE_SPINS) {
                atomic_fetch_add_explicit(&net->idle_count, 1, memory_order_relaxed);
                
                while (!atomic_load_explicit(&net->done, memory_order_relaxed)) {
                    bool any_work = false;
                    for (int i = 0; i < num_threads && !any_work; i++) {
                        if (deque_size(net->threads[i]) > 0) {
                            any_work = true;
                        }
                    }
                    
                    if (any_work) {
                        atomic_fetch_sub_explicit(&net->idle_count, 1, memory_order_relaxed);
                        break;
                    }
                    
                    uint32_t idle = atomic_load_explicit(&net->idle_count, memory_order_relaxed);
                    if (idle >= (uint32_t)num_threads) {
                        atomic_store_explicit(&net->done, 1, memory_order_relaxed);
                        break;
                    }
                    
                    sched_yield();
                }
                
                idle_spins = 0;
            } else {
                for (volatile int i = 0; i < 100; i++);
            }
        }
    }
    
    atomic_fetch_add(&net->interactions, tm->interactions);
    
    return NULL;
}

/*============================================================================
 * Main Entry Point
 *===========================================================================*/

int64_t inet_reduce(INet* net, Term root) {
    int num_threads = net->num_threads;
    
    /* Reset state */
    atomic_store(&net->interactions, 0);
    atomic_store(&net->idle_count, 0);
    atomic_store(&net->done, 0);
    
    for (int i = 0; i < num_threads; i++) {
        atomic_store(&net->threads[i]->bottom, 0);
        atomic_store(&net->threads[i]->top, 0);
        net->threads[i]->interactions = 0;
        net->threads[i]->steals = 0;
        net->threads[i]->steal_fails = 0;
        net->threads[i]->pushes = 0;
    }
    
    if (num_threads == 1) {
        /* Single-threaded: use simple stack-based reducer */
        Term result = reduce_term(net, net->threads[0], root);
        atomic_fetch_add(&net->interactions, net->threads[0]->interactions);
        
        if (term_tag(result) == TAG_NUM) {
            return inet_get_num(result);
        }
        return 0;
    }
    
    /* Multi-threaded: use parallel reducer with work-stealing */
    
    /* Allocate root slot */
    Loc root_loc = inet_alloc(net, net->threads[0], 1);
    inet_set(net, root_loc, term_new(TAG_NIL, 0, 0));
    net->root_loc = root_loc;
    
    /* Push root as initial work */
    inet_push(net, net->threads[0], root, term_new(TAG_NIL, 0, root_loc));
    
    /* Start workers */
    WorkerArg args[INET_MAX_THREADS];
    
    for (int i = 0; i < num_threads; i++) {
        args[i].net = net;
        args[i].tm = net->threads[i];
        args[i].num_threads = num_threads;
    }
    
    for (int i = 1; i < num_threads; i++) {
        pthread_create(&net->pthreads[i], NULL, worker_thread, &args[i]);
    }
    
    worker_thread(&args[0]);
    
    for (int i = 1; i < num_threads; i++) {
        pthread_join(net->pthreads[i], NULL);
    }
    
    /* Read result */
    Term result = inet_get(net, root_loc);
    if (term_is_sub(result)) {
        result = term_clr_sub(result);
        if (term_tag(result) == TAG_NUM) {
            return inet_get_num(result);
        }
    }
    
    fprintf(stderr, "inet_reduce: did not reduce to number (tag=%02x)\n", term_tag(result));
    return 0;
}

/*============================================================================
 * Debug
 *===========================================================================*/

void inet_print_term(INet* net, Term t) {
    (void)net;
    Tag tag = term_tag(t);
    bool sub = term_is_sub(t);
    
    if (sub) fprintf(stderr, "!");
    
    switch (tag) {
        case TAG_NIL: fprintf(stderr, "NIL@%u", term_loc(t)); break;
        case TAG_NUM: fprintf(stderr, "%ld", inet_get_num(t)); break;
        case TAG_ERA: fprintf(stderr, "*"); break;
        case TAG_LAM: fprintf(stderr, "LAM@%u", term_loc(t)); break;
        case TAG_APP: fprintf(stderr, "APP@%u", term_loc(t)); break;
        case TAG_CON: fprintf(stderr, "CON@%u", term_loc(t)); break;
        case TAG_SUP: fprintf(stderr, "SUP[%u]@%u", term_aux(t), term_loc(t)); break;
        case TAG_DUP: fprintf(stderr, "DUP[%u]@%u", term_aux(t), term_loc(t)); break;
        case TAG_OPR: fprintf(stderr, "OPR[%u]@%u", term_aux(t), term_loc(t)); break;
        case TAG_OP1: fprintf(stderr, "OP1[%u]@%u", term_aux(t), term_loc(t)); break;
        case TAG_REF: fprintf(stderr, "@%u", term_aux(t)); break;
        default: fprintf(stderr, "?%02x", tag); break;
    }
}

void inet_print_stats(INet* net) {
    fprintf(stderr, "\n=== INet Stats ===\n");
    fprintf(stderr, "Total interactions: %lu\n", atomic_load(&net->interactions));
    
    uint64_t total_steals = 0;
    uint64_t total_fails = 0;
    uint64_t total_pushes = 0;
    
    for (int i = 0; i < net->num_threads; i++) {
        ThreadMem* tm = net->threads[i];
        if (tm) {
            fprintf(stderr, "Thread %d: itrs=%lu pushes=%lu steals=%lu fails=%lu\n",
                    i, tm->interactions, tm->pushes, tm->steals, tm->steal_fails);
            total_steals += tm->steals;
            total_fails += tm->steal_fails;
            total_pushes += tm->pushes;
        }
    }
    
    fprintf(stderr, "Total: pushes=%lu steals=%lu (%.1f%% success)\n",
            total_pushes, total_steals,
            (total_steals + total_fails) > 0 
                ? 100.0 * total_steals / (total_steals + total_fails) : 0.0);
    fprintf(stderr, "==================\n");
}
