/*
 * Soma HVM-Style Graph Reduction Runtime
 * 
 * Implementation based on HVM2's parallel architecture.
 * Key design: work-stealing deques with partitioned memory.
 */

#define _GNU_SOURCE
#include "soma_hvm.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sched.h>
#include <sys/mman.h>

/* Debug macro */
#ifdef HVM_DEBUG
#define HDEBUG(...) fprintf(stderr, "[HVM] " __VA_ARGS__)
#else
#define HDEBUG(...)
#endif

/*
 * Memory Management
 */

static void* alloc_huge(size_t size) {
    void* ptr = mmap(NULL, size, PROT_READ | PROT_WRITE,
                     MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
    if (ptr == MAP_FAILED) {
        perror("mmap failed");
        return NULL;
    }
    return ptr;
}

static ThreadMem* tm_new(uint32_t tid) {
    ThreadMem* tm = calloc(1, sizeof(ThreadMem));
    tm->tid = tid;
    tm->nput = 1;  /* Start at 1 (0 is reserved for NULL) */
    tm->itrs = 0;
    tm->rbag_lo = 0;  /* rput in HVM2 terms */
    tm->rbag_hi = 0;  /* hput in HVM2 terms */
    tm->sidx = 0;
    tm->steals = 0;
    tm->steal_attempts = 0;
    tm->pushes = 0;
    tm->max_rbag = 0;
    
    /* Allocate local buffers */
    tm->hbag  = calloc(HVM_RBAG_SIZE, sizeof(Redex));  /* High priority local */
    tm->stack = calloc(HVM_STACK_SIZE, sizeof(Term));
    tm->spos  = 0;
    
    /* rbag is in global memory, not allocated here */
    tm->rbag = NULL;
    
    return tm;
}

static void tm_free(ThreadMem* tm) {
    if (!tm) return;
    free(tm->hbag);
    free(tm->stack);
    free(tm);
}

HvmNet* hvm_init(int num_threads) {
    if (num_threads <= 0) num_threads = 1;
    if (num_threads > HVM_THREADS) num_threads = HVM_THREADS;
    
    HvmNet* net = calloc(1, sizeof(HvmNet));
    
    /* Allocate partitioned heap */
    size_t heap_size = (size_t)HVM_HEAP_SIZE * HVM_THREADS * sizeof(Term);
    net->heap = alloc_huge(heap_size);
    if (!net->heap) {
        free(net);
        return NULL;
    }
    
    /* Allocate global redex buffer (partitioned by thread for stealing) */
    size_t rbag_size = (size_t)HVM_RBAG_SIZE * HVM_THREADS * sizeof(Redex);
    net->rbag_buf = alloc_huge(rbag_size);
    net->rbag_cnt = calloc(HVM_THREADS, sizeof(_Atomic(uint32_t)));
    
    /* Initialize atomics */
    atomic_store(&net->itrs, 0);
    atomic_store(&net->idle, 0);
    atomic_store(&net->done, 0);
    
    /* Initialize thread memories */
    for (int i = 0; i < num_threads; i++) {
        net->tms[i] = tm_new(i);
    }
    
    net->num_funcs = 0;
    net->root_var = 0;
    
    return net;
}

void hvm_free(HvmNet* net) {
    if (!net) return;
    
    for (int i = 0; i < HVM_THREADS; i++) {
        tm_free(net->tms[i]);
    }
    
    if (net->heap) munmap((void*)net->heap, (size_t)HVM_HEAP_SIZE * HVM_THREADS * sizeof(Term));
    if (net->rbag_buf) munmap((void*)net->rbag_buf, (size_t)HVM_RBAG_SIZE * HVM_THREADS * sizeof(Redex));
    free(net->rbag_cnt);
    free(net);
}

void hvm_register_func(HvmNet* net, const char* name, uint16_t arity, HvmFunc func) {
    if (net->num_funcs >= 256) return;
    FuncDef* f = &net->funcs[net->num_funcs++];
    strncpy(f->name, name, 63);
    f->arity = arity;
    f->func = func;
}

/*
 * Node Operations - Key: NO ATOMICS for allocation!
 */

/* Allocate N slots from thread's partition - NO ATOMIC! */
Loc hvm_alloc_n(HvmNet* net, ThreadMem* tm, uint32_t n) {
    (void)net;
    Loc base = tm->tid * HVM_HEAP_SIZE;
    Loc offset = tm->nput % HVM_HEAP_SIZE;
    tm->nput += n;
    return base + offset;
}

Loc hvm_alloc(HvmNet* net, ThreadMem* tm) {
    return hvm_alloc_n(net, tm, 1);
}

/* Read/write heap - relaxed atomics for cross-thread visibility */
void hvm_set(HvmNet* net, Loc loc, Term val) {
    atomic_store_explicit(&net->heap[loc], val, memory_order_relaxed);
}

Term hvm_get(HvmNet* net, Loc loc) {
    return atomic_load_explicit(&net->heap[loc], memory_order_relaxed);
}

Term hvm_exchange(HvmNet* net, Loc loc, Term val) {
    return atomic_exchange_explicit(&net->heap[loc], val, memory_order_relaxed);
}

void hvm_sub(HvmNet* net, Loc loc, Term val) {
    hvm_set(net, loc, term_set_sub(val));
}

/*
 * Term Construction
 */

Term hvm_con(HvmNet* net, ThreadMem* tm, Term a, Term b) {
    Loc loc = hvm_alloc_n(net, tm, 2);
    hvm_set(net, loc, a);
    hvm_set(net, loc + 1, b);
    return term_new(TAG_CON, 0, loc);
}

Term hvm_opx(HvmNet* net, ThreadMem* tm, Lab op, Term a, Term b) {
    Loc loc = hvm_alloc_n(net, tm, 2);
    hvm_set(net, loc, a);
    hvm_set(net, loc + 1, b);
    return term_new(TAG_OPX, op, loc);
}

Term hvm_app(HvmNet* net, ThreadMem* tm, Term fun, Term arg) {
    Loc loc = hvm_alloc_n(net, tm, 2);
    hvm_set(net, loc, fun);
    hvm_set(net, loc + 1, arg);
    return term_new(TAG_APP, 0, loc);
}

Term hvm_lam(HvmNet* net, ThreadMem* tm, Term body) {
    Loc loc = hvm_alloc_n(net, tm, 2);
    hvm_set(net, loc, 0);
    hvm_set(net, loc + 1, body);
    return term_new(TAG_LAM, 0, loc);
}

Term hvm_ref(uint16_t func_idx, Term arg) {
    return term_new(TAG_REF, func_idx, term_loc(arg));
}

/*
 * Redex Bag - HVM2 style work-stealing deque
 * 
 * Each thread has a partition: [tid * HVM_RBAG_SIZE, (tid+1) * HVM_RBAG_SIZE)
 * Owner pushes/pops from TOP (LIFO) using rbag_lo as the stack pointer
 * Stealers scan from BOTTOM (index 0) upward (FIFO)
 */

static inline bool is_high_priority(Tag a, Tag b) {
    return (a == TAG_ERA || b == TAG_ERA);
}

/* Push redex - owner pushes to TOP */
void hvm_push_redex(HvmNet* net, ThreadMem* tm, Term a, Term b) {
    Redex r = {a, b};
    
    /* All redexes go to global buffer for stealing */
    if (tm->rbag_lo < HVM_RBAG_SIZE) {
        uint32_t idx = tm->tid * HVM_RBAG_SIZE + tm->rbag_lo;
        atomic_store_explicit(&net->rbag_buf[idx], r, memory_order_relaxed);
        tm->rbag_lo++;
        tm->pushes++;
        if (tm->rbag_lo > tm->max_rbag) tm->max_rbag = tm->rbag_lo;
    }
}

/* Pop redex - owner pops from TOP (LIFO) */
bool hvm_pop_redex(HvmNet* net, ThreadMem* tm, Redex* out) {
    /* High priority first */
    if (tm->rbag_hi > 0) {
        *out = tm->hbag[--tm->rbag_hi];
        return true;
    }
    
    /* Low priority from global buffer */
    if (tm->rbag_lo > 0) {
        uint32_t idx = tm->tid * HVM_RBAG_SIZE + (--tm->rbag_lo);
        Redex r = atomic_exchange_explicit(&net->rbag_buf[idx], (Redex){0, 0}, memory_order_relaxed);
        if (r.a != 0 || r.b != 0) {
            *out = r;
            return true;
        }
    }
    
    return false;
}

/* Get total redex count for this thread */
static inline uint32_t rbag_len(ThreadMem* tm) {
    return tm->rbag_lo + tm->rbag_hi;
}

/* Steal redex - stealer scans from BOTTOM (FIFO) */
bool hvm_steal_redex(HvmNet* net, ThreadMem* tm, Redex* out, int num_threads) {
    tm->steal_attempts++;
    
    /* Steal from previous thread (HVM2 pattern) */
    uint32_t victim = (tm->tid + num_threads - 1) % num_threads;
    uint32_t idx = victim * HVM_RBAG_SIZE + tm->sidx;
    
    Redex r = atomic_exchange_explicit(&net->rbag_buf[idx], (Redex){0, 0}, memory_order_relaxed);
    
    if (r.a != 0 || r.b != 0) {
        tm->sidx++;
        tm->steals++;
        *out = r;
        return true;
    } else {
        /* Empty slot - reset to try from beginning next time */
        tm->sidx = 0;
        return false;
    }
}

/*
 * Interaction Rules
 */

void hvm_link(HvmNet* net, ThreadMem* tm, Term a, Term b) {
    /* Follow substitutions */
    while (term_tag(a) == TAG_VAR) {
        Term val = hvm_get(net, term_loc(a));
        if (!term_is_sub(val)) break;
        a = term_rem_sub(val);
    }
    while (term_tag(b) == TAG_VAR) {
        Term val = hvm_get(net, term_loc(b));
        if (!term_is_sub(val)) break;
        b = term_rem_sub(val);
    }
    
    Tag ta = term_tag(a);
    Tag tb = term_tag(b);
    
    if (ta == TAG_VAR) {
        hvm_sub(net, term_loc(a), b);
        return;
    }
    if (tb == TAG_VAR) {
        hvm_sub(net, term_loc(b), a);
        return;
    }
    
    hvm_push_redex(net, tm, a, b);
}

static Term interact_app_lam(HvmNet* net, ThreadMem* tm, Term app, Term lam) {
    tm->itrs++;
    Loc app_loc = term_loc(app);
    Loc lam_loc = term_loc(lam);
    
    Term arg = hvm_get(net, app_loc + 1);
    Term body = hvm_get(net, lam_loc + 1);
    
    hvm_sub(net, lam_loc, arg);
    
    return body;
}

static Term interact_ref(HvmNet* net, ThreadMem* tm, Term ref) {
    tm->itrs++;
    uint16_t func_idx = term_aux(ref);
    
    if (func_idx >= net->num_funcs) {
        return term_new(TAG_ERA, 0, 0);
    }
    
    FuncDef* f = &net->funcs[func_idx];
    if (!f->func) {
        return term_new(TAG_ERA, 0, 0);
    }
    
    return f->func(net, tm, ref);
}

static void interact_era(HvmNet* net, ThreadMem* tm, Term other) {
    tm->itrs++;
    Tag tag = term_tag(other);
    Loc loc = term_loc(other);
    
    switch (tag) {
        case TAG_CON:
        case TAG_APP:
        case TAG_OPX:
        case TAG_OPY: {
            Term a = hvm_get(net, loc);
            Term b = hvm_get(net, loc + 1);
            hvm_link(net, tm, term_new(TAG_ERA, 0, 0), a);
            hvm_link(net, tm, term_new(TAG_ERA, 0, 0), b);
            break;
        }
        case TAG_LAM: {
            Term body = hvm_get(net, loc + 1);
            hvm_link(net, tm, term_new(TAG_ERA, 0, 0), body);
            break;
        }
        default:
            break;
    }
}

/*
 * Reducer - HVM3 style stack-based WHNF
 */

static Term reduce_whnf(HvmNet* net, ThreadMem* tm, Term term) {
    Term* stack = tm->stack;
    uint32_t spos = 0;
    uint32_t stop = 0;
    
    while (1) {
        Tag tag = term_tag(term);
        Loc loc = term_loc(term);
        
        /* Follow substitutions */
        if (tag == TAG_VAR) {
            Term val = hvm_get(net, loc);
            if (term_is_sub(val)) {
                term = term_rem_sub(val);
                continue;
            }
        }
        
        /* Push eliminators */
        switch (tag) {
            case TAG_APP: {
                stack[spos++] = term;
                term = hvm_get(net, loc);
                continue;
            }
            case TAG_OPX: {
                stack[spos++] = term;
                term = hvm_get(net, loc);
                continue;
            }
            case TAG_OPY: {
                stack[spos++] = term;
                term = hvm_get(net, loc);
                continue;
            }
            case TAG_REF: {
                term = interact_ref(net, tm, term);
                continue;
            }
            default:
                break;
        }
        
        /* Stack empty - WHNF */
        if (spos == stop) {
            return term;
        }
        
        /* Pop and interact */
        Term prev = stack[--spos];
        Tag prev_tag = term_tag(prev);
        Loc prev_loc = term_loc(prev);
        
        switch (prev_tag) {
            case TAG_APP: {
                if (tag == TAG_LAM) {
                    term = interact_app_lam(net, tm, prev, term);
                    continue;
                }
                if (tag == TAG_ERA) {
                    interact_era(net, tm, prev);
                    term = term_new(TAG_ERA, 0, 0);
                    continue;
                }
                break;
            }
            case TAG_OPX: {
                if (tag == TAG_NUM) {
                    tm->itrs++;
                    Lab op = term_aux(prev);
                    Term second = hvm_get(net, prev_loc + 1);
                    hvm_set(net, prev_loc + 0, second);
                    hvm_set(net, prev_loc + 1, term);
                    term = term_new(TAG_OPY, op, prev_loc);
                    continue;
                }
                if (tag == TAG_ERA) {
                    term = term_new(TAG_ERA, 0, 0);
                    continue;
                }
                break;
            }
            case TAG_OPY: {
                if (tag == TAG_NUM) {
                    tm->itrs++;
                    Lab op = term_aux(prev);
                    Term first_num = hvm_get(net, prev_loc + 1);
                    int64_t x = hvm_get_num(first_num);
                    int64_t y = hvm_get_num(term);
                    int64_t result;
                    switch (op) {
                        case OP_ADD: result = x + y; break;
                        case OP_SUB: result = x - y; break;
                        case OP_MUL: result = x * y; break;
                        case OP_DIV: result = y != 0 ? x / y : 0; break;
                        case OP_MOD: result = y != 0 ? x % y : 0; break;
                        case OP_EQ:  result = x == y ? 1 : 0; break;
                        case OP_NE:  result = x != y ? 1 : 0; break;
                        case OP_LT:  result = x < y ? 1 : 0; break;
                        case OP_GT:  result = x > y ? 1 : 0; break;
                        case OP_LE:  result = x <= y ? 1 : 0; break;
                        case OP_GE:  result = x >= y ? 1 : 0; break;
                        default:     result = 0; break;
                    }
                    term = hvm_num(result);
                    continue;
                }
                if (tag == TAG_ERA) {
                    term = term_new(TAG_ERA, 0, 0);
                    continue;
                }
                break;
            }
            default:
                break;
        }
        
        /* No interaction - unwind */
        hvm_set(net, prev_loc, term);
        while (spos > stop) {
            Term host = stack[--spos];
            hvm_set(net, term_loc(host), term);
            term = host;
        }
        return term;
    }
}

static bool interact(HvmNet* net, ThreadMem* tm) {
    Redex redex;
    if (!hvm_pop_redex(net, tm, &redex)) {
        return false;
    }
    
    Term a = reduce_whnf(net, tm, redex.a);
    Term b = reduce_whnf(net, tm, redex.b);
    
    hvm_link(net, tm, a, b);
    
    return true;
}



/*
 * Parallel Evaluator - HVM2 style
 */

/* Barrier using atomics */
static _Atomic(uint64_t) barrier_count = 0;
static _Atomic(uint64_t) barrier_gen = 0;

static void sync_threads(int num_threads) {
    uint64_t gen = atomic_load_explicit(&barrier_gen, memory_order_acquire);
    if (atomic_fetch_add_explicit(&barrier_count, 1, memory_order_acq_rel) == (uint64_t)(num_threads - 1)) {
        atomic_store_explicit(&barrier_count, 0, memory_order_relaxed);
        atomic_fetch_add_explicit(&barrier_gen, 1, memory_order_release);
    } else {
        while (atomic_load_explicit(&barrier_gen, memory_order_acquire) == gen) {
            sched_yield();
        }
    }
}

typedef struct {
    HvmNet*    net;
    ThreadMem* tm;
    int        num_threads;
} ThreadArg;

static void* evaluator_thread(void* arg) {
    ThreadArg* ta = (ThreadArg*)arg;
    HvmNet* net = ta->net;
    ThreadMem* tm = ta->tm;
    int num_threads = ta->num_threads;
    
    /* Initialize idle counter: all threads except 0 start idle */
    atomic_store_explicit(&net->idle, num_threads - 1, memory_order_relaxed);
    sync_threads(num_threads);
    
    uint32_t tick = 0;
    bool busy = (tm->tid == 0);  /* Only thread 0 has initial work */
    
    while (1) {
        tick++;
        
        /* If we have redexes, do work */
        if (rbag_len(tm) > 0) {
            if (!busy) {
                atomic_fetch_sub_explicit(&net->idle, 1, memory_order_relaxed);
                busy = true;
            }
            interact(net, tm);
        } else {
            /* No local work - update idle counter */
            if (busy) {
                atomic_fetch_add_explicit(&net->idle, 1, memory_order_relaxed);
                busy = false;
            }
            
            /* Try to steal */
            Redex stolen;
            if (hvm_steal_redex(net, tm, &stolen, num_threads)) {
                hvm_push_redex(net, tm, stolen.a, stolen.b);
                continue;
            }
            
            /* Chill */
            sched_yield();
            
            /* Check termination */
            if (tick % 256 == 0) {
                uint32_t idle_count = atomic_load_explicit(&net->idle, memory_order_relaxed);
                if (idle_count >= (uint32_t)num_threads) {
                    break;
                }
            }
        }
    }
    
    sync_threads(num_threads);
    
    atomic_fetch_add(&net->itrs, tm->itrs);
    tm->itrs = 0;
    
    return NULL;
}

/*
 * Main Entry Point
 */

int64_t hvm_reduce(HvmNet* net, Term root) {
    int num_threads = 0;
    for (int i = 0; i < HVM_THREADS; i++) {
        if (net->tms[i]) num_threads++;
    }
    if (num_threads == 0) num_threads = 1;
    
    /* Reset state */
    atomic_store(&net->idle, 0);
    atomic_store(&net->done, 0);
    atomic_store(&barrier_count, 0);
    atomic_store(&barrier_gen, 0);
    
    /* Reset thread state */
    for (int i = 0; i < num_threads; i++) {
        net->tms[i]->rbag_lo = 0;
        net->tms[i]->rbag_hi = 0;
        net->tms[i]->sidx = 0;
    }
    
    /* Set root variable */
    Loc root_var = hvm_alloc(net, net->tms[0]);
    hvm_set(net, root_var, TERM_NULL);
    net->root_var = root_var;
    
    /* Push initial redex */
    hvm_push_redex(net, net->tms[0], root, term_new(TAG_VAR, 0, root_var));
    
    if (num_threads == 1) {
        /* Single-threaded - simple loop */
        while (rbag_len(net->tms[0]) > 0) {
            interact(net, net->tms[0]);
        }
        atomic_fetch_add(&net->itrs, net->tms[0]->itrs);
        net->tms[0]->itrs = 0;
    } else {
        /* Multi-threaded */
        ThreadArg args[HVM_THREADS];
        
        for (int i = 0; i < num_threads; i++) {
            args[i].net = net;
            args[i].tm = net->tms[i];
            args[i].num_threads = num_threads;
        }
        
        for (int i = 1; i < num_threads; i++) {
            pthread_create(&net->threads[i], NULL, evaluator_thread, &args[i]);
        }
        
        evaluator_thread(&args[0]);
        
        for (int i = 1; i < num_threads; i++) {
            pthread_join(net->threads[i], NULL);
        }
    }
    
    /* Read result */
    Term result = hvm_get(net, root_var);
    if (term_is_sub(result)) {
        result = term_rem_sub(result);
        if (term_tag(result) == TAG_NUM) {
            return hvm_get_num(result);
        }
    }
    
    fprintf(stderr, "hvm_reduce: did not reduce to number\n");
    return 0;
}

/*
 * Debug
 */

void hvm_print_term(HvmNet* net, Term t) {
    (void)net;
    Tag tag = term_tag(t);
    switch (tag) {
        case TAG_NUM: fprintf(stderr, "%ld", hvm_get_num(t)); break;
        case TAG_ERA: fprintf(stderr, "*"); break;
        case TAG_VAR: fprintf(stderr, "x%u", term_loc(t)); break;
        case TAG_REF: fprintf(stderr, "@%u", term_aux(t)); break;
        case TAG_CON: fprintf(stderr, "CON@%u", term_loc(t)); break;
        case TAG_APP: fprintf(stderr, "APP@%u", term_loc(t)); break;
        case TAG_LAM: fprintf(stderr, "LAM@%u", term_loc(t)); break;
        case TAG_OPX: fprintf(stderr, "OPX[%u]@%u", term_aux(t), term_loc(t)); break;
        case TAG_OPY: fprintf(stderr, "OPY[%u]@%u", term_aux(t), term_loc(t)); break;
        default: fprintf(stderr, "?%02x", tag); break;
    }
}

void hvm_print_stats(HvmNet* net) {
    fprintf(stderr, "\n=== HVM Stats ===\n");
    fprintf(stderr, "Total interactions: %lu\n", atomic_load(&net->itrs));
    
    uint64_t total_steals = 0;
    uint64_t total_attempts = 0;
    uint64_t total_pushes = 0;
    for (int i = 0; i < HVM_THREADS; i++) {
        if (net->tms[i]) {
            fprintf(stderr, "Thread %d: itrs=%lu pushes=%lu max_rbag=%lu steals=%lu/%lu\n",
                    i, net->tms[i]->itrs, net->tms[i]->pushes, net->tms[i]->max_rbag,
                    net->tms[i]->steals, net->tms[i]->steal_attempts);
            total_steals += net->tms[i]->steals;
            total_attempts += net->tms[i]->steal_attempts;
            total_pushes += net->tms[i]->pushes;
        }
    }
    fprintf(stderr, "Total pushes: %lu, steals: %lu/%lu (%.1f%%)\n", 
            total_pushes, total_steals, total_attempts,
            total_attempts > 0 ? 100.0 * total_steals / total_attempts : 0.0);
    fprintf(stderr, "=================\n");
}
