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

/* Portable CPU pause/yield for spin loops */
#if defined(__x86_64__) || defined(__i386__)
#include <immintrin.h>
#define cpu_pause() _mm_pause()
#elif defined(__aarch64__)
#define cpu_pause() __asm__ __volatile__("yield" ::: "memory")
#else
#define cpu_pause() ((void)0)
#endif

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
    const Loc base = (Loc)tm->tid * INET_HEAP_SIZE;
    const Loc offset = tm->alloc;
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
    atomic_store_explicit(&net->heap[loc], term_set_sub(val), memory_order_relaxed);
}

/*============================================================================
 * Node Construction
 * 
 * Direct heap access using cached pointer where possible
 *===========================================================================*/

Term inet_lam(INet* net, ThreadMem* tm, Loc var_loc, Term body) {
    const Loc loc = inet_alloc(net, tm, 2);
    ATerm* const heap = net->heap;
    atomic_store_explicit(&heap[loc], term_new(TAG_NIL, 0, var_loc), memory_order_relaxed);
    atomic_store_explicit(&heap[loc + 1], body, memory_order_relaxed);
    return term_new(TAG_LAM, 0, loc);
}

Term inet_app(INet* net, ThreadMem* tm, Term fun, Term arg) {
    const Loc loc = inet_alloc(net, tm, 2);
    ATerm* const heap = net->heap;
    atomic_store_explicit(&heap[loc], fun, memory_order_relaxed);
    atomic_store_explicit(&heap[loc + 1], arg, memory_order_relaxed);
    return term_new(TAG_APP, 0, loc);
}

Term inet_con(INet* net, ThreadMem* tm, Term fst, Term snd) {
    const Loc loc = inet_alloc(net, tm, 2);
    ATerm* const heap = net->heap;
    atomic_store_explicit(&heap[loc], fst, memory_order_relaxed);
    atomic_store_explicit(&heap[loc + 1], snd, memory_order_relaxed);
    return term_new(TAG_CON, 0, loc);
}

Term inet_sup(INet* net, ThreadMem* tm, Lab label, Term a, Term b) {
    const Loc loc = inet_alloc(net, tm, 2);
    ATerm* const heap = net->heap;
    atomic_store_explicit(&heap[loc], a, memory_order_relaxed);
    atomic_store_explicit(&heap[loc + 1], b, memory_order_relaxed);
    return term_new(TAG_SUP, label, loc);
}

Term inet_dup(INet* net, ThreadMem* tm, Lab label, Term target) {
    const Loc loc = inet_alloc(net, tm, 3);
    ATerm* const heap = net->heap;
    atomic_store_explicit(&heap[loc], target, memory_order_relaxed);
    atomic_store_explicit(&heap[loc + 1], term_new(TAG_NIL, 0, 0), memory_order_relaxed);
    atomic_store_explicit(&heap[loc + 2], term_new(TAG_NIL, 0, 0), memory_order_relaxed);
    return term_new(TAG_DUP, label, loc);
}

/* Forward declaration for perform_dup_interaction */
static void perform_dup_interaction(INet* net, ThreadMem* tm, Term dup, Term target);

/*
 * inet_dup_eager: Create a DUP and immediately trigger the interaction
 * 
 * This is used in lgraph mode where we need both projections immediately.
 * Returns the DUP term; the proj0/proj1 slots are filled after the call.
 * Caller can use inet_dup_proj0_slot/inet_dup_proj1_slot to get slot locations,
 * then inet_get to read the results.
 */
Term inet_dup_eager(INet* net, ThreadMem* tm, Lab label, Term target) {
    Loc loc = inet_alloc(net, tm, 3);
    inet_set(net, loc, target);
    inet_set(net, loc + 1, term_new(TAG_NIL, 0, 0));
    inet_set(net, loc + 2, term_new(TAG_NIL, 0, 0));
    Term dup = term_new(TAG_DUP, label, loc);
    
    /* Immediately trigger the DUP interaction */
    perform_dup_interaction(net, tm, dup, target);
    
    return dup;
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
 * Closure Construction and Manipulation
 *
 * Closure layout in heap:
 *   [0]: func_idx (stored in aux of the CLO term itself)
 *   [0]: arity remaining (as NUM)
 *   [1]: env_size (as NUM)
 *   [2..2+env_size): captured environment values
 *
 * The func_idx is stored in the Term's aux field for efficiency.
 *===========================================================================*/

Term inet_closure(INet* net, ThreadMem* tm, uint16_t func_idx, uint16_t arity,
                  Term* env, uint16_t env_size) {
    Loc loc = inet_alloc(net, tm, 2 + env_size);
    inet_set(net, loc, inet_num(arity));
    inet_set(net, loc + 1, inet_num(env_size));
    for (uint16_t i = 0; i < env_size; i++) {
        inet_set(net, loc + 2 + i, env[i]);
    }
    return term_new(TAG_CLO, func_idx, loc);
}

/* Clone a closure - shallow copy of the entire structure */
Term inet_clone_closure(INet* net, ThreadMem* tm, Term clo) {
    if (term_tag(clo) != TAG_CLO) return clo;  /* Not a closure, return as-is */

    uint16_t func_idx = term_aux(clo);
    Loc src_loc = term_loc(clo);

    /* Read arity and env_size */
    int64_t arity = inet_get_num(inet_get(net, src_loc));
    int64_t env_size = inet_get_num(inet_get(net, src_loc + 1));

    /* Allocate new closure */
    Loc dst_loc = inet_alloc(net, tm, 2 + (uint32_t)env_size);

    /* Copy all slots */
    inet_set(net, dst_loc, inet_num(arity));
    inet_set(net, dst_loc + 1, inet_num(env_size));
    for (int64_t i = 0; i < env_size; i++) {
        inet_set(net, dst_loc + 2 + i, inet_get(net, src_loc + 2 + i));
    }

    return term_new(TAG_CLO, func_idx, dst_loc);
}

/* Get a value from closure environment by index */
Term inet_closure_get_env(INet* net, Term clo, uint16_t idx) {
    if (term_tag(clo) != TAG_CLO) return term_new(TAG_ERA, 0, 0);
    Loc loc = term_loc(clo);
    /* Closure layout: [arity, env_size, env[0], env[1], ...] */
    return inet_get(net, loc + 2 + idx);
}

/* Apply one argument to a closure, returns new closure or result */
static Term apply_closure(INet* net, ThreadMem* tm, Term clo, Term arg) {
    uint16_t func_idx = term_aux(clo);
    Loc loc = term_loc(clo);

    int64_t arity = inet_get_num(inet_get(net, loc));
    int64_t env_size = inet_get_num(inet_get(net, loc + 1));

    if (arity <= 1) {
        /* Fully saturated - call the function */
        /* Build argument array: env + this arg */
        if (func_idx >= net->num_funcs || !net->funcs[func_idx].impl) {
            return term_new(TAG_ERA, 0, 0);
        }

        /* For now, pass the closure location as the "arg" -
         * the function can read env from there, and arg is the last element */
        /* Store arg at the end of env temporarily */
        Loc call_loc = inet_alloc(net, tm, 2 + (uint32_t)env_size + 1);
        inet_set(net, call_loc, inet_num(0));  /* arity = 0 */
        inet_set(net, call_loc + 1, inet_num(env_size + 1));
        for (int64_t i = 0; i < env_size; i++) {
            inet_set(net, call_loc + 2 + i, inet_get(net, loc + 2 + i));
        }
        inet_set(net, call_loc + 2 + env_size, arg);

        Term call_term = term_new(TAG_CLO, func_idx, call_loc);
        return net->funcs[func_idx].impl(net, tm, call_term);
    } else {
        /* Partial application - create new closure with arg added to env */
        Loc new_loc = inet_alloc(net, tm, 2 + (uint32_t)env_size + 1);
        inet_set(net, new_loc, inet_num(arity - 1));
        inet_set(net, new_loc + 1, inet_num(env_size + 1));
        for (int64_t i = 0; i < env_size; i++) {
            inet_set(net, new_loc + 2 + i, inet_get(net, loc + 2 + i));
        }
        inet_set(net, new_loc + 2 + env_size, arg);

        return term_new(TAG_CLO, func_idx, new_loc);
    }
}

/*============================================================================
 * Interaction Calculus Operations
 *
 * These implement the core interaction rules from the Interaction Calculus.
 *===========================================================================*/

/* Global label counter for fresh labels */
static _Atomic(uint32_t) g_label_counter = 1;

static inline Lab fresh_label(void) {
    return (Lab)atomic_fetch_add_explicit(&g_label_counter, 1, memory_order_relaxed);
}

Term inet_dup_with_projs(INet* net, ThreadMem* tm, Lab label, Term target,
                         Loc* out_proj0_slot, Loc* out_proj1_slot) {
    Loc loc = inet_alloc(net, tm, 3);
    inet_set(net, loc, target);
    inet_set(net, loc + 1, term_new(TAG_NIL, 0, 0));  /* proj0 slot */
    inet_set(net, loc + 2, term_new(TAG_NIL, 0, 0));  /* proj1 slot */

    if (out_proj0_slot) *out_proj0_slot = loc + 1;
    if (out_proj1_slot) *out_proj1_slot = loc + 2;

    return term_new(TAG_DUP, label, loc);
}

/*
 * DUP-SUP Interaction
 *
 * Case 1: Same label (annihilation)
 *   !{a b} &L = &L{x y}  =>  a = x, b = y
 *
 * Case 2: Different labels (commutation)
 *   !{a b} &L = &M{x y}  =>
 *     a = &M{x0 y0}, b = &M{x1 y1}
 *     where !{x0 x1} &L = x, !{y0 y1} &L = y
 *
 * For primitives (NUM, ERA) inside SUP, duplicate directly.
 */
void inet_interact_dup_sup(INet* net, ThreadMem* tm, Term dup, Term sup) {
    Lab dup_label = term_aux(dup);
    Lab sup_label = term_aux(sup);
    Loc dup_loc = term_loc(dup);
    Loc sup_loc = term_loc(sup);

    Term sup_left = inet_get(net, sup_loc);
    Term sup_right = inet_get(net, sup_loc + 1);

    Loc proj0_slot = dup_loc + 1;
    Loc proj1_slot = dup_loc + 2;

    if (dup_label == sup_label) {
        /* Annihilation: proj0 = left, proj1 = right */
        inet_subst(net, proj0_slot, sup_left);
        inet_subst(net, proj1_slot, sup_right);
    } else {
        /* Commutation: create nested structure */
        /*
         * We need:
         *   proj0 = &M{x0, y0}
         *   proj1 = &M{x1, y1}
         * Where:
         *   !{x0 x1} &L = sup_left
         *   !{y0 y1} &L = sup_right
         */

        Term x0, x1, y0, y1;
        Tag left_tag = term_tag(sup_left);
        Tag right_tag = term_tag(sup_right);

        /* Primitives can be duplicated directly */
        if (left_tag == TAG_NUM || left_tag == TAG_ERA) {
            x0 = sup_left;
            x1 = sup_left;
        } else {
            Loc x0_slot, x1_slot;
            inet_dup_with_projs(net, tm, dup_label, sup_left, &x0_slot, &x1_slot);
            x0 = term_new(TAG_NIL, 0, x0_slot);
            x1 = term_new(TAG_NIL, 0, x1_slot);
        }

        if (right_tag == TAG_NUM || right_tag == TAG_ERA) {
            y0 = sup_right;
            y1 = sup_right;
        } else {
            Loc y0_slot, y1_slot;
            inet_dup_with_projs(net, tm, dup_label, sup_right, &y0_slot, &y1_slot);
            y0 = term_new(TAG_NIL, 0, y0_slot);
            y1 = term_new(TAG_NIL, 0, y1_slot);
        }

        /* Create the two new SUPs with the original SUP's label */
        Term new_sup0 = inet_sup(net, tm, sup_label, x0, y0);
        Term new_sup1 = inet_sup(net, tm, sup_label, x1, y1);

        /* Write results to DUP's projection slots */
        inet_subst(net, proj0_slot, new_sup0);
        inet_subst(net, proj1_slot, new_sup1);
    }
}

/*
 * DUP-LAM Interaction
 *
 * !{a b} &L = λx.body  =>
 *   a = λx0.body0, b = λx1.body1
 *   where x = &L{x0 x1}, !{body0 body1} &L = body
 */
void inet_interact_dup_lam(INet* net, ThreadMem* tm, Term dup, Term lam) {
    Lab label = term_aux(dup);
    Loc dup_loc = term_loc(dup);
    Loc lam_loc = term_loc(lam);

    /* Read lambda structure */
    Term var_ptr = inet_get(net, lam_loc);      /* Contains var slot location */
    Loc orig_var_slot = term_loc(var_ptr);
    Term body = inet_get(net, lam_loc + 1);

    Loc proj0_slot = dup_loc + 1;
    Loc proj1_slot = dup_loc + 2;

    /* Create two fresh variable slots for x0 and x1 */
    Loc var0_slot = inet_alloc(net, tm, 1);
    Loc var1_slot = inet_alloc(net, tm, 1);
    inet_set(net, var0_slot, term_new(TAG_NIL, 0, 0));
    inet_set(net, var1_slot, term_new(TAG_NIL, 0, 0));

    /* Substitute original var with SUP{x0_ref, x1_ref} */
    Term x0_ref = term_new(TAG_NIL, 0, var0_slot);
    Term x1_ref = term_new(TAG_NIL, 0, var1_slot);
    Term var_sup = inet_sup(net, tm, label, x0_ref, x1_ref);
    inet_subst(net, orig_var_slot, var_sup);

    /* Create DUP for the body */
    Loc body0_slot, body1_slot;
    Term body_dup = inet_dup_with_projs(net, tm, label, body, &body0_slot, &body1_slot);
    (void)body_dup;

    /* Create the two new lambdas */
    /* λx0.body0 and λx1.body1 */
    Term body0_ref = term_new(TAG_NIL, 0, body0_slot);
    Term body1_ref = term_new(TAG_NIL, 0, body1_slot);

    Term lam0 = inet_lam(net, tm, var0_slot, body0_ref);
    Term lam1 = inet_lam(net, tm, var1_slot, body1_ref);

    /* Write results to DUP's projection slots */
    inet_subst(net, proj0_slot, lam0);
    inet_subst(net, proj1_slot, lam1);
}

/*
 * DUP-ERA Interaction
 *
 * !{a b} &L = *  =>  a = *, b = *
 */
void inet_interact_dup_era(INet* net, ThreadMem* tm, Term dup) {
    (void)tm;
    Loc dup_loc = term_loc(dup);

    Loc proj0_slot = dup_loc + 1;
    Loc proj1_slot = dup_loc + 2;

    Term era = term_new(TAG_ERA, 0, 0);
    inet_subst(net, proj0_slot, era);
    inet_subst(net, proj1_slot, era);
}

/*
 * DUP-NUM Interaction
 *
 * !{a b} &L = n  =>  a = n, b = n
 */
void inet_interact_dup_num(INet* net, ThreadMem* tm, Term dup, Term num) {
    (void)tm;
    Loc dup_loc = term_loc(dup);

    Loc proj0_slot = dup_loc + 1;
    Loc proj1_slot = dup_loc + 2;

    /* Numbers can be freely copied */
    inet_subst(net, proj0_slot, num);
    inet_subst(net, proj1_slot, num);
}

/*
 * APP-SUP Interaction
 *
 * (&L{f0 f1} arg)  =>  &L{(f0 arg0) (f1 arg1)}
 * where !{arg0 arg1} &L = arg
 *
 * If arg is a primitive (NUM, ERA), duplicate directly without DUP node.
 * This is a key optimization for numeric code like fib.
 */
Term inet_interact_app_sup(INet* net, ThreadMem* tm, Term sup_fun, Term arg, Lab sup_label) {
    Loc sup_loc = term_loc(sup_fun);
    Term f0 = inet_get(net, sup_loc);
    Term f1 = inet_get(net, sup_loc + 1);

    Term arg0, arg1;
    Tag arg_tag = term_tag(arg);

    /* Fast path: primitives can be duplicated directly without DUP nodes */
    if (__builtin_expect(arg_tag == TAG_NUM || arg_tag == TAG_ERA, 1)) {
        /* NUM and ERA can be freely copied */
        arg0 = arg;
        arg1 = arg;
    } else {
        /* Complex value: create lazy DUP */
        Loc arg0_slot, arg1_slot;
        inet_dup_with_projs(net, tm, sup_label, arg, &arg0_slot, &arg1_slot);
        arg0 = term_new(TAG_NIL, 0, arg0_slot);
        arg1 = term_new(TAG_NIL, 0, arg1_slot);
    }

    /* Create the two applications */
    Term app0 = inet_app(net, tm, f0, arg0);
    Term app1 = inet_app(net, tm, f1, arg1);

    /* Return SUP of the applications */
    return inet_sup(net, tm, sup_label, app0, app1);
}

/*
 * DUP-CLO Interaction
 *
 * Similar to DUP-LAM but handles closure environment.
 * Each captured variable in the env needs to be duplicated.
 * 
 * For primitive values (NUM), we copy them directly.
 * For complex values, we create lazy DUP references.
 */
void inet_interact_dup_clo(INet* net, ThreadMem* tm, Term dup, Term clo) {
    Lab label = term_aux(dup);
    Loc dup_loc = term_loc(dup);

    uint16_t func_idx = term_aux(clo);
    Loc clo_loc = term_loc(clo);

    int64_t arity = inet_get_num(inet_get(net, clo_loc));
    int64_t env_size = inet_get_num(inet_get(net, clo_loc + 1));

    Loc proj0_slot = dup_loc + 1;
    Loc proj1_slot = dup_loc + 2;

    /* For each env variable, duplicate it */
    /* Primitives (NUM) are copied directly; complex values use lazy DUP */

    /* Arrays to hold duplicated env values for each closure */
    Term env0_vals[64];  /* Max env size */
    Term env1_vals[64];

    for (int64_t i = 0; i < env_size && i < 64; i++) {
        Term env_val = inet_get(net, clo_loc + 2 + i);
        Tag env_tag = term_tag(env_val);
        
        if (env_tag == TAG_NUM) {
            /* Primitive: copy directly to both closures */
            env0_vals[i] = env_val;
            env1_vals[i] = env_val;
        } else if (env_tag == TAG_ERA) {
            /* Eraser: copy directly */
            env0_vals[i] = env_val;
            env1_vals[i] = env_val;
        } else {
            /* Complex value: create DUP with lazy references */
            Loc slot0, slot1;
            Term env_dup = inet_dup_with_projs(net, tm, label, env_val, &slot0, &slot1);
            (void)env_dup;
            /* Store references to DUP projection slots */
            env0_vals[i] = term_new(TAG_SUB, 0, slot0);
            env1_vals[i] = term_new(TAG_SUB, 0, slot1);
        }
    }

    /* Create closure 0 */
    Loc clo0_loc = inet_alloc(net, tm, 2 + (uint32_t)env_size);
    inet_set(net, clo0_loc, inet_num(arity));
    inet_set(net, clo0_loc + 1, inet_num(env_size));
    for (int64_t i = 0; i < env_size && i < 64; i++) {
        inet_set(net, clo0_loc + 2 + i, env0_vals[i]);
    }
    Term clo0 = term_new(TAG_CLO, func_idx, clo0_loc);

    /* Create closure 1 */
    Loc clo1_loc = inet_alloc(net, tm, 2 + (uint32_t)env_size);
    inet_set(net, clo1_loc, inet_num(arity));
    inet_set(net, clo1_loc + 1, inet_num(env_size));
    for (int64_t i = 0; i < env_size && i < 64; i++) {
        inet_set(net, clo1_loc + 2 + i, env1_vals[i]);
    }
    Term clo1 = term_new(TAG_CLO, func_idx, clo1_loc);

    /* Write results */
    inet_subst(net, proj0_slot, clo0);
    inet_subst(net, proj1_slot, clo1);
}

/*
 * Perform a DUP interaction based on the target's type
 */
static void perform_dup_interaction(INet* net, ThreadMem* tm, Term dup, Term target) {
    Tag target_tag = term_tag(target);

    switch (target_tag) {
        case TAG_SUP:
            inet_interact_dup_sup(net, tm, dup, target);
            break;
        case TAG_LAM:
            inet_interact_dup_lam(net, tm, dup, target);
            break;
        case TAG_CLO:
            inet_interact_dup_clo(net, tm, dup, target);
            break;
        case TAG_ERA:
            inet_interact_dup_era(net, tm, dup);
            break;
        case TAG_NUM:
            inet_interact_dup_num(net, tm, dup, target);
            break;
        default:
            /* Unknown target - treat as ERA */
            IDEBUG("DUP on unknown tag: %02x\n", target_tag);
            inet_interact_dup_era(net, tm, dup);
            break;
    }
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

static __attribute__((always_inline)) inline int64_t compute_op(Lab op, int64_t x, int64_t y) {
    /* Use a jump table for fast dispatch - compiler will optimize this */
    switch (op) {
        case OP_ADD: return x + y;
        case OP_SUB: return x - y;
        case OP_MUL: return x * y;
        case OP_DIV: return __builtin_expect(y != 0, 1) ? x / y : 0;
        case OP_MOD: return __builtin_expect(y != 0, 1) ? x % y : 0;
        case OP_EQ:  return x == y;
        case OP_NE:  return x != y;
        case OP_LT:  return x < y;
        case OP_GT:  return x > y;
        case OP_LE:  return x <= y;
        case OP_GE:  return x >= y;
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
 * reduce_term: Reduce a term to a value (NUM, ERA, LAM, CLO, or SUP)
 *
 * Returns the reduced term.
 * Handles all interaction calculus rules.
 *
 * Cached heap pointer to reduce indirection and inlined tag checks with unlikely/likely hints
 */
static __attribute__((hot)) Term reduce_term(INet* net, ThreadMem* tm, Term term) {
    Frame stack[MAX_STACK];
    int sp = 0;

    /* Cache heap pointer locally - reduces pointer chasing */
    ATerm* const __restrict__ heap = net->heap;

    for (;;) {
        /* Follow substitutions - use unlikely since most terms aren't subs */
        while (__builtin_expect(term_is_sub(term), 0)) {
            term = term_clr_sub(term);
        }

        const Tag tag = term_tag(term);

        /* Fast path: check if it's a value type (most common case) */
        /* Values are: NUM(0x13), ERA(0x14), LAM(0x10), CLO(0x11), SUP(0x15) */
        const int is_value = (tag == TAG_NUM) | (tag == TAG_ERA) | 
                             (tag == TAG_LAM) | (tag == TAG_CLO) | (tag == TAG_SUP);
        
        if (__builtin_expect(is_value, 1)) {
            /* It's a value - unwind stack or return */
            if (__builtin_expect(sp == 0, 0)) {
                return term;
            }

            while (sp > 0) {
                Frame* const f = &stack[--sp];

                if (f->op == TAG_OPR) {
                    if (f->state == 0) {
                        /* Got first operand, now need second */
                        if (__builtin_expect(tag == TAG_NUM, 1)) {
                            f->val = inet_get_num(term);
                            f->state = 1;

                            /* Get second operand directly from cached heap */
                            term = atomic_load_explicit(&heap[f->loc + 1], memory_order_relaxed);
                            while (__builtin_expect(term_is_sub(term), 0)) {
                                term = term_clr_sub(term);
                            }
                            sp++;  /* Keep frame on stack */
                            goto next_iter;  /* Continue reducing */
                        } else {
                            IDEBUG("OPR first arg not NUM: tag=%02x\n", tag);
                            term = term_new(TAG_ERA, 0, 0);
                        }
                    } else {
                        /* Got second operand, compute result */
                        if (__builtin_expect(tag == TAG_NUM, 1)) {
                            const int64_t result = compute_op(f->aux, f->val, inet_get_num(term));
                            term = inet_num(result);
                            tm->interactions++;
                        } else {
                            IDEBUG("OPR second arg not NUM: tag=%02x\n", tag);
                            term = term_new(TAG_ERA, 0, 0);
                        }
                    }
                } else if (f->op == TAG_DUP) {
                    /* DUP waiting for its target value */
                    const Term dup_term = term_new(TAG_DUP, f->aux, f->loc);
                    perform_dup_interaction(net, tm, dup_term, term);
                    tm->interactions++;

                    /* Read the projection we need directly */
                    const Loc proj_slot = f->loc + 1 + f->state;
                    term = atomic_load_explicit(&heap[proj_slot], memory_order_relaxed);
                }
            }

            if (sp == 0) {
                return term;
            }
            continue;
        }

        /* Handle non-value node types */
        switch (tag) {
            case TAG_OPR: {
                const Loc loc = term_loc(term);
                const Lab op = term_aux(term);

                /* Check if both operands are already NUMs */
                Term left = atomic_load_explicit(&heap[loc], memory_order_relaxed);
                Term right = atomic_load_explicit(&heap[loc + 1], memory_order_relaxed);
                
                /* Follow substitutions for both */
                while (__builtin_expect(term_is_sub(left), 0)) left = term_clr_sub(left);
                while (__builtin_expect(term_is_sub(right), 0)) right = term_clr_sub(right);

                /* Fast path: both are NUMs - compute immediately without stack */
                if (__builtin_expect(term_tag(left) == TAG_NUM && term_tag(right) == TAG_NUM, 1)) {
                    const int64_t result = compute_op(op, inet_get_num(left), inet_get_num(right));
                    term = inet_num(result);
                    tm->interactions++;
                    break;
                }

                if (__builtin_expect(sp >= MAX_STACK - 1, 0)) {
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
                term = left;
                break;
            }

            case TAG_REF: {
                const uint16_t func_idx = term_aux(term);
                const Loc loc = term_loc(term);

                if (__builtin_expect(func_idx >= net->num_funcs || !net->funcs[func_idx].impl, 0)) {
                    term = term_new(TAG_ERA, 0, 0);
                    break;
                }

                const Term arg = atomic_load_explicit(&heap[loc], memory_order_relaxed);
                term = net->funcs[func_idx].impl(net, tm, arg);
                tm->interactions++;
                break;
            }

            case TAG_APP: {
                const Loc loc = term_loc(term);
                Term fun = atomic_load_explicit(&heap[loc], memory_order_relaxed);
                const Term arg = atomic_load_explicit(&heap[loc + 1], memory_order_relaxed);

                /* Reduce function first */
                fun = reduce_term(net, tm, fun);
                const Tag fun_tag = term_tag(fun);

                if (fun_tag == TAG_LAM) {
                    const Loc lam_loc = term_loc(fun);
                    const Term var_ptr = atomic_load_explicit(&heap[lam_loc], memory_order_relaxed);
                    const Loc var_loc = term_loc(var_ptr);
                    const Term body = atomic_load_explicit(&heap[lam_loc + 1], memory_order_relaxed);

                    inet_subst(net, var_loc, arg);
                    term = body;
                    tm->interactions++;
                } else if (fun_tag == TAG_CLO) {
                    term = apply_closure(net, tm, fun, arg);
                    tm->interactions++;
                } else if (fun_tag == TAG_SUP) {
                    const Lab sup_label = term_aux(fun);
                    term = inet_interact_app_sup(net, tm, fun, arg, sup_label);
                    tm->interactions++;
                } else if (fun_tag == TAG_ERA) {
                    term = term_new(TAG_ERA, 0, 0);
                } else {
                    IDEBUG("APP to non-function: tag=%02x\n", fun_tag);
                    term = term_new(TAG_ERA, 0, 0);
                }
                break;
            }

            case TAG_DUP: {
                const Loc loc = term_loc(term);
                const Lab label = term_aux(term);
                Term target = atomic_load_explicit(&heap[loc], memory_order_relaxed);

                while (__builtin_expect(term_is_sub(target), 0)) {
                    target = term_clr_sub(target);
                }

                const Tag target_tag = term_tag(target);
                const int target_is_value = (target_tag == TAG_NUM) | (target_tag == TAG_ERA) |
                                            (target_tag == TAG_LAM) | (target_tag == TAG_CLO) | 
                                            (target_tag == TAG_SUP);
                
                if (__builtin_expect(target_is_value, 1)) {
                    perform_dup_interaction(net, tm, term, target);
                    tm->interactions++;
                    term = atomic_load_explicit(&heap[loc + 1], memory_order_relaxed);
                } else {
                    if (__builtin_expect(sp >= MAX_STACK - 1, 0)) {
                        fprintf(stderr, "Stack overflow in reduce_term (DUP)\n");
                        return inet_num(0);
                    }

                    stack[sp].op = TAG_DUP;
                    stack[sp].state = 0;
                    stack[sp].aux = label;
                    stack[sp].loc = loc;
                    stack[sp].out = 0;
                    sp++;

                    term = target;
                }
                break;
            }

            case TAG_LAM:
            case TAG_CLO:
            case TAG_SUP:
                return term;

            case TAG_NIL:
            case TAG_SUB: {
                const Loc loc = term_loc(term);
                term = atomic_load_explicit(&heap[loc], memory_order_relaxed);
                break;
            }

            default:
                IDEBUG("Unknown tag in reduce_term: %02x\n", tag);
                term = term_new(TAG_ERA, 0, 0);
                break;
        }
        next_iter:;
    }
}

/*
 * reduce_parallel: Reduce with work-stealing parallelism
 *
 * Similar to reduce_term but pushes right subtrees as redexes
 * that can be stolen by other threads.
 *
 * OPTIMIZATIONS:
 * - Only push parallel work for REF nodes (function calls) to reduce overhead
 * - Use cached heap pointer
 * - Branch prediction hints
 */
typedef struct {
    uint8_t  op;
    uint8_t  state;
    Lab      aux;
    Loc      loc;
    int64_t  val;
    Loc      result_slot;
} PFrame;

static __attribute__((hot)) Term reduce_parallel(INet* net, ThreadMem* tm, Term term, int depth) {
    PFrame stack[MAX_STACK];
    int sp = 0;

    /* Cache heap pointer */
    ATerm* const __restrict__ heap = net->heap;

    /* Only push parallel work at shallow depths to avoid overhead */
    const int PARALLEL_DEPTH = 3;

    for (;;) {
        while (__builtin_expect(term_is_sub(term), 0)) {
            term = term_clr_sub(term);
        }

        const Tag tag = term_tag(term);
        const int is_value = (tag == TAG_NUM) | (tag == TAG_ERA) | 
                             (tag == TAG_LAM) | (tag == TAG_CLO) | (tag == TAG_SUP);

        if (__builtin_expect(is_value, 1)) {
            if (__builtin_expect(sp == 0, 0)) {
                return term;
            }

            while (sp > 0) {
                PFrame* const f = &stack[--sp];

                if (f->op == TAG_OPR) {
                    if (f->state == 0) {
                        if (__builtin_expect(tag != TAG_NUM, 0)) {
                            IDEBUG("OPR first arg not NUM: tag=%02x\n", tag);
                            term = term_new(TAG_ERA, 0, 0);
                            continue;
                        }
                        f->val = inet_get_num(term);
                        f->state = 1;

                        if (f->result_slot != 0) {
                            /* Wait for parallel result - but help out */
                            Term slot_val = atomic_load_explicit(&heap[f->result_slot], memory_order_acquire);
                            int spins = 0;
                            while (!term_is_sub(slot_val)) {
                                Redex r;
                                if (inet_pop(net, tm, &r)) {
                                    Term res = reduce_parallel(net, tm, r.a, depth + 1);
                                    inet_subst(net, term_loc(r.b), res);
                                } else if (++spins > 64) {
                                    /* Avoid spinning too long */
                                    cpu_pause();
                                    spins = 0;
                                }
                                slot_val = atomic_load_explicit(&heap[f->result_slot], memory_order_acquire);
                            }
                            term = term_clr_sub(slot_val);
                            sp++;
                            goto next_iter;
                        } else {
                            term = atomic_load_explicit(&heap[f->loc + 1], memory_order_relaxed);
                            while (__builtin_expect(term_is_sub(term), 0)) {
                                term = term_clr_sub(term);
                            }
                            sp++;
                            goto next_iter;
                        }
                    } else {
                        if (__builtin_expect(tag != TAG_NUM, 0)) {
                            IDEBUG("OPR second arg not NUM: tag=%02x\n", tag);
                            term = term_new(TAG_ERA, 0, 0);
                            continue;
                        }
                        const int64_t result = compute_op(f->aux, f->val, inet_get_num(term));
                        term = inet_num(result);
                        tm->interactions++;
                    }
                } else if (f->op == TAG_DUP) {
                    const Term dup_term = term_new(TAG_DUP, f->aux, f->loc);
                    perform_dup_interaction(net, tm, dup_term, term);
                    tm->interactions++;

                    const Loc proj_slot = f->loc + 1 + f->state;
                    term = atomic_load_explicit(&heap[proj_slot], memory_order_relaxed);
                }
            }

            if (sp == 0) {
                return term;
            }
            continue;
        }

        switch (tag) {
            case TAG_OPR: {
                const Loc loc = term_loc(term);
                const Lab op = term_aux(term);

                /* Check if both operands are already NUMs */
                Term left = atomic_load_explicit(&heap[loc], memory_order_relaxed);
                Term right = atomic_load_explicit(&heap[loc + 1], memory_order_relaxed);
                
                while (__builtin_expect(term_is_sub(left), 0)) left = term_clr_sub(left);
                while (__builtin_expect(term_is_sub(right), 0)) right = term_clr_sub(right);

                /* Fast path: both are NUMs - compute immediately */
                if (__builtin_expect(term_tag(left) == TAG_NUM && term_tag(right) == TAG_NUM, 1)) {
                    const int64_t result = compute_op(op, inet_get_num(left), inet_get_num(right));
                    term = inet_num(result);
                    tm->interactions++;
                    break;
                }

                if (__builtin_expect(sp >= MAX_STACK - 1, 0)) {
                    fprintf(stderr, "Stack overflow\n");
                    return inet_num(0);
                }

                stack[sp].op = TAG_OPR;
                stack[sp].state = 0;
                stack[sp].aux = op;
                stack[sp].loc = loc;
                stack[sp].result_slot = 0;

                /* Only push parallel work for REF (function calls) at shallow depth */
                const Tag right_tag = term_tag(right);
                if (depth < PARALLEL_DEPTH && right_tag == TAG_REF) {
                    const Loc slot = inet_alloc(net, tm, 1);
                    atomic_store_explicit(&heap[slot], term_new(TAG_NIL, 0, 0), memory_order_relaxed);
                    stack[sp].result_slot = slot;
                    inet_push(net, tm, right, term_new(TAG_NIL, 0, slot));
                }

                sp++;
                term = left;
                depth++;
                break;
            }

            case TAG_REF: {
                const uint16_t func_idx = term_aux(term);
                const Loc loc = term_loc(term);

                if (__builtin_expect(func_idx >= net->num_funcs || !net->funcs[func_idx].impl, 0)) {
                    term = term_new(TAG_ERA, 0, 0);
                    break;
                }

                const Term arg = atomic_load_explicit(&heap[loc], memory_order_relaxed);
                term = net->funcs[func_idx].impl(net, tm, arg);
                tm->interactions++;
                break;
            }

            case TAG_APP: {
                const Loc loc = term_loc(term);
                Term fun = atomic_load_explicit(&heap[loc], memory_order_relaxed);
                const Term arg = atomic_load_explicit(&heap[loc + 1], memory_order_relaxed);

                fun = reduce_parallel(net, tm, fun, depth + 1);
                const Tag fun_tag = term_tag(fun);

                if (fun_tag == TAG_LAM) {
                    const Loc lam_loc = term_loc(fun);
                    const Term var_ptr = atomic_load_explicit(&heap[lam_loc], memory_order_relaxed);
                    const Loc var_loc = term_loc(var_ptr);
                    const Term body = atomic_load_explicit(&heap[lam_loc + 1], memory_order_relaxed);

                    inet_subst(net, var_loc, arg);
                    term = body;
                    tm->interactions++;
                } else if (fun_tag == TAG_CLO) {
                    term = apply_closure(net, tm, fun, arg);
                    tm->interactions++;
                } else if (fun_tag == TAG_SUP) {
                    const Lab sup_label = term_aux(fun);
                    term = inet_interact_app_sup(net, tm, fun, arg, sup_label);
                    tm->interactions++;
                } else if (fun_tag == TAG_ERA) {
                    term = term_new(TAG_ERA, 0, 0);
                } else {
                    IDEBUG("APP to non-function: tag=%02x\n", fun_tag);
                    term = term_new(TAG_ERA, 0, 0);
                }
                break;
            }

            case TAG_DUP: {
                const Loc loc = term_loc(term);
                const Lab label = term_aux(term);
                Term target = atomic_load_explicit(&heap[loc], memory_order_relaxed);

                while (__builtin_expect(term_is_sub(target), 0)) {
                    target = term_clr_sub(target);
                }

                const Tag target_tag = term_tag(target);
                const int target_is_value = (target_tag == TAG_NUM) | (target_tag == TAG_ERA) |
                                            (target_tag == TAG_LAM) | (target_tag == TAG_CLO) | 
                                            (target_tag == TAG_SUP);

                if (__builtin_expect(target_is_value, 1)) {
                    perform_dup_interaction(net, tm, term, target);
                    tm->interactions++;
                    term = atomic_load_explicit(&heap[loc + 1], memory_order_relaxed);
                } else {
                    if (__builtin_expect(sp >= MAX_STACK - 1, 0)) {
                        fprintf(stderr, "Stack overflow in reduce_parallel (DUP)\n");
                        return inet_num(0);
                    }

                    stack[sp].op = TAG_DUP;
                    stack[sp].state = 0;
                    stack[sp].aux = label;
                    stack[sp].loc = loc;
                    stack[sp].result_slot = 0;
                    sp++;

                    term = target;
                }
                break;
            }

            case TAG_LAM:
            case TAG_CLO:
            case TAG_SUP:
                return term;

            case TAG_NIL:
            case TAG_SUB: {
                const Loc loc = term_loc(term);
                term = atomic_load_explicit(&heap[loc], memory_order_relaxed);
                break;
            }

            default:
                IDEBUG("Unknown tag: %02x\n", tag);
                term = term_new(TAG_ERA, 0, 0);
                break;
        }
        next_iter:;
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
    const int num_threads = wa->num_threads;

    uint32_t idle_spins = 0;
    const uint32_t MAX_IDLE_SPINS = 256;  /* Reduced for faster termination detection */
    const uint32_t PAUSE_SPINS = 32;      /* Use pause instruction instead of busy loop */

    while (__builtin_expect(!atomic_load_explicit(&net->done, memory_order_relaxed), 1)) {
        Redex r;

        /* Try local pop first - most likely to succeed */
        if (__builtin_expect(inet_pop(net, tm, &r), 1)) {
            const Term result = reduce_parallel(net, tm, r.a, 0);
            if (term_tag(r.b) == TAG_NIL) {
                inet_subst(net, term_loc(r.b), result);
            }
            idle_spins = 0;
            continue;
        }

        /* Try stealing from other threads */
        bool stolen = false;
        /* Start from a random offset to avoid contention */
        const int start = (tm->tid + 1) % num_threads;
        for (int i = 0; i < num_threads - 1 && !stolen; i++) {
            const int victim_id = (start + i) % num_threads;
            if (victim_id == (int)tm->tid) continue;
            
            ThreadMem* const victim = net->threads[victim_id];
            if (inet_steal(net, tm, victim, &r)) {
                tm->steals++;
                const Term result = reduce_parallel(net, tm, r.a, 0);
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

            if (__builtin_expect(idle_spins > MAX_IDLE_SPINS, 0)) {
                atomic_fetch_add_explicit(&net->idle_count, 1, memory_order_release);

                /* Wait for work or termination */
                while (!atomic_load_explicit(&net->done, memory_order_acquire)) {
                    bool any_work = false;
                    for (int i = 0; i < num_threads && !any_work; i++) {
                        if (deque_size(net->threads[i]) > 0) {
                            any_work = true;
                        }
                    }

                    if (any_work) {
                        atomic_fetch_sub_explicit(&net->idle_count, 1, memory_order_release);
                        break;
                    }

                    const uint32_t idle = atomic_load_explicit(&net->idle_count, memory_order_acquire);
                    if (idle >= (uint32_t)num_threads) {
                        atomic_store_explicit(&net->done, 1, memory_order_release);
                        break;
                    }

                    sched_yield();
                }

                idle_spins = 0;
            } else if (idle_spins > PAUSE_SPINS) {
                /* Use CPU pause instruction for light spinning */
                for (int i = 0; i < 8; i++) {
                    cpu_pause();
                }
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

/*============================================================================
 * Non-inline Wrappers for LLVM Codegen
 *
 * These functions provide external linkage for inline functions defined
 * in soma_inet.h, so LLVM-generated code can call them.
 *===========================================================================*/

Term inet_num_ext(int64_t n) {
    return inet_num(n);
}

int64_t inet_get_num_ext(Term t) {
    return inet_get_num(t);
}

/*============================================================================
 * Global Runtime State (for compiled programs)
 *
 * These globals are referenced by LLVM-generated code.
 *===========================================================================*/

INet* g_inet = NULL;
ThreadMem* g_inet_tm = NULL;

/*============================================================================
 * Initialization helper for LLVM codegen
 *
 * Initializes the runtime and sets both g_inet and g_inet_tm globals.
 *===========================================================================*/

void inet_init_globals(int num_threads) {
    g_inet = inet_init(num_threads);
    if (g_inet) {
        g_inet_tm = g_inet->threads[0];
    }
}

/*============================================================================
 * Main Entry Point
 *
 * Compiled Soma programs define `soma_main()` which returns an Int.
 * This main() initializes the runtime, calls soma_main, prints result.
 *===========================================================================*/

#ifndef SOMA_NO_MAIN
/* Forward declaration of compiled soma_main */
extern int32_t soma_main(void);

int main(int argc, char** argv) {
    (void)argc;
    (void)argv;

    /* Get number of threads from SOMA_WORKERS env var, default to 1 */
    int num_threads = 1;
    const char* workers_env = getenv("SOMA_WORKERS");
    if (workers_env) {
        int n = atoi(workers_env);
        if (n > 0 && n <= INET_MAX_THREADS) {
            num_threads = n;
        } else if (n > INET_MAX_THREADS) {
            fprintf(stderr, "Warning: SOMA_WORKERS=%d exceeds max %d, using %d\n",
                    n, INET_MAX_THREADS, INET_MAX_THREADS);
            num_threads = INET_MAX_THREADS;
        }
    }

    /* Initialize runtime */
    g_inet = inet_init(num_threads);
    if (!g_inet) {
        fprintf(stderr, "Failed to initialize INET runtime\n");
        return 1;
    }

    /* Set main thread's ThreadMem */
    g_inet_tm = g_inet->threads[0];

    /* Call the compiled program */
    int32_t result = soma_main();

    /* Cleanup */
    inet_free(g_inet);
    g_inet = NULL;
    g_inet_tm = NULL;

    return result;
}
#endif /* SOMA_NO_MAIN */
