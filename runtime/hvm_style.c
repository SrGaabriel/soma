/*
 * HVM-Style Parallel Reduction
 * 
 * Key insight from HVM2/HVM3 papers:
 * 1. Each thread has LOCAL redex bag - no shared worklist
 * 2. Work stealing only when local bag empty
 * 3. Interactions are purely LOCAL - touch only 2 nodes
 * 4. No parent pointers needed for strict CBV evaluation
 * 
 * For fib-like computations:
 * - fib(N) creates ADD(CALL(fib, N-1), CALL(fib, N-2))
 * - Each CALL is completely independent
 * - Workers can reduce entire subtrees without ANY synchronization
 */

#include "soma_graph.h"
#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <stdatomic.h>
#include <time.h>

/* Per-worker state */
typedef struct {
    GraphRuntime* rt;
    int worker_id;
    int num_workers;
    
    /* Local work - no atomics needed! */
    uint32_t* local_stack;
    int stack_top;
    int stack_capacity;
    
    /* Stats */
    uint64_t reductions;
    uint64_t steals;
} HVMWorker;

/* Global state for work stealing */
static _Atomic uint32_t* g_steal_slots;  /* One slot per worker for stealing */
static atomic_int g_done;
static uint32_t g_root;

/* Simple recursive fib for building graph */
uint32_t graph_fib(GraphRuntime* rt, int64_t n) {
    if (n < 2) return soma_graph_num(rt, n);
    uint32_t n1 = soma_graph_num(rt, n - 1);
    uint32_t n2 = soma_graph_num(rt, n - 2);
    uint32_t c1 = soma_graph_call1(rt, 0, n1);
    uint32_t c2 = soma_graph_call1(rt, 0, n2);
    return soma_graph_add(rt, c1, c2);
}

/* Check if node is reducible (CBV: all args must be values) */
static inline int is_reducible_local(GraphRuntime* rt, uint32_t idx) {
    if (idx == GIDX_NULL || idx >= rt->next_alloc) return 0;
    GNode* n = &rt->nodes[idx];
    
    switch (n->tag) {
        case GTAG_ADD: case GTAG_SUB: case GTAG_MUL: {
            uint32_t l = n->data.pair.l;
            uint32_t r = n->data.pair.r;
            /* Follow INDs */
            while (l < rt->next_alloc && rt->nodes[l].tag == GTAG_IND)
                l = rt->nodes[l].data.pair.l;
            while (r < rt->next_alloc && rt->nodes[r].tag == GTAG_IND)
                r = rt->nodes[r].data.pair.l;
            return (l < rt->next_alloc && rt->nodes[l].tag == GTAG_NUM) &&
                   (r < rt->next_alloc && rt->nodes[r].tag == GTAG_NUM);
        }
        case GTAG_CALL: {
            int arity = n->data.call.arity;
            for (int i = 0; i < arity; i++) {
                uint32_t arg = (arity == 1) ? n->data.call.args : rt->arg_pool[n->data.call.args + i];
                while (arg < rt->next_alloc && rt->nodes[arg].tag == GTAG_IND)
                    arg = rt->nodes[arg].data.pair.l;
                if (arg >= rt->next_alloc || rt->nodes[arg].tag != GTAG_NUM)
                    return 0;
            }
            return 1;
        }
        default:
            return 0;
    }
}

/* Reduce a single node - returns new node to process (or GIDX_NULL) */
static uint32_t reduce_one(GraphRuntime* rt, uint32_t idx, uint64_t* reductions) {
    if (idx == GIDX_NULL || idx >= rt->next_alloc) return GIDX_NULL;
    
    GNode* n = &rt->nodes[idx];
    
    /* Follow IND */
    while (n->tag == GTAG_IND) {
        idx = n->data.pair.l;
        if (idx == GIDX_NULL || idx >= rt->next_alloc) return GIDX_NULL;
        n = &rt->nodes[idx];
    }
    
    /* Already value? */
    if (n->tag == GTAG_NUM || n->tag == GTAG_ERA) return GIDX_NULL;
    
    switch (n->tag) {
        case GTAG_ADD: case GTAG_SUB: case GTAG_MUL: {
            uint32_t l = n->data.pair.l;
            uint32_t r = n->data.pair.r;
            while (l < rt->next_alloc && rt->nodes[l].tag == GTAG_IND)
                l = rt->nodes[l].data.pair.l;
            while (r < rt->next_alloc && rt->nodes[r].tag == GTAG_IND)
                r = rt->nodes[r].data.pair.l;
            
            if (rt->nodes[l].tag == GTAG_NUM && rt->nodes[r].tag == GTAG_NUM) {
                int64_t lv = rt->nodes[l].data.num;
                int64_t rv = rt->nodes[r].data.num;
                int64_t result;
                switch (n->tag) {
                    case GTAG_ADD: result = lv + rv; break;
                    case GTAG_SUB: result = lv - rv; break;
                    case GTAG_MUL: result = lv * rv; break;
                    default: result = 0;
                }
                n->tag = GTAG_NUM;
                n->data.num = result;
                (*reductions)++;
                return GIDX_NULL;  /* Now a value */
            }
            return idx;  /* Not yet reducible */
        }
        
        case GTAG_CALL: {
            int arity = n->data.call.arity;
            int64_t args[4];
            int ready = 1;
            
            for (int i = 0; i < arity && i < 4; i++) {
                uint32_t arg = (arity == 1) ? n->data.call.args : rt->arg_pool[n->data.call.args + i];
                while (arg < rt->next_alloc && rt->nodes[arg].tag == GTAG_IND)
                    arg = rt->nodes[arg].data.pair.l;
                if (arg >= rt->next_alloc || rt->nodes[arg].tag != GTAG_NUM) {
                    ready = 0;
                    break;
                }
                args[i] = rt->nodes[arg].data.num;
            }
            
            if (ready) {
                GFunc* fn = &rt->functions[n->data.call.fn];
                uint32_t result;
                if (arity == 1) {
                    typedef uint32_t (*Fn1)(GraphRuntime*, int64_t);
                    result = ((Fn1)fn->impl)(rt, args[0]);
                } else if (arity == 2) {
                    typedef uint32_t (*Fn2)(GraphRuntime*, int64_t, int64_t);
                    result = ((Fn2)fn->impl)(rt, args[0], args[1]);
                } else {
                    result = GIDX_NULL;
                }
                n->tag = GTAG_IND;
                n->data.pair.l = result;
                (*reductions)++;
                return result;  /* Process the new subgraph */
            }
            return idx;
        }
        
        default:
            return GIDX_NULL;
    }
}

/* Fully reduce a subtree to a value - NO SYNCHRONIZATION */
static void reduce_subtree(HVMWorker* w, uint32_t root) {
    GraphRuntime* rt = w->rt;
    
    w->local_stack[0] = root;
    w->stack_top = 1;
    
    while (w->stack_top > 0) {
        uint32_t idx = w->local_stack[--w->stack_top];
        
        if (idx == GIDX_NULL || idx >= rt->next_alloc) continue;
        
        /* Follow IND */
        GNode* n = &rt->nodes[idx];
        while (n->tag == GTAG_IND) {
            idx = n->data.pair.l;
            if (idx == GIDX_NULL || idx >= rt->next_alloc) goto next_iter;
            n = &rt->nodes[idx];
        }
        
        /* Value? Done. */
        if (n->tag == GTAG_NUM || n->tag == GTAG_ERA) continue;
        
        /* Try to reduce */
        uint32_t result = reduce_one(rt, idx, &w->reductions);
        
        if (result != GIDX_NULL && result != idx) {
            /* Reduced to new subgraph - process it */
            if (w->stack_top < w->stack_capacity - 1)
                w->local_stack[w->stack_top++] = result;
            continue;
        }
        
        /* Not reducible yet - push children */
        if (n->tag == GTAG_ADD || n->tag == GTAG_SUB || n->tag == GTAG_MUL) {
            if (w->stack_top < w->stack_capacity - 3) {
                w->local_stack[w->stack_top++] = idx;  /* Re-check later */
                w->local_stack[w->stack_top++] = n->data.pair.l;
                w->local_stack[w->stack_top++] = n->data.pair.r;
            }
        } else if (n->tag == GTAG_CALL) {
            int arity = n->data.call.arity;
            if (w->stack_top < w->stack_capacity - arity - 1) {
                w->local_stack[w->stack_top++] = idx;
                for (int i = 0; i < arity; i++) {
                    uint32_t arg = (arity == 1) ? n->data.call.args : rt->arg_pool[n->data.call.args + i];
                    w->local_stack[w->stack_top++] = arg;
                }
            }
        }
        
        next_iter:;
    }
}

/* Worker thread */
static void* hvm_worker(void* arg) {
    HVMWorker* w = (HVMWorker*)arg;
    
    while (!atomic_load(&g_done)) {
        /* Try to get work from our steal slot */
        uint32_t task = atomic_exchange(&g_steal_slots[w->worker_id], GIDX_NULL);
        
        if (task != GIDX_NULL) {
            w->steals++;
            reduce_subtree(w, task);
            continue;
        }
        
        /* Try stealing from other workers (round-robin) */
        int found = 0;
        for (int i = 1; i < w->num_workers && !found; i++) {
            int victim = (w->worker_id + i) % w->num_workers;
            task = atomic_exchange(&g_steal_slots[victim], GIDX_NULL);
            if (task != GIDX_NULL) {
                w->steals++;
                reduce_subtree(w, task);
                found = 1;
            }
        }
        
        if (!found) {
            /* No work - check if done */
            uint32_t root = g_root;
            while (root < w->rt->next_alloc && w->rt->nodes[root].tag == GTAG_IND)
                root = w->rt->nodes[root].data.pair.l;
            if (root < w->rt->next_alloc && w->rt->nodes[root].tag == GTAG_NUM) {
                atomic_store(&g_done, 1);
                break;
            }
            
            /* Yield */
            sched_yield();
        }
    }
    
    return NULL;
}

/* Build balanced tree of fib calls */
static uint32_t build_fib_tree(GraphRuntime* rt, int fib_n, int count) {
    if (count <= 0) return soma_graph_num(rt, 0);
    if (count == 1) {
        uint32_t arg = soma_graph_num(rt, fib_n);
        return soma_graph_call1(rt, 0, arg);
    }
    int mid = count / 2;
    uint32_t left = build_fib_tree(rt, fib_n, mid);
    uint32_t right = build_fib_tree(rt, fib_n, count - mid);
    return soma_graph_add(rt, left, right);
}

/* Find all CALL nodes and distribute to workers */
static int seed_calls(GraphRuntime* rt, uint32_t root, uint32_t* calls, int max_calls) {
    uint32_t stack[256];
    int stack_top = 0;
    int call_count = 0;
    
    stack[stack_top++] = root;
    
    while (stack_top > 0 && call_count < max_calls) {
        uint32_t idx = stack[--stack_top];
        if (idx == GIDX_NULL || idx >= rt->next_alloc) continue;
        
        GNode* n = &rt->nodes[idx];
        
        if (n->tag == GTAG_CALL) {
            calls[call_count++] = idx;
        } else if (n->tag == GTAG_ADD || n->tag == GTAG_SUB || n->tag == GTAG_MUL) {
            if (stack_top < 254) {
                stack[stack_top++] = n->data.pair.l;
                stack[stack_top++] = n->data.pair.r;
            }
        }
    }
    
    return call_count;
}

int main(int argc, char** argv) {
    int fib_n = 25;
    int count = 8;
    int num_workers = 4;
    
    if (argc > 1) fib_n = atoi(argv[1]);
    if (argc > 2) count = atoi(argv[2]);
    if (argc > 3) num_workers = atoi(argv[3]);
    
    printf("HVM-Style Parallel: %d × fib(%d) with %d workers\n\n", count, fib_n, num_workers);
    
    /* Single-threaded baseline */
    GraphRuntime* rt1 = soma_graph_init(0);
    soma_graph_register_func(rt1, "fib", 1, 0, (void*)graph_fib);
    uint32_t root1 = build_fib_tree(rt1, fib_n, count);
    
    struct timespec start, end;
    clock_gettime(CLOCK_MONOTONIC, &start);
    int64_t result1 = soma_graph_reduce_fast(rt1, root1);
    clock_gettime(CLOCK_MONOTONIC, &end);
    double single_time = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
    
    printf("Single-threaded: %.4fs, result=%ld\n", single_time, result1);
    soma_graph_shutdown(rt1);
    
    /* HVM-style parallel */
    GraphRuntime* rt = soma_graph_init(0);  /* 0 workers - we manage our own */
    soma_graph_register_func(rt, "fib", 1, 0, (void*)graph_fib);
    uint32_t root = build_fib_tree(rt, fib_n, count);
    g_root = root;
    
    /* Find all top-level CALL nodes */
    uint32_t calls[256];
    int num_calls = seed_calls(rt, root, calls, 256);
    printf("Found %d top-level CALL nodes\n", num_calls);
    
    /* Initialize steal slots */
    g_steal_slots = calloc(num_workers, sizeof(_Atomic uint32_t));
    for (int i = 0; i < num_workers; i++) {
        atomic_store(&g_steal_slots[i], GIDX_NULL);
    }
    atomic_store(&g_done, 0);
    
    /* Distribute calls to workers */
    for (int i = 0; i < num_calls; i++) {
        int worker = i % num_workers;
        /* If slot is empty, put work there; otherwise add to first empty slot */
        if (atomic_load(&g_steal_slots[worker]) == GIDX_NULL) {
            atomic_store(&g_steal_slots[worker], calls[i]);
        } else {
            for (int j = 0; j < num_workers; j++) {
                if (atomic_load(&g_steal_slots[j]) == GIDX_NULL) {
                    atomic_store(&g_steal_slots[j], calls[i]);
                    break;
                }
            }
        }
    }
    
    /* Create workers */
    HVMWorker* workers = calloc(num_workers, sizeof(HVMWorker));
    pthread_t* threads = calloc(num_workers, sizeof(pthread_t));
    
    for (int i = 0; i < num_workers; i++) {
        workers[i].rt = rt;
        workers[i].worker_id = i;
        workers[i].num_workers = num_workers;
        workers[i].stack_capacity = 65536;
        workers[i].local_stack = malloc(workers[i].stack_capacity * sizeof(uint32_t));
        workers[i].stack_top = 0;
        workers[i].reductions = 0;
        workers[i].steals = 0;
    }
    
    clock_gettime(CLOCK_MONOTONIC, &start);
    
    /* Start workers */
    for (int i = 1; i < num_workers; i++) {
        pthread_create(&threads[i], NULL, hvm_worker, &workers[i]);
    }
    hvm_worker(&workers[0]);
    
    /* Wait for completion */
    for (int i = 1; i < num_workers; i++) {
        pthread_join(threads[i], NULL);
    }
    
    clock_gettime(CLOCK_MONOTONIC, &end);
    double par_time = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
    
    /* Get result */
    uint32_t final = root;
    while (final < rt->next_alloc && rt->nodes[final].tag == GTAG_IND)
        final = rt->nodes[final].data.pair.l;
    int64_t result = (final < rt->next_alloc && rt->nodes[final].tag == GTAG_NUM) 
                     ? rt->nodes[final].data.num : -1;
    
    /* Need to reduce the ADD tree at the end */
    if (result == -1) {
        /* Workers reduced the CALLs, but not the ADDs at the top */
        result = soma_graph_reduce_fast(rt, root);
        clock_gettime(CLOCK_MONOTONIC, &end);
        par_time = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
    }
    
    printf("Parallel (%d workers): %.4fs, result=%ld\n", num_workers, par_time, result);
    printf("Speedup: %.2fx\n", single_time / par_time);
    
    printf("\nPer-worker stats:\n");
    uint64_t total_red = 0, total_steal = 0;
    for (int i = 0; i < num_workers; i++) {
        printf("  Worker %d: %lu reductions, %lu steals\n", 
               i, workers[i].reductions, workers[i].steals);
        total_red += workers[i].reductions;
        total_steal += workers[i].steals;
    }
    printf("  Total: %lu reductions, %lu steals\n", total_red, total_steal);
    
    /* Cleanup */
    for (int i = 0; i < num_workers; i++) {
        free(workers[i].local_stack);
    }
    free(workers);
    free(threads);
    free(g_steal_slots);
    soma_graph_shutdown(rt);
    
    return 0;
}
