/*
 * HVM-Style Parallel Reduction - Simplified
 * 
 * Key insight: For strict CBV fib-like code, once we have independent CALL nodes,
 * each can be reduced completely independently. No synchronization needed during
 * reduction - only at the start (distribute work) and end (combine results).
 */

#include "soma_graph.h"
#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <stdatomic.h>
#include <time.h>

/* Work queue - simple lock-free MPMC */
#define QUEUE_SIZE 1024
static uint32_t g_queue[QUEUE_SIZE];
static atomic_uint g_queue_head;
static atomic_uint g_queue_tail;
static atomic_int g_done;

static inline void queue_push(uint32_t val) {
    uint32_t tail = atomic_fetch_add(&g_queue_tail, 1) % QUEUE_SIZE;
    g_queue[tail] = val;
}

static inline uint32_t queue_pop(void) {
    uint32_t head = atomic_load(&g_queue_head);
    uint32_t tail = atomic_load(&g_queue_tail);
    if (head >= tail) return GIDX_NULL;
    
    uint32_t old_head = atomic_fetch_add(&g_queue_head, 1);
    if (old_head >= tail) return GIDX_NULL;
    
    return g_queue[old_head % QUEUE_SIZE];
}

/* Per-worker state */
typedef struct {
    GraphRuntime* rt;
    int worker_id;
    uint64_t reductions;
    uint64_t tasks;
} Worker;

/* Simple recursive fib for building graph */
uint32_t graph_fib(GraphRuntime* rt, int64_t n) {
    if (n < 2) return soma_graph_num(rt, n);
    uint32_t n1 = soma_graph_num(rt, n - 1);
    uint32_t n2 = soma_graph_num(rt, n - 2);
    uint32_t c1 = soma_graph_call1(rt, 0, n1);
    uint32_t c2 = soma_graph_call1(rt, 0, n2);
    return soma_graph_add(rt, c1, c2);
}

/* Reduce a subtree completely - no synchronization */
static void reduce_local(Worker* w, uint32_t root) {
    GraphRuntime* rt = w->rt;
    uint32_t stack[8192];
    int top = 0;
    
    stack[top++] = root;
    
    while (top > 0) {
        uint32_t idx = stack[--top];
        
        if (idx == GIDX_NULL || idx >= rt->next_alloc) continue;
        
        GNode* n = &rt->nodes[idx];
        
        /* Follow IND */
        while (n->tag == GTAG_IND) {
            idx = n->data.pair.l;
            if (idx == GIDX_NULL || idx >= rt->next_alloc) goto next;
            n = &rt->nodes[idx];
        }
        
        /* Value? Done */
        if (n->tag == GTAG_NUM || n->tag == GTAG_ERA) continue;
        
        /* Binary op - check if reducible */
        if (n->tag == GTAG_ADD || n->tag == GTAG_SUB || n->tag == GTAG_MUL) {
            uint32_t l = n->data.pair.l;
            uint32_t r = n->data.pair.r;
            
            /* Follow INDs */
            while (l < rt->next_alloc && rt->nodes[l].tag == GTAG_IND)
                l = rt->nodes[l].data.pair.l;
            while (r < rt->next_alloc && rt->nodes[r].tag == GTAG_IND)
                r = rt->nodes[r].data.pair.l;
            
            if (l < rt->next_alloc && rt->nodes[l].tag == GTAG_NUM &&
                r < rt->next_alloc && rt->nodes[r].tag == GTAG_NUM) {
                /* Reduce! */
                int64_t lv = rt->nodes[l].data.num;
                int64_t rv = rt->nodes[r].data.num;
                int64_t res = (n->tag == GTAG_ADD) ? lv + rv :
                              (n->tag == GTAG_SUB) ? lv - rv : lv * rv;
                n->tag = GTAG_NUM;
                n->data.num = res;
                w->reductions++;
            } else {
                /* Not ready - push children then self */
                if (top < 8189) {
                    stack[top++] = idx;
                    stack[top++] = n->data.pair.l;
                    stack[top++] = n->data.pair.r;
                }
            }
            continue;
        }
        
        /* CALL - check if reducible */
        if (n->tag == GTAG_CALL) {
            int arity = n->data.call.arity;
            int64_t args[4];
            int ready = 1;
            
            for (int i = 0; i < arity && i < 4; i++) {
                uint32_t arg = (arity == 1) ? n->data.call.args 
                             : rt->arg_pool[n->data.call.args + i];
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
                } else {
                    typedef uint32_t (*Fn2)(GraphRuntime*, int64_t, int64_t);
                    result = ((Fn2)fn->impl)(rt, args[0], args[1]);
                }
                n->tag = GTAG_IND;
                n->data.pair.l = result;
                w->reductions++;
                
                /* Process result */
                if (top < 8191) stack[top++] = result;
            } else {
                /* Not ready - push args then self */
                if (top < 8190 - arity) {
                    stack[top++] = idx;
                    for (int i = 0; i < arity; i++) {
                        uint32_t arg = (arity == 1) ? n->data.call.args 
                                     : rt->arg_pool[n->data.call.args + i];
                        stack[top++] = arg;
                    }
                }
            }
        }
        
        next:;
    }
}

static void* worker_thread(void* arg) {
    Worker* w = (Worker*)arg;
    
    while (!atomic_load(&g_done)) {
        uint32_t task = queue_pop();
        if (task != GIDX_NULL) {
            w->tasks++;
            reduce_local(w, task);
        } else {
            /* No more work - signal done */
            atomic_store(&g_done, 1);
            break;
        }
    }
    
    return NULL;
}

/* Build balanced tree */
static uint32_t build_tree(GraphRuntime* rt, int fib_n, int count) {
    if (count <= 0) return soma_graph_num(rt, 0);
    if (count == 1) {
        uint32_t arg = soma_graph_num(rt, fib_n);
        return soma_graph_call1(rt, 0, arg);
    }
    int mid = count / 2;
    uint32_t l = build_tree(rt, fib_n, mid);
    uint32_t r = build_tree(rt, fib_n, count - mid);
    return soma_graph_add(rt, l, r);
}

/* Find all CALL nodes */
static int find_calls(GraphRuntime* rt, uint32_t root, uint32_t* calls, int max) {
    uint32_t stack[256];
    int top = 0, count = 0;
    stack[top++] = root;
    
    while (top > 0 && count < max) {
        uint32_t idx = stack[--top];
        if (idx == GIDX_NULL || idx >= rt->next_alloc) continue;
        GNode* n = &rt->nodes[idx];
        
        if (n->tag == GTAG_CALL) {
            calls[count++] = idx;
        } else if (n->tag == GTAG_ADD || n->tag == GTAG_SUB || n->tag == GTAG_MUL) {
            if (top < 254) {
                stack[top++] = n->data.pair.l;
                stack[top++] = n->data.pair.r;
            }
        }
    }
    return count;
}

int main(int argc, char** argv) {
    int fib_n = 25, count = 8, nworkers = 4;
    if (argc > 1) fib_n = atoi(argv[1]);
    if (argc > 2) count = atoi(argv[2]);
    if (argc > 3) nworkers = atoi(argv[3]);
    
    printf("HVM-Style: %d × fib(%d), %d workers\n\n", count, fib_n, nworkers);
    
    /* Baseline */
    GraphRuntime* rt1 = soma_graph_init(0);
    soma_graph_register_func(rt1, "fib", 1, 0, (void*)graph_fib);
    uint32_t root1 = build_tree(rt1, fib_n, count);
    
    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);
    int64_t res1 = soma_graph_reduce_fast(rt1, root1);
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double base = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) / 1e9;
    printf("Single: %.4fs, result=%ld\n", base, res1);
    soma_graph_shutdown(rt1);
    
    /* Parallel */
    GraphRuntime* rt = soma_graph_init(0);
    soma_graph_register_func(rt, "fib", 1, 0, (void*)graph_fib);
    uint32_t root = build_tree(rt, fib_n, count);
    
    /* Find CALL nodes and queue them */
    uint32_t calls[256];
    int ncalls = find_calls(rt, root, calls, 256);
    printf("Found %d CALL nodes\n", ncalls);
    
    atomic_store(&g_queue_head, 0);
    atomic_store(&g_queue_tail, 0);
    atomic_store(&g_done, 0);
    
    for (int i = 0; i < ncalls; i++) {
        queue_push(calls[i]);
    }
    
    Worker* workers = calloc(nworkers, sizeof(Worker));
    pthread_t* threads = calloc(nworkers, sizeof(pthread_t));
    
    for (int i = 0; i < nworkers; i++) {
        workers[i].rt = rt;
        workers[i].worker_id = i;
    }
    
    clock_gettime(CLOCK_MONOTONIC, &t0);
    
    for (int i = 1; i < nworkers; i++)
        pthread_create(&threads[i], NULL, worker_thread, &workers[i]);
    worker_thread(&workers[0]);
    
    for (int i = 1; i < nworkers; i++)
        pthread_join(threads[i], NULL);
    
    /* Now reduce the top-level ADDs (they connect the CALL results) */
    int64_t res = soma_graph_reduce_fast(rt, root);
    
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double par = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) / 1e9;
    
    printf("Parallel: %.4fs, result=%ld\n", par, res);
    printf("Speedup: %.2fx\n", base / par);
    
    uint64_t total_red = 0, total_tasks = 0;
    for (int i = 0; i < nworkers; i++) {
        printf("  Worker %d: %lu reductions, %lu tasks\n", 
               i, workers[i].reductions, workers[i].tasks);
        total_red += workers[i].reductions;
        total_tasks += workers[i].tasks;
    }
    
    free(workers);
    free(threads);
    soma_graph_shutdown(rt);
    
    return 0;
}
