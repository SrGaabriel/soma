/*
 * True parallel: Each worker has its OWN runtime
 * This is the upper bound on parallelism we can achieve
 */

#include "soma_graph.h"
#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <time.h>

typedef struct {
    int fib_n;
    int count;  /* Number of fibs this worker computes */
    int64_t result;
} Task;

uint32_t graph_fib(GraphRuntime* rt, int64_t n) {
    if (n < 2) return soma_graph_num(rt, n);
    uint32_t n1 = soma_graph_num(rt, n - 1);
    uint32_t n2 = soma_graph_num(rt, n - 2);
    uint32_t c1 = soma_graph_call1(rt, 0, n1);
    uint32_t c2 = soma_graph_call1(rt, 0, n2);
    return soma_graph_add(rt, c1, c2);
}

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

static void* worker(void* arg) {
    Task* t = (Task*)arg;
    
    /* Each worker has its OWN runtime */
    GraphRuntime* rt = soma_graph_init(0);
    soma_graph_register_func(rt, "fib", 1, 0, (void*)graph_fib);
    
    uint32_t root = build_tree(rt, t->fib_n, t->count);
    t->result = soma_graph_reduce_fast(rt, root);
    
    soma_graph_shutdown(rt);
    return NULL;
}

int main(int argc, char** argv) {
    int fib_n = 25, count = 8, nworkers = 4;
    if (argc > 1) fib_n = atoi(argv[1]);
    if (argc > 2) count = atoi(argv[2]);
    if (argc > 3) nworkers = atoi(argv[3]);
    
    printf("Separate runtimes: %d × fib(%d), %d workers\n\n", count, fib_n, nworkers);
    
    /* Baseline - single thread */
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
    
    /* Parallel - each worker has separate runtime */
    Task* tasks = calloc(nworkers, sizeof(Task));
    pthread_t* threads = calloc(nworkers, sizeof(pthread_t));
    
    /* Distribute work */
    int per_worker = count / nworkers;
    int remainder = count % nworkers;
    for (int i = 0; i < nworkers; i++) {
        tasks[i].fib_n = fib_n;
        tasks[i].count = per_worker + (i < remainder ? 1 : 0);
    }
    
    clock_gettime(CLOCK_MONOTONIC, &t0);
    
    for (int i = 1; i < nworkers; i++)
        pthread_create(&threads[i], NULL, worker, &tasks[i]);
    worker(&tasks[0]);
    
    for (int i = 1; i < nworkers; i++)
        pthread_join(threads[i], NULL);
    
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double par = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) / 1e9;
    
    int64_t total = 0;
    for (int i = 0; i < nworkers; i++) total += tasks[i].result;
    
    printf("Parallel: %.4fs, result=%ld\n", par, total);
    printf("Speedup: %.2fx\n", base / par);
    
    free(tasks);
    free(threads);
    
    return 0;
}
