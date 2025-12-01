#include "soma_graph.h"
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

uint32_t graph_fib(GraphRuntime* rt, int64_t n) {
    if (n < 2) return soma_graph_num(rt, n);
    uint32_t n1 = soma_graph_num(rt, n - 1);
    uint32_t n2 = soma_graph_num(rt, n - 2);
    uint32_t c1 = soma_graph_call1(rt, 0, n1);
    uint32_t c2 = soma_graph_call1(rt, 0, n2);
    return soma_graph_add(rt, c1, c2);
}

int main() {
    printf("Profiling single fib(30)...\n");
    
    struct timespec start, end;
    
    // Single-threaded
    GraphRuntime* rt = soma_graph_init(0);
    soma_graph_register_func(rt, "fib", 1, 0, (void*)graph_fib);
    
    uint32_t arg = soma_graph_num(rt, 30);
    uint32_t root = soma_graph_call1(rt, 0, arg);
    
    clock_gettime(CLOCK_MONOTONIC, &start);
    int64_t result = soma_graph_reduce_fast(rt, root);
    clock_gettime(CLOCK_MONOTONIC, &end);
    
    double time_sec = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
    uint64_t reductions = atomic_load(&rt->total_reductions);
    
    printf("Result: %ld\n", result);
    printf("Time: %.4f s\n", time_sec);
    printf("Reductions: %lu\n", (unsigned long)reductions);
    printf("Reductions/sec: %.2f M/s\n", reductions / time_sec / 1e6);
    
    soma_graph_shutdown(rt);
    return 0;
}
