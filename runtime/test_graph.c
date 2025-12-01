/*
 * Test program for Soma Graph Reduction Runtime
 * 
 * Tests:
 * 1. Basic arithmetic reduction
 * 2. Nested expressions
 * 3. Function calls (fib)
 */

#include "soma_graph.h"
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <string.h>

/* 
 * Graph-building fib function
 * 
 * This is what the compiler would generate for:
 *   def fib n = if n < 2 then n else fib(n-1) + fib(n-2)
 * 
 * The function builds a graph representing the computation,
 * rather than computing immediately. This allows parallel reduction.
 */
uint32_t graph_fib(GraphRuntime* rt, int64_t n) {
    if (n < 2) {
        /* Base case: return NUM node directly */
        return soma_graph_num(rt, n);
    }
    
    /* Recursive case: build ADD(CALL(fib, n-1), CALL(fib, n-2)) */
    
    /* Get fib's function index (it's 0, the first registered function) */
    uint16_t fib_idx = 0;
    
    /* Build argument nodes */
    uint32_t n_minus_1 = soma_graph_num(rt, n - 1);
    uint32_t n_minus_2 = soma_graph_num(rt, n - 2);
    
    if (n_minus_1 == GIDX_NULL || n_minus_2 == GIDX_NULL) {
        return GIDX_NULL;  /* Pool exhausted */
    }
    
    /* Build CALL nodes */
    uint32_t call_left = soma_graph_call1(rt, fib_idx, n_minus_1);
    uint32_t call_right = soma_graph_call1(rt, fib_idx, n_minus_2);
    
    if (call_left == GIDX_NULL || call_right == GIDX_NULL) {
        return GIDX_NULL;  /* Pool exhausted */
    }
    
    /* Build ADD node */
    return soma_graph_add(rt, call_left, call_right);
}

/* Test basic arithmetic */
void test_basic_arithmetic(void) {
    printf("=== Test: Basic Arithmetic ===\n");
    
    GraphRuntime* rt = soma_graph_init(0);  /* Single-threaded */
    
    /* Test: (3 + 4) * 2 = 14 */
    uint32_t n3 = soma_graph_num(rt, 3);
    uint32_t n4 = soma_graph_num(rt, 4);
    uint32_t n2 = soma_graph_num(rt, 2);
    uint32_t add = soma_graph_add(rt, n3, n4);
    uint32_t mul = soma_graph_mul(rt, add, n2);
    
    printf("Expression: (3 + 4) * 2\n");
    printf("Before reduction: ");
    soma_graph_dump(rt, mul, 10);
    printf("\n");
    
    int64_t result = soma_graph_reduce_fast(rt, mul);
    
    printf("After reduction: %ld\n", result);
    printf("Expected: 14\n");
    printf("Status: %s\n\n", result == 14 ? "PASS" : "FAIL");
    
    soma_graph_print_stats(rt);
    soma_graph_shutdown(rt);
}

/* Test nested expressions */
void test_nested_expressions(void) {
    printf("=== Test: Nested Expressions ===\n");
    
    GraphRuntime* rt = soma_graph_init(0);
    
    /* Test: ((1 + 2) + (3 + 4)) + ((5 + 6) + (7 + 8)) = 36 */
    uint32_t n1 = soma_graph_num(rt, 1);
    uint32_t n2 = soma_graph_num(rt, 2);
    uint32_t n3 = soma_graph_num(rt, 3);
    uint32_t n4 = soma_graph_num(rt, 4);
    uint32_t n5 = soma_graph_num(rt, 5);
    uint32_t n6 = soma_graph_num(rt, 6);
    uint32_t n7 = soma_graph_num(rt, 7);
    uint32_t n8 = soma_graph_num(rt, 8);
    
    uint32_t a12 = soma_graph_add(rt, n1, n2);
    uint32_t a34 = soma_graph_add(rt, n3, n4);
    uint32_t a56 = soma_graph_add(rt, n5, n6);
    uint32_t a78 = soma_graph_add(rt, n7, n8);
    
    uint32_t a1234 = soma_graph_add(rt, a12, a34);
    uint32_t a5678 = soma_graph_add(rt, a56, a78);
    
    uint32_t root = soma_graph_add(rt, a1234, a5678);
    
    printf("Expression: ((1+2)+(3+4)) + ((5+6)+(7+8))\n");
    printf("Before reduction: ");
    soma_graph_dump(rt, root, 5);
    printf("\n");
    
    int64_t result = soma_graph_reduce_fast(rt, root);
    
    printf("After reduction: %ld\n", result);
    printf("Expected: 36\n");
    printf("Status: %s\n\n", result == 36 ? "PASS" : "FAIL");
    
    soma_graph_print_stats(rt);
    soma_graph_shutdown(rt);
}

/* Test fib with graph building */
void test_fib(int n) {
    printf("=== Test: fib(%d) ===\n", n);
    
    GraphRuntime* rt = soma_graph_init(0);
    
    /* Register fib function */
    soma_graph_register_func(rt, "fib", 1, GFUNC_RECURSIVE, (void*)graph_fib);
    
    /* Build initial CALL node */
    uint32_t arg = soma_graph_num(rt, n);
    uint32_t root = soma_graph_call1(rt, 0, arg);
    
    printf("Expression: fib(%d)\n", n);
    
    /* Time the reduction */
    clock_t start = clock();
    int64_t result = soma_graph_reduce_fast(rt, root);
    clock_t end = clock();
    
    double time_sec = (double)(end - start) / CLOCKS_PER_SEC;
    
    printf("Result: %ld\n", result);
    printf("Time: %.4f seconds\n", time_sec);
    
    /* Known fib values for verification */
    int64_t expected[] = {0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 
                          610, 987, 1597, 2584, 4181, 6765, 10946, 17711, 28657,
                          46368, 75025, 121393, 196418, 317811, 514229, 832040};
    if (n < 31) {
        printf("Expected: %ld\n", expected[n]);
        printf("Status: %s\n", result == expected[n] ? "PASS" : "FAIL");
    }
    printf("\n");
    
    soma_graph_print_stats(rt);
    soma_graph_shutdown(rt);
}

/* Benchmark fib single-threaded */
void benchmark_fib(int n) {
    printf("=== Benchmark: fib(%d) [single-threaded] ===\n", n);
    
    GraphRuntime* rt = soma_graph_init(0);
    
    /* Register fib function */
    soma_graph_register_func(rt, "fib", 1, GFUNC_RECURSIVE, (void*)graph_fib);
    
    /* Build initial CALL node */
    uint32_t arg = soma_graph_num(rt, n);
    uint32_t root = soma_graph_call1(rt, 0, arg);
    
    /* Time the reduction */
    clock_t start = clock();
    int64_t result = soma_graph_reduce_fast(rt, root);
    clock_t end = clock();
    
    double time_sec = (double)(end - start) / CLOCKS_PER_SEC;
    
    printf("fib(%d) = %ld\n", n, result);
    printf("Time: %.4f seconds\n", time_sec);
    
    soma_graph_print_stats(rt);
    soma_graph_shutdown(rt);
}

/* Benchmark fib parallel */
void benchmark_fib_parallel(int n, int num_workers) {
    printf("=== Benchmark: fib(%d) [%d workers] ===\n", n, num_workers);
    
    GraphRuntime* rt = soma_graph_init(num_workers);
    
    /* Register fib function */
    soma_graph_register_func(rt, "fib", 1, GFUNC_RECURSIVE, (void*)graph_fib);
    
    /* Build initial CALL node */
    uint32_t arg = soma_graph_num(rt, n);
    uint32_t root = soma_graph_call1(rt, 0, arg);
    
    /* Time the reduction */
    clock_t start = clock();
    int64_t result = soma_graph_reduce_parallel(rt, root);
    clock_t end = clock();
    
    double time_sec = (double)(end - start) / CLOCKS_PER_SEC;
    
    printf("fib(%d) = %ld\n", n, result);
    printf("Time: %.4f seconds\n", time_sec);
    
    /* Print per-worker stats */
    printf("\nPer-worker statistics:\n");
    for (int i = 0; i < num_workers; i++) {
        printf("  Worker %d: %lu reductions, %lu steals\n", 
               i, rt->workers[i].reductions, rt->workers[i].steals);
    }
    
    soma_graph_print_stats(rt);
    soma_graph_shutdown(rt);
}

/*
 * Tree sum benchmark
 * 
 * Builds a complete binary tree of depth d with leaves containing 1,
 * then sums all leaves. Result = 2^d.
 * 
 * This has natural parallelism: sum(tree) = sum(left) + sum(right)
 * Unlike fib, no overlapping subproblems, so more independent work.
 */

/* tree_sum(depth): builds tree and returns sum */
uint32_t graph_tree_sum(GraphRuntime* rt, int64_t depth) {
    if (depth <= 0) {
        /* Leaf: return 1 */
        return soma_graph_num(rt, 1);
    }
    
    /* Internal node: sum(left) + sum(right) */
    uint16_t tree_sum_idx = 1;  /* tree_sum is registered at index 1 */
    
    uint32_t d_minus_1 = soma_graph_num(rt, depth - 1);
    uint32_t d_minus_1_b = soma_graph_num(rt, depth - 1);
    
    if (d_minus_1 == GIDX_NULL || d_minus_1_b == GIDX_NULL) {
        return GIDX_NULL;
    }
    
    uint32_t left = soma_graph_call1(rt, tree_sum_idx, d_minus_1);
    uint32_t right = soma_graph_call1(rt, tree_sum_idx, d_minus_1_b);
    
    if (left == GIDX_NULL || right == GIDX_NULL) {
        return GIDX_NULL;
    }
    
    return soma_graph_add(rt, left, right);
}

/* Benchmark tree_sum single-threaded */
void benchmark_tree_sum(int depth) {
    printf("=== Benchmark: tree_sum(%d) [single-threaded] ===\n", depth);
    
    GraphRuntime* rt = soma_graph_init(0);
    
    /* Register tree_sum function at index 1 (index 0 reserved for fib compatibility) */
    soma_graph_register_func(rt, "dummy", 1, 0, NULL);  /* placeholder at 0 */
    soma_graph_register_func(rt, "tree_sum", 1, GFUNC_RECURSIVE, (void*)graph_tree_sum);
    
    /* Build initial CALL node */
    uint32_t arg = soma_graph_num(rt, depth);
    uint32_t root = soma_graph_call1(rt, 1, arg);
    
    /* Time the reduction */
    clock_t start = clock();
    int64_t result = soma_graph_reduce_fast(rt, root);
    clock_t end = clock();
    
    double time_sec = (double)(end - start) / CLOCKS_PER_SEC;
    
    int64_t expected = 1LL << depth;  /* 2^depth */
    printf("tree_sum(%d) = %ld (expected %ld)\n", depth, result, expected);
    printf("Time: %.4f seconds\n", time_sec);
    printf("Status: %s\n", result == expected ? "PASS" : "FAIL");
    
    soma_graph_print_stats(rt);
    soma_graph_shutdown(rt);
}

/* Benchmark tree_sum parallel */
void benchmark_tree_sum_parallel(int depth, int num_workers) {
    printf("=== Benchmark: tree_sum(%d) [%d workers] ===\n", depth, num_workers);
    
    GraphRuntime* rt = soma_graph_init(num_workers);
    
    /* Register tree_sum function */
    soma_graph_register_func(rt, "dummy", 1, 0, NULL);
    soma_graph_register_func(rt, "tree_sum", 1, GFUNC_RECURSIVE, (void*)graph_tree_sum);
    
    /* Build initial CALL node */
    uint32_t arg = soma_graph_num(rt, depth);
    uint32_t root = soma_graph_call1(rt, 1, arg);
    
    /* Time the reduction */
    clock_t start = clock();
    int64_t result = soma_graph_reduce_parallel(rt, root);
    clock_t end = clock();
    
    double time_sec = (double)(end - start) / CLOCKS_PER_SEC;
    
    int64_t expected = 1LL << depth;
    printf("tree_sum(%d) = %ld (expected %ld)\n", depth, result, expected);
    printf("Time: %.4f seconds\n", time_sec);
    printf("Status: %s\n", result == expected ? "PASS" : "FAIL");
    
    /* Print per-worker stats */
    printf("\nPer-worker statistics:\n");
    for (int i = 0; i < num_workers; i++) {
        printf("  Worker %d: %lu reductions, %lu iters\n", 
               i, rt->workers[i].reductions, rt->workers[i].steals);
    }
    
    soma_graph_print_stats(rt);
    soma_graph_shutdown(rt);
}

/*
 * Parallel sum of multiple independent fib computations
 * 
 * Computes: fib(n) + fib(n) + ... + fib(n)  (k times)
 * 
 * This is ideal for parallelism because:
 * - Each fib(n) is completely independent
 * - Each subtask has significant work (unlike tree_sum leaves)
 * - No data dependencies between branches
 */
/* Build a balanced binary tree of fib(n) calls to enable parallel reduction.
 * 
 * Instead of left-deep:  ADD(ADD(ADD(fib, fib), fib), fib)  -- sequential deps!
 * Build balanced:        ADD(ADD(fib, fib), ADD(fib, fib))  -- parallel branches!
 */
static uint32_t graph_sum_fibs_balanced(GraphRuntime* rt, uint16_t fib_idx, int n, int start, int end) {
    if (start >= end) {
        return soma_graph_num(rt, 0);
    }
    if (start + 1 == end) {
        /* Single element: just one fib(n) call */
        uint32_t arg = soma_graph_num(rt, n);
        return soma_graph_call1(rt, fib_idx, arg);
    }
    
    /* Split in half and recurse - this creates a balanced tree */
    int mid = start + (end - start) / 2;
    uint32_t left = graph_sum_fibs_balanced(rt, fib_idx, n, start, mid);
    uint32_t right = graph_sum_fibs_balanced(rt, fib_idx, n, mid, end);
    
    return soma_graph_add(rt, left, right);
}

uint32_t graph_sum_fibs(GraphRuntime* rt, int n, int count) {
    if (count <= 0) {
        return soma_graph_num(rt, 0);
    }
    
    uint16_t fib_idx = 0;  /* fib is at index 0 */
    
    /* Build a BALANCED binary tree of count fib(n) calls.
     * This allows parallel evaluation of independent branches. */
    return graph_sum_fibs_balanced(rt, fib_idx, n, 0, count);
}

/*
 * True parallel benchmark: run N independent fib computations
 * using pthread-level parallelism, then compare to sequential.
 * 
 * This shows what parallelism SHOULD look like when work is
 * truly independent (no shared graph state).
 */

typedef struct {
    int n;
    int64_t result;
} FibTask;

static void* pthread_fib_worker(void* arg) {
    FibTask* task = (FibTask*)arg;
    
    /* Each worker gets its own graph runtime */
    GraphRuntime* rt = soma_graph_init(0);
    soma_graph_register_func(rt, "fib", 1, GFUNC_RECURSIVE, (void*)graph_fib);
    
    uint32_t arg_node = soma_graph_num(rt, task->n);
    uint32_t root = soma_graph_call1(rt, 0, arg_node);
    
    task->result = soma_graph_reduce_fast(rt, root);
    
    soma_graph_shutdown(rt);
    return NULL;
}

void benchmark_true_parallel(int fib_n, int count, int max_workers) {
    printf("\n");
    printf("╔══════════════════════════════════════════════════════════════════════╗\n");
    printf("║   TRUE PARALLEL BENCHMARK: %d independent fib(%d) computations       ║\n", count, fib_n);
    printf("╠══════════════════════════════════════════════════════════════════════╣\n");
    
    int64_t fib_values[] = {0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 
                           610, 987, 1597, 2584, 4181, 6765, 10946, 17711, 28657,
                           46368, 75025, 121393, 196418, 317811, 514229, 832040};
    int64_t single_fib = (fib_n < 31) ? fib_values[fib_n] : -1;
    int64_t expected = single_fib * count;
    
    double single_time = 0;
    
    /* Single-threaded: run all fibs sequentially */
    printf("║                                                                      ║\n");
    printf("║ === Sequential (one thread, %d fibs in series) ===                   ║\n", count);
    {
        struct timespec start, end;
        clock_gettime(CLOCK_MONOTONIC, &start);
        
        int64_t total = 0;
        for (int i = 0; i < count; i++) {
            GraphRuntime* rt = soma_graph_init(0);
            soma_graph_register_func(rt, "fib", 1, GFUNC_RECURSIVE, (void*)graph_fib);
            uint32_t arg = soma_graph_num(rt, fib_n);
            uint32_t root = soma_graph_call1(rt, 0, arg);
            total += soma_graph_reduce_fast(rt, root);
            soma_graph_shutdown(rt);
        }
        
        clock_gettime(CLOCK_MONOTONIC, &end);
        single_time = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
        
        char status = (total == expected) ? '+' : 'X';
        printf("║ Sequential:       %8.4fs  speedup:  1.00x  result: %-8ld %c     ║\n",
               single_time, total, status);
    }
    
    printf("║                                                                      ║\n");
    printf("║ === Pthread parallel (each fib in separate thread) ===               ║\n");
    
    /* Parallel with different thread counts */
    for (int num_threads = 2; num_threads <= max_workers && num_threads <= count; num_threads++) {
        struct timespec start, end;
        clock_gettime(CLOCK_MONOTONIC, &start);
        
        FibTask* tasks = malloc(count * sizeof(FibTask));
        pthread_t* threads = malloc(num_threads * sizeof(pthread_t));
        
        /* Initialize all tasks */
        for (int i = 0; i < count; i++) {
            tasks[i].n = fib_n;
            tasks[i].result = 0;
        }
        
        /* Process tasks in batches of num_threads */
        int task_idx = 0;
        while (task_idx < count) {
            int batch_size = (count - task_idx < num_threads) ? (count - task_idx) : num_threads;
            
            /* Start threads for this batch */
            for (int t = 0; t < batch_size; t++) {
                pthread_create(&threads[t], NULL, pthread_fib_worker, &tasks[task_idx + t]);
            }
            
            /* Wait for batch to complete */
            for (int t = 0; t < batch_size; t++) {
                pthread_join(threads[t], NULL);
            }
            
            task_idx += batch_size;
        }
        
        /* Sum results */
        int64_t total = 0;
        for (int i = 0; i < count; i++) {
            total += tasks[i].result;
        }
        
        clock_gettime(CLOCK_MONOTONIC, &end);
        double time_sec = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
        double speedup = single_time / time_sec;
        double efficiency = speedup / num_threads * 100;
        
        char status = (total == expected) ? '+' : 'X';
        printf("║ %d threads:        %8.4fs  speedup: %5.2fx  efficiency: %5.1f%% %c   ║\n",
               num_threads, time_sec, speedup, efficiency, status);
        
        free(tasks);
        free(threads);
    }
    
    printf("╠══════════════════════════════════════════════════════════════════════╣\n");
    printf("║ Expected result: %-10ld                                           ║\n", expected);
    printf("╚══════════════════════════════════════════════════════════════════════╝\n\n");
}

/* Comprehensive parallel benchmark comparing 1 vs N workers */
void benchmark_parallel_comparison(int fib_n, int count, int max_workers) {
    printf("\n");
    printf("╔══════════════════════════════════════════════════════════════════════╗\n");
    printf("║         PARALLEL SPEEDUP BENCHMARK: %d × fib(%d)                     ║\n", count, fib_n);
    printf("╠══════════════════════════════════════════════════════════════════════╣\n");
    
    /* Known fib values */
    int64_t fib_values[] = {0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 
                           610, 987, 1597, 2584, 4181, 6765, 10946, 17711, 28657,
                           46368, 75025, 121393, 196418, 317811, 514229, 832040};
    int64_t expected = (fib_n < 31) ? fib_values[fib_n] * count : -1;
    
    double single_time = 0;
    
    printf("║                                                                      ║\n");
    printf("║ === Single-threaded baseline ===                                     ║\n");
    
    /* Single-threaded baseline */
    {
        GraphRuntime* rt = soma_graph_init(1);
        soma_graph_register_func(rt, "fib", 1, GFUNC_RECURSIVE, (void*)graph_fib);
        uint32_t root = graph_sum_fibs(rt, fib_n, count);
        
        struct timespec start, end;
        clock_gettime(CLOCK_MONOTONIC, &start);
        int64_t result = soma_graph_reduce_fast(rt, root);
        clock_gettime(CLOCK_MONOTONIC, &end);
        
        single_time = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
        char status = (expected == -1 || result == expected) ? '+' : 'X';
        
        printf("║ 1 worker (fast):  %8.4fs  speedup:  1.00x  efficiency: 100.0%% %c  ║\n",
               single_time, status);
        soma_graph_shutdown(rt);
    }
    
    printf("║                                                                      ║\n");
    printf("║ === Task-parallel (work-stealing, no barriers) ===                   ║\n");
    
    /* Task-parallel with different worker counts */
    for (int workers = 2; workers <= max_workers; workers++) {
        GraphRuntime* rt = soma_graph_init(workers);
        soma_graph_register_func(rt, "fib", 1, GFUNC_RECURSIVE, (void*)graph_fib);
        uint32_t root = graph_sum_fibs(rt, fib_n, count);
        
        struct timespec start, end;
        clock_gettime(CLOCK_MONOTONIC, &start);
        int64_t result = soma_graph_reduce_taskpar(rt, root);
        clock_gettime(CLOCK_MONOTONIC, &end);
        
        double time_sec = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
        double speedup = single_time / time_sec;
        double efficiency = speedup / workers * 100;
        char status = (expected == -1 || result == expected) ? '+' : 'X';
        
        printf("║ %d workers (task): %8.4fs  speedup: %5.2fx  efficiency: %5.1f%% %c  ║\n",
               workers, time_sec, speedup, efficiency, status);
        
        /* Show per-worker stats */
        uint64_t total_reductions = 0;
        uint64_t total_steals = 0;
        for (int i = 0; i < workers; i++) {
            total_reductions += rt->workers[i].reductions;
            total_steals += rt->workers[i].steals;
        }
        printf("║   reductions: %-8lu  steals: %-8lu                            ║\n",
               total_reductions, total_steals);
        
        soma_graph_shutdown(rt);
    }
    
    printf("║                                                                      ║\n");
    printf("║ === Fork-join parallel (separate runtimes per subtask) ===           ║\n");
    
    /* Fork-join with different worker counts */
    for (int workers = 2; workers <= max_workers; workers++) {
        GraphRuntime* rt = soma_graph_init(workers);
        soma_graph_register_func(rt, "fib", 1, GFUNC_RECURSIVE, (void*)graph_fib);
        uint32_t root = graph_sum_fibs(rt, fib_n, count);
        
        struct timespec start, end;
        clock_gettime(CLOCK_MONOTONIC, &start);
        int64_t result = soma_graph_reduce_forkjoin(rt, root);
        clock_gettime(CLOCK_MONOTONIC, &end);
        
        double time_sec = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
        double speedup = single_time / time_sec;
        double efficiency = speedup / workers * 100;
        char status = (expected == -1 || result == expected) ? '+' : 'X';
        
        printf("║ %d workers (fork): %8.4fs  speedup: %5.2fx  efficiency: %5.1f%% %c  ║\n",
               workers, time_sec, speedup, efficiency, status);
        
        soma_graph_shutdown(rt);
    }
    
    printf("╠══════════════════════════════════════════════════════════════════════╣\n");
    printf("║ Expected result: %-10ld                                           ║\n", expected);
    printf("╚══════════════════════════════════════════════════════════════════════╝\n\n");
}

/* Quick parallel correctness test */
void test_parallel_correctness(void) {
    printf("=== Test: Parallel Reduction Correctness ===\n");
    
    /* Test with 4 workers */
    GraphRuntime* rt = soma_graph_init(4);
    
    soma_graph_register_func(rt, "fib", 1, GFUNC_RECURSIVE, (void*)graph_fib);
    
    /* Compute 4 × fib(15) in parallel */
    uint32_t root = graph_sum_fibs(rt, 15, 4);
    
    int64_t result = soma_graph_reduce_parallel(rt, root);
    int64_t expected = 610 * 4;  /* fib(15) = 610 */
    
    printf("4 × fib(15) = %ld (expected %ld)\n", result, expected);
    printf("Status: %s\n\n", result == expected ? "PASS" : "FAIL");
    
    soma_graph_print_stats(rt);
    soma_graph_shutdown(rt);
}

int main(int argc, char** argv) {
    printf("Soma Graph Reduction Runtime Tests\n");
    printf("===================================\n\n");
    
    if (argc > 1 && strcmp(argv[1], "bench") == 0) {
        int n = 30;
        if (argc > 2) {
            n = atoi(argv[2]);
        }
        benchmark_fib(n);
        return 0;
    }
    
    if (argc > 1 && strcmp(argv[1], "parallel") == 0) {
        int n = 30;
        int workers = 4;
        if (argc > 2) {
            n = atoi(argv[2]);
        }
        if (argc > 3) {
            workers = atoi(argv[3]);
        }
        benchmark_fib_parallel(n, workers);
        return 0;
    }
    
    if (argc > 1 && strcmp(argv[1], "tree") == 0) {
        int depth = 20;
        if (argc > 2) {
            depth = atoi(argv[2]);
        }
        benchmark_tree_sum(depth);
        return 0;
    }
    
    if (argc > 1 && strcmp(argv[1], "tree-parallel") == 0) {
        int depth = 20;
        int workers = 4;
        if (argc > 2) {
            depth = atoi(argv[2]);
        }
        if (argc > 3) {
            workers = atoi(argv[3]);
        }
        benchmark_tree_sum_parallel(depth, workers);
        return 0;
    }
    
    /* New: parallel speedup comparison */
    if (argc > 1 && strcmp(argv[1], "speedup") == 0) {
        int fib_n = 25;       /* Size of each fib computation */
        int count = 8;        /* Number of independent fibs */
        int max_workers = 4;  /* Max workers to test */
        
        if (argc > 2) fib_n = atoi(argv[2]);
        if (argc > 3) count = atoi(argv[3]);
        if (argc > 4) max_workers = atoi(argv[4]);
        
        benchmark_parallel_comparison(fib_n, count, max_workers);
        return 0;
    }
    
    /* True parallel benchmark with separate runtimes */
    if (argc > 1 && strcmp(argv[1], "trueparallel") == 0) {
        int fib_n = 25;
        int count = 8;
        int max_workers = 4;
        
        if (argc > 2) fib_n = atoi(argv[2]);
        if (argc > 3) count = atoi(argv[3]);
        if (argc > 4) max_workers = atoi(argv[4]);
        
        benchmark_true_parallel(fib_n, count, max_workers);
        return 0;
    }
    
    /* Run tests */
    test_basic_arithmetic();
    test_nested_expressions();
    test_fib(10);
    test_fib(20);
    
    printf("\nAll tests completed!\n");
    
    return 0;
}
