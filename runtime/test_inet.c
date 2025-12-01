/*
 * Test program for Soma Interaction Net Runtime
 * 
 * Tests the pure redex-driven reduction model.
 */

#include "soma_inet.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/*============================================================================
 * Fibonacci Implementation
 * 
 * fib(n) = if n < 2 then n else fib(n-1) + fib(n-2)
 * 
 * KEY: This function returns a TERM, not a value.
 * The term represents the computation graph.
 * Actual reduction happens incrementally via redexes.
 *===========================================================================*/

Term graph_fib(INet* net, ThreadMem* tm, Term arg) {
    /* Follow substitutions to get actual value */
    arg = term_is_sub(arg) ? term_clr_sub(arg) : arg;
    
    /* If arg is at a location, read it */
    if (term_tag(arg) != TAG_NUM) {
        /* Arg might be stored at a location */
        Term val = inet_get(net, term_loc(arg));
        if (term_is_sub(val)) {
            arg = term_clr_sub(val);
        }
    }
    
    if (term_tag(arg) != TAG_NUM) {
        /* Not yet a number - shouldn't happen with CBV */
        fprintf(stderr, "fib: arg not a number (tag=%02x)\n", term_tag(arg));
        return term_new(TAG_ERA, 0, 0);
    }
    
    int64_t n = inet_get_num(arg);
    
    if (n < 2) {
        return inet_num(n);
    }
    
    /* Build: ADD(fib(n-1), fib(n-2)) */
    
    /* Create REF nodes for recursive calls */
    /* REF stores the argument at its location */
    Term call1 = inet_ref(net, tm, 0, inet_num(n - 1));  /* fib(n-1) */
    Term call2 = inet_ref(net, tm, 0, inet_num(n - 2));  /* fib(n-2) */
    
    /* Create ADD(call1, call2) */
    return inet_opr(net, tm, OP_ADD, call1, call2);
}

/*============================================================================
 * Tree Sum Implementation
 * 
 * tree_sum(depth) = if depth <= 0 then 1 else tree_sum(depth-1) + tree_sum(depth-1)
 * Result = 2^depth
 * 
 * This creates a perfectly balanced binary tree of additions.
 *===========================================================================*/

Term graph_tree_sum(INet* net, ThreadMem* tm, Term arg) {
    arg = term_is_sub(arg) ? term_clr_sub(arg) : arg;
    
    if (term_tag(arg) != TAG_NUM) {
        Term val = inet_get(net, term_loc(arg));
        if (term_is_sub(val)) {
            arg = term_clr_sub(val);
        }
    }
    
    if (term_tag(arg) != TAG_NUM) {
        fprintf(stderr, "tree_sum: arg not a number\n");
        return term_new(TAG_ERA, 0, 0);
    }
    
    int64_t depth = inet_get_num(arg);
    
    if (depth <= 0) {
        return inet_num(1);
    }
    
    /* Build: ADD(tree_sum(depth-1), tree_sum(depth-1)) */
    Term call1 = inet_ref(net, tm, 1, inet_num(depth - 1));  /* tree_sum is at index 1 */
    Term call2 = inet_ref(net, tm, 1, inet_num(depth - 1));
    
    return inet_opr(net, tm, OP_ADD, call1, call2);
}

/*============================================================================
 * Build a balanced tree of fib calls (for parallel benchmarks)
 *===========================================================================*/

Term build_fib_tree(INet* net, ThreadMem* tm, int fib_n, int count) {
    if (count <= 0) {
        return inet_num(0);
    }
    if (count == 1) {
        return inet_ref(net, tm, 0, inet_num(fib_n));
    }
    
    int mid = count / 2;
    Term left = build_fib_tree(net, tm, fib_n, mid);
    Term right = build_fib_tree(net, tm, fib_n, count - mid);
    
    return inet_opr(net, tm, OP_ADD, left, right);
}

/*============================================================================
 * Tests
 *===========================================================================*/

void test_basic(void) {
    printf("=== Test: Basic Arithmetic ===\n");
    
    INet* net = inet_init(1);
    ThreadMem* tm = net->threads[0];
    
    /* Test: 3 + 4 = 7 */
    Term three = inet_num(3);
    Term four = inet_num(4);
    Term add = inet_opr(net, tm, OP_ADD, three, four);
    
    int64_t result = inet_reduce(net, add);
    
    printf("3 + 4 = %ld (expected 7)\n", result);
    printf("Status: %s\n\n", result == 7 ? "PASS" : "FAIL");
    
    inet_free(net);
}

void test_nested(void) {
    printf("=== Test: Nested Arithmetic ===\n");
    
    INet* net = inet_init(1);
    ThreadMem* tm = net->threads[0];
    
    /* Test: (1 + 2) + (3 + 4) = 10 */
    Term a = inet_opr(net, tm, OP_ADD, inet_num(1), inet_num(2));
    Term b = inet_opr(net, tm, OP_ADD, inet_num(3), inet_num(4));
    Term root = inet_opr(net, tm, OP_ADD, a, b);
    
    int64_t result = inet_reduce(net, root);
    
    printf("(1+2) + (3+4) = %ld (expected 10)\n", result);
    printf("Status: %s\n\n", result == 10 ? "PASS" : "FAIL");
    
    inet_free(net);
}

void test_fib(int n) {
    printf("=== Test: fib(%d) ===\n", n);
    
    INet* net = inet_init(1);
    inet_register_func(net, "fib", 1, graph_fib);
    
    Term root = inet_ref(net, net->threads[0], 0, inet_num(n));
    
    struct timespec start, end;
    clock_gettime(CLOCK_MONOTONIC, &start);
    int64_t result = inet_reduce(net, root);
    clock_gettime(CLOCK_MONOTONIC, &end);
    
    double time_sec = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
    
    int64_t fib_values[] = {0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 
                           610, 987, 1597, 2584, 4181, 6765, 10946, 17711, 28657,
                           46368, 75025, 121393, 196418, 317811, 514229, 832040};
    int64_t expected = (n < 31) ? fib_values[n] : -1;
    
    printf("fib(%d) = %ld (expected %ld)\n", n, result, expected);
    printf("Time: %.4f seconds\n", time_sec);
    printf("Status: %s\n\n", (expected == -1 || result == expected) ? "PASS" : "FAIL");
    
    inet_print_stats(net);
    inet_free(net);
}

/*============================================================================
 * Benchmarks
 *===========================================================================*/

void benchmark_fib(int fib_n, int count, int max_workers) {
    printf("\n");
    printf("╔══════════════════════════════════════════════════════════════════════╗\n");
    printf("║     INET PARALLEL BENCHMARK: %d × fib(%d)                            ║\n", count, fib_n);
    printf("╠══════════════════════════════════════════════════════════════════════╣\n");
    
    int64_t fib_values[] = {0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 
                           610, 987, 1597, 2584, 4181, 6765, 10946, 17711, 28657,
                           46368, 75025, 121393, 196418, 317811, 514229, 832040};
    int64_t expected = (fib_n < 31) ? fib_values[fib_n] * count : -1;
    
    double single_time = 0;
    
    printf("║                                                                      ║\n");
    printf("║ === Single-threaded baseline ===                                     ║\n");
    
    /* Single-threaded baseline */
    {
        INet* net = inet_init(1);
        inet_register_func(net, "fib", 1, graph_fib);
        inet_register_func(net, "tree_sum", 1, graph_tree_sum);
        
        Term root = build_fib_tree(net, net->threads[0], fib_n, count);
        
        struct timespec start, end;
        clock_gettime(CLOCK_MONOTONIC, &start);
        int64_t result = inet_reduce(net, root);
        clock_gettime(CLOCK_MONOTONIC, &end);
        
        single_time = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
        char status = (expected == -1 || result == expected) ? '+' : 'X';
        
        printf("║ 1 worker:         %8.4fs  speedup:  1.00x  result: %-8ld %c    ║\n",
               single_time, result, status);
        
        inet_free(net);
    }
    
    printf("║                                                                      ║\n");
    printf("║ === Multi-threaded (pure redex-driven) ===                           ║\n");
    
    /* Multi-threaded */
    for (int workers = 2; workers <= max_workers; workers++) {
        INet* net = inet_init(workers);
        inet_register_func(net, "fib", 1, graph_fib);
        inet_register_func(net, "tree_sum", 1, graph_tree_sum);
        
        Term root = build_fib_tree(net, net->threads[0], fib_n, count);
        
        struct timespec start, end;
        clock_gettime(CLOCK_MONOTONIC, &start);
        int64_t result = inet_reduce(net, root);
        clock_gettime(CLOCK_MONOTONIC, &end);
        
        double time_sec = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
        double speedup = single_time / time_sec;
        double efficiency = speedup / workers * 100;
        char status = (expected == -1 || result == expected) ? '+' : 'X';
        
        printf("║ %d workers:        %8.4fs  speedup: %5.2fx  efficiency: %5.1f%% %c  ║\n",
               workers, time_sec, speedup, efficiency, status);
        
        inet_free(net);
    }
    
    printf("╠══════════════════════════════════════════════════════════════════════╣\n");
    printf("║ Expected result: %-10ld                                           ║\n", expected);
    printf("╚══════════════════════════════════════════════════════════════════════╝\n\n");
}

void benchmark_tree_sum(int depth, int max_workers) {
    printf("\n");
    printf("╔══════════════════════════════════════════════════════════════════════╗\n");
    printf("║     INET TREE SUM BENCHMARK: tree_sum(%d)                            ║\n", depth);
    printf("╠══════════════════════════════════════════════════════════════════════╣\n");
    
    int64_t expected = 1LL << depth;
    double single_time = 0;
    
    printf("║                                                                      ║\n");
    printf("║ === Single-threaded baseline ===                                     ║\n");
    
    {
        INet* net = inet_init(1);
        inet_register_func(net, "fib", 1, graph_fib);
        inet_register_func(net, "tree_sum", 1, graph_tree_sum);
        
        Term root = inet_ref(net, net->threads[0], 1, inet_num(depth));
        
        struct timespec start, end;
        clock_gettime(CLOCK_MONOTONIC, &start);
        int64_t result = inet_reduce(net, root);
        clock_gettime(CLOCK_MONOTONIC, &end);
        
        single_time = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
        char status = (result == expected) ? '+' : 'X';
        
        printf("║ 1 worker:         %8.4fs  speedup:  1.00x  result: %-8ld %c    ║\n",
               single_time, result, status);
        
        inet_free(net);
    }
    
    printf("║                                                                      ║\n");
    printf("║ === Multi-threaded (pure redex-driven) ===                           ║\n");
    
    for (int workers = 2; workers <= max_workers; workers++) {
        INet* net = inet_init(workers);
        inet_register_func(net, "fib", 1, graph_fib);
        inet_register_func(net, "tree_sum", 1, graph_tree_sum);
        
        Term root = inet_ref(net, net->threads[0], 1, inet_num(depth));
        
        struct timespec start, end;
        clock_gettime(CLOCK_MONOTONIC, &start);
        int64_t result = inet_reduce(net, root);
        clock_gettime(CLOCK_MONOTONIC, &end);
        
        double time_sec = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
        double speedup = single_time / time_sec;
        double efficiency = speedup / workers * 100;
        char status = (result == expected) ? '+' : 'X';
        
        printf("║ %d workers:        %8.4fs  speedup: %5.2fx  efficiency: %5.1f%% %c  ║\n",
               workers, time_sec, speedup, efficiency, status);
        
        inet_free(net);
    }
    
    printf("╠══════════════════════════════════════════════════════════════════════╣\n");
    printf("║ Expected result: %-10ld                                           ║\n", expected);
    printf("╚══════════════════════════════════════════════════════════════════════╝\n\n");
}

/*============================================================================
 * Main
 *===========================================================================*/

int main(int argc, char** argv) {
    printf("Soma Interaction Net Runtime Tests\n");
    printf("===================================\n\n");
    
    if (argc > 1 && strcmp(argv[1], "bench") == 0) {
        int fib_n = 25;
        int count = 8;
        int max_workers = 4;
        
        if (argc > 2) fib_n = atoi(argv[2]);
        if (argc > 3) count = atoi(argv[3]);
        if (argc > 4) max_workers = atoi(argv[4]);
        
        benchmark_fib(fib_n, count, max_workers);
        return 0;
    }
    
    if (argc > 1 && strcmp(argv[1], "tree") == 0) {
        int depth = 20;
        int max_workers = 4;
        
        if (argc > 2) depth = atoi(argv[2]);
        if (argc > 3) max_workers = atoi(argv[3]);
        
        benchmark_tree_sum(depth, max_workers);
        return 0;
    }
    
    if (argc > 1 && strcmp(argv[1], "debug") == 0) {
        int fib_n = 10;
        if (argc > 2) fib_n = atoi(argv[2]);
        
        test_fib(fib_n);
        return 0;
    }
    
    /* Run basic tests */
    test_basic();
    test_nested();
    test_fib(10);
    test_fib(20);
    
    printf("\nAll tests completed!\n");
    
    return 0;
}
