/*
 * Test program for Soma HVM-Style Runtime
 */

#include "soma_hvm.h"
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <string.h>

/*
 * Fibonacci function implementation
 * 
 * fib(n) = if n < 2 then n else fib(n-1) + fib(n-2)
 */
Term graph_fib(HvmNet* net, ThreadMem* tm, Term ref) {
    /* Get argument from ref */
    Loc arg_loc = term_loc(ref);
    Term arg = hvm_get(net, arg_loc);
    
    /* Follow substitutions to get actual value */
    while (term_tag(arg) == TAG_VAR) {
        Term val = hvm_get(net, term_loc(arg));
        if (!term_is_sub(val)) break;
        arg = term_rem_sub(val);
    }
    
    if (term_tag(arg) != TAG_NUM) {
        /* Argument not yet reduced - re-enqueue */
        return ref;
    }
    
    int64_t n = hvm_get_num(arg);
    
    if (n < 2) {
        return hvm_num(n);
    }
    
    /* Build: ADD(fib(n-1), fib(n-2)) */
    
    /* Create argument nodes */
    Loc arg1_loc = hvm_alloc(net, tm);
    Loc arg2_loc = hvm_alloc(net, tm);
    hvm_set(net, arg1_loc, hvm_num(n - 1));
    hvm_set(net, arg2_loc, hvm_num(n - 2));
    
    /* Create REF nodes for recursive calls */
    Term call1 = term_new(TAG_REF, 0, arg1_loc);  /* fib(n-1) */
    Term call2 = term_new(TAG_REF, 0, arg2_loc);  /* fib(n-2) */
    
    /* Create ADD node: OPX(ADD, call1, call2) */
    return hvm_opx(net, tm, OP_ADD, call1, call2);
}

/*
 * Build a balanced tree of fib calls
 */
Term build_fib_tree(HvmNet* net, ThreadMem* tm, int fib_n, int count) {
    if (count <= 0) {
        return hvm_num(0);
    }
    if (count == 1) {
        Loc arg_loc = hvm_alloc(net, tm);
        hvm_set(net, arg_loc, hvm_num(fib_n));
        return term_new(TAG_REF, 0, arg_loc);  /* fib(fib_n) */
    }
    
    /* Build balanced tree: ADD(left_subtree, right_subtree) */
    int mid = count / 2;
    Term left = build_fib_tree(net, tm, fib_n, mid);
    Term right = build_fib_tree(net, tm, fib_n, count - mid);
    
    return hvm_opx(net, tm, OP_ADD, left, right);
}

/*
 * Benchmark
 */
void benchmark(int fib_n, int count, int max_workers) {
    printf("\n");
    printf("╔══════════════════════════════════════════════════════════════════════╗\n");
    printf("║     HVM-STYLE PARALLEL BENCHMARK: %d × fib(%d)                       ║\n", count, fib_n);
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
        HvmNet* net = hvm_init(1);
        hvm_register_func(net, "fib", 1, graph_fib);
        
        Term root = build_fib_tree(net, net->tms[0], fib_n, count);
        
        struct timespec start, end;
        clock_gettime(CLOCK_MONOTONIC, &start);
        int64_t result = hvm_reduce(net, root);
        clock_gettime(CLOCK_MONOTONIC, &end);
        
        single_time = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
        char status = (expected == -1 || result == expected) ? '+' : 'X';
        
        printf("║ 1 worker:         %8.4fs  speedup:  1.00x  result: %-8ld %c    ║\n",
               single_time, result, status);
        
        hvm_free(net);
    }
    
    printf("║                                                                      ║\n");
    printf("║ === Multi-threaded (HVM-style partitioned memory) ===                ║\n");
    
    /* Multi-threaded with different worker counts */
    for (int workers = 2; workers <= max_workers; workers++) {
        HvmNet* net = hvm_init(workers);
        hvm_register_func(net, "fib", 1, graph_fib);
        
        Term root = build_fib_tree(net, net->tms[0], fib_n, count);
        
        struct timespec start, end;
        clock_gettime(CLOCK_MONOTONIC, &start);
        int64_t result = hvm_reduce(net, root);
        clock_gettime(CLOCK_MONOTONIC, &end);
        
        double time_sec = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
        double speedup = single_time / time_sec;
        double efficiency = speedup / workers * 100;
        char status = (expected == -1 || result == expected) ? '+' : 'X';
        
        printf("║ %d workers:        %8.4fs  speedup: %5.2fx  efficiency: %5.1f%% %c  ║\n",
               workers, time_sec, speedup, efficiency, status);
        
        hvm_free(net);
    }
    
    printf("╠══════════════════════════════════════════════════════════════════════╣\n");
    printf("║ Expected result: %-10ld                                           ║\n", expected);
    printf("╚══════════════════════════════════════════════════════════════════════╝\n\n");
}

/* Simple correctness test */
void test_basic(void) {
    printf("=== Test: Basic Arithmetic ===\n");
    
    HvmNet* net = hvm_init(1);
    
    /* Test: 3 + 4 = 7 */
    Term three = hvm_num(3);
    Term four = hvm_num(4);
    Term add = hvm_opx(net, net->tms[0], OP_ADD, three, four);
    
    int64_t result = hvm_reduce(net, add);
    
    printf("3 + 4 = %ld (expected 7)\n", result);
    printf("Status: %s\n\n", result == 7 ? "PASS" : "FAIL");
    
    hvm_free(net);
}

void test_nested(void) {
    printf("=== Test: Nested Arithmetic ===\n");
    
    HvmNet* net = hvm_init(1);
    ThreadMem* tm = net->tms[0];
    
    /* Test: (1 + 2) + (3 + 4) = 10 */
    Term a = hvm_opx(net, tm, OP_ADD, hvm_num(1), hvm_num(2));
    Term b = hvm_opx(net, tm, OP_ADD, hvm_num(3), hvm_num(4));
    Term root = hvm_opx(net, tm, OP_ADD, a, b);
    
    int64_t result = hvm_reduce(net, root);
    
    printf("(1+2) + (3+4) = %ld (expected 10)\n", result);
    printf("Status: %s\n\n", result == 10 ? "PASS" : "FAIL");
    
    hvm_free(net);
}

void test_fib(int n) {
    printf("=== Test: fib(%d) ===\n", n);
    
    HvmNet* net = hvm_init(1);
    hvm_register_func(net, "fib", 1, graph_fib);
    
    /* Build fib(n) call */
    Loc arg_loc = hvm_alloc(net, net->tms[0]);
    hvm_set(net, arg_loc, hvm_num(n));
    Term root = term_new(TAG_REF, 0, arg_loc);
    
    struct timespec start, end;
    clock_gettime(CLOCK_MONOTONIC, &start);
    int64_t result = hvm_reduce(net, root);
    clock_gettime(CLOCK_MONOTONIC, &end);
    
    double time_sec = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
    
    int64_t fib_values[] = {0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 
                           610, 987, 1597, 2584, 4181, 6765, 10946, 17711, 28657,
                           46368, 75025, 121393, 196418, 317811, 514229, 832040};
    int64_t expected = (n < 31) ? fib_values[n] : -1;
    
    printf("fib(%d) = %ld (expected %ld)\n", n, result, expected);
    printf("Time: %.4f seconds\n", time_sec);
    printf("Status: %s\n\n", (expected == -1 || result == expected) ? "PASS" : "FAIL");
    
    hvm_print_stats(net);
    hvm_free(net);
}

/*
 * Tree sum function implementation
 * 
 * tree_sum(depth) = if depth <= 0 then 1 else tree_sum(depth-1) + tree_sum(depth-1)
 * Result = 2^depth
 */
Term graph_tree_sum(HvmNet* net, ThreadMem* tm, Term ref) {
    Loc arg_loc = term_loc(ref);
    Term arg = hvm_get(net, arg_loc);
    
    while (term_tag(arg) == TAG_VAR) {
        Term val = hvm_get(net, term_loc(arg));
        if (!term_is_sub(val)) break;
        arg = term_rem_sub(val);
    }
    
    if (term_tag(arg) != TAG_NUM) {
        return ref;
    }
    
    int64_t depth = hvm_get_num(arg);
    
    if (depth <= 0) {
        return hvm_num(1);
    }
    
    /* Build: ADD(tree_sum(depth-1), tree_sum(depth-1)) */
    Loc arg1_loc = hvm_alloc(net, tm);
    Loc arg2_loc = hvm_alloc(net, tm);
    hvm_set(net, arg1_loc, hvm_num(depth - 1));
    hvm_set(net, arg2_loc, hvm_num(depth - 1));
    
    /* tree_sum is registered at index 1 */
    Term call1 = term_new(TAG_REF, 1, arg1_loc);
    Term call2 = term_new(TAG_REF, 1, arg2_loc);
    
    return hvm_opx(net, tm, OP_ADD, call1, call2);
}

void benchmark_tree_sum(int depth, int max_workers) {
    printf("\n");
    printf("╔══════════════════════════════════════════════════════════════════════╗\n");
    printf("║     HVM-STYLE TREE SUM BENCHMARK: tree_sum(%d)                       ║\n", depth);
    printf("╠══════════════════════════════════════════════════════════════════════╣\n");
    
    int64_t expected = 1LL << depth;  /* 2^depth */
    double single_time = 0;
    
    printf("║                                                                      ║\n");
    printf("║ === Single-threaded baseline ===                                     ║\n");
    
    {
        HvmNet* net = hvm_init(1);
        hvm_register_func(net, "fib", 1, graph_fib);        /* Index 0 (placeholder) */
        hvm_register_func(net, "tree_sum", 1, graph_tree_sum);  /* Index 1 */
        
        Loc arg_loc = hvm_alloc(net, net->tms[0]);
        hvm_set(net, arg_loc, hvm_num(depth));
        Term root = term_new(TAG_REF, 1, arg_loc);  /* Call tree_sum */
        
        struct timespec start, end;
        clock_gettime(CLOCK_MONOTONIC, &start);
        int64_t result = hvm_reduce(net, root);
        clock_gettime(CLOCK_MONOTONIC, &end);
        
        single_time = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
        char status = (result == expected) ? '+' : 'X';
        
        printf("║ 1 worker:         %8.4fs  speedup:  1.00x  result: %-8ld %c    ║\n",
               single_time, result, status);
        
        hvm_free(net);
    }
    
    printf("║                                                                      ║\n");
    printf("║ === Multi-threaded (HVM-style partitioned memory) ===                ║\n");
    
    for (int workers = 2; workers <= max_workers; workers++) {
        HvmNet* net = hvm_init(workers);
        hvm_register_func(net, "fib", 1, graph_fib);
        hvm_register_func(net, "tree_sum", 1, graph_tree_sum);
        
        Loc arg_loc = hvm_alloc(net, net->tms[0]);
        hvm_set(net, arg_loc, hvm_num(depth));
        Term root = term_new(TAG_REF, 1, arg_loc);
        
        struct timespec start, end;
        clock_gettime(CLOCK_MONOTONIC, &start);
        int64_t result = hvm_reduce(net, root);
        clock_gettime(CLOCK_MONOTONIC, &end);
        
        double time_sec = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
        double speedup = single_time / time_sec;
        double efficiency = speedup / workers * 100;
        char status = (result == expected) ? '+' : 'X';
        
        printf("║ %d workers:        %8.4fs  speedup: %5.2fx  efficiency: %5.1f%% %c  ║\n",
               workers, time_sec, speedup, efficiency, status);
        
        hvm_free(net);
    }
    
    printf("╠══════════════════════════════════════════════════════════════════════╣\n");
    printf("║ Expected result: %-10ld                                           ║\n", expected);
    printf("╚══════════════════════════════════════════════════════════════════════╝\n\n");
}

int main(int argc, char** argv) {
    printf("Soma HVM-Style Runtime Tests\n");
    printf("============================\n\n");
    
    if (argc > 1 && strcmp(argv[1], "bench") == 0) {
        int fib_n = 25;
        int count = 8;
        int max_workers = 4;
        
        if (argc > 2) fib_n = atoi(argv[2]);
        if (argc > 3) count = atoi(argv[3]);
        if (argc > 4) max_workers = atoi(argv[4]);
        
        benchmark(fib_n, count, max_workers);
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
        int depth = 20;
        int workers = 2;
        
        if (argc > 2) depth = atoi(argv[2]);
        if (argc > 3) workers = atoi(argv[3]);
        
        printf("Debug: tree_sum(%d) with %d workers\n\n", depth, workers);
        
        HvmNet* net = hvm_init(workers);
        hvm_register_func(net, "fib", 1, graph_fib);
        hvm_register_func(net, "tree_sum", 1, graph_tree_sum);
        
        Loc arg_loc = hvm_alloc(net, net->tms[0]);
        hvm_set(net, arg_loc, hvm_num(depth));
        Term root = term_new(TAG_REF, 1, arg_loc);
        
        struct timespec start, end;
        clock_gettime(CLOCK_MONOTONIC, &start);
        int64_t result = hvm_reduce(net, root);
        clock_gettime(CLOCK_MONOTONIC, &end);
        
        double time_sec = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
        int64_t expected = 1LL << depth;
        
        printf("Result: %ld (expected %ld) %s\n", result, expected, 
               result == expected ? "OK" : "FAIL");
        printf("Time: %.4fs\n", time_sec);
        
        hvm_print_stats(net);
        hvm_free(net);
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
