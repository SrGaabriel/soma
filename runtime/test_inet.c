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
 * Interaction Calculus Tests
 *===========================================================================*/

void test_dup_num(void) {
    printf("=== Test: DUP-NUM (duplicate a number) ===\n");
    
    INet* net = inet_init(1);
    ThreadMem* tm = net->threads[0];
    
    /* Test: !{a b} &1 = 42; a + b = 84 */
    
    /* Create DUP node for 42 */
    Loc proj0_slot, proj1_slot;
    Term dup = inet_dup_with_projs(net, tm, 1, inet_num(42), &proj0_slot, &proj1_slot);
    (void)dup;
    
    /* Manually trigger the interaction */
    inet_interact_dup_num(net, tm, dup, inet_num(42));
    
    /* Read proj0 and proj1 */
    Term proj0 = inet_get(net, proj0_slot);
    Term proj1 = inet_get(net, proj1_slot);
    
    /* Both should be 42 (with SUB flag) */
    int64_t val0 = inet_get_num(term_clr_sub(proj0));
    int64_t val1 = inet_get_num(term_clr_sub(proj1));
    
    printf("DUP-NUM: proj0=%ld, proj1=%ld (expected 42, 42)\n", val0, val1);
    printf("Status: %s\n\n", (val0 == 42 && val1 == 42) ? "PASS" : "FAIL");
    
    inet_free(net);
}

void test_dup_era(void) {
    printf("=== Test: DUP-ERA (duplicate erasure) ===\n");
    
    INet* net = inet_init(1);
    ThreadMem* tm = net->threads[0];
    
    /* Test: !{a b} &1 = *; a = *, b = * */
    
    Term era = term_new(TAG_ERA, 0, 0);
    Loc proj0_slot, proj1_slot;
    Term dup = inet_dup_with_projs(net, tm, 1, era, &proj0_slot, &proj1_slot);
    
    inet_interact_dup_era(net, tm, dup);
    
    Term proj0 = inet_get(net, proj0_slot);
    Term proj1 = inet_get(net, proj1_slot);
    
    int pass = (term_tag(term_clr_sub(proj0)) == TAG_ERA && 
                term_tag(term_clr_sub(proj1)) == TAG_ERA);
    
    printf("DUP-ERA: proj0=ERA?%d, proj1=ERA?%d\n", 
           term_tag(term_clr_sub(proj0)) == TAG_ERA,
           term_tag(term_clr_sub(proj1)) == TAG_ERA);
    printf("Status: %s\n\n", pass ? "PASS" : "FAIL");
    
    inet_free(net);
}

void test_dup_sup_annihilate(void) {
    printf("=== Test: DUP-SUP Annihilation (same label) ===\n");
    
    INet* net = inet_init(1);
    ThreadMem* tm = net->threads[0];
    
    /* Test: !{a b} &1 = &1{10, 20}; a = 10, b = 20 */
    
    /* Create SUP{10, 20} with label 1 */
    Term sup = inet_sup(net, tm, 1, inet_num(10), inet_num(20));
    
    /* Create DUP with same label 1 */
    Loc proj0_slot, proj1_slot;
    Term dup = inet_dup_with_projs(net, tm, 1, sup, &proj0_slot, &proj1_slot);
    
    inet_interact_dup_sup(net, tm, dup, sup);
    
    Term proj0 = inet_get(net, proj0_slot);
    Term proj1 = inet_get(net, proj1_slot);
    
    int64_t val0 = inet_get_num(term_clr_sub(proj0));
    int64_t val1 = inet_get_num(term_clr_sub(proj1));
    
    printf("DUP-SUP annihilate: proj0=%ld, proj1=%ld (expected 10, 20)\n", val0, val1);
    printf("Status: %s\n\n", (val0 == 10 && val1 == 20) ? "PASS" : "FAIL");
    
    inet_free(net);
}

void test_dup_sup_commute(void) {
    printf("=== Test: DUP-SUP Commutation (different labels) ===\n");
    
    INet* net = inet_init(1);
    ThreadMem* tm = net->threads[0];
    
    /* Test: !{a b} &1 = &2{10, 20}
     * Result: a = &2{x0, y0}, b = &2{x1, y1}
     *         where !{x0 x1} &1 = 10, !{y0 y1} &1 = 20
     */
    
    /* Create SUP{10, 20} with label 2 */
    Term sup = inet_sup(net, tm, 2, inet_num(10), inet_num(20));
    
    /* Create DUP with label 1 (different from SUP's label 2) */
    Loc proj0_slot, proj1_slot;
    Term dup = inet_dup_with_projs(net, tm, 1, sup, &proj0_slot, &proj1_slot);
    
    inet_interact_dup_sup(net, tm, dup, sup);
    
    Term proj0 = inet_get(net, proj0_slot);
    Term proj1 = inet_get(net, proj1_slot);
    
    /* Both projections should be SUPs with label 2 */
    proj0 = term_clr_sub(proj0);
    proj1 = term_clr_sub(proj1);
    
    int pass = (term_tag(proj0) == TAG_SUP && term_aux(proj0) == 2 &&
                term_tag(proj1) == TAG_SUP && term_aux(proj1) == 2);
    
    printf("DUP-SUP commute: proj0=SUP[%d]? proj1=SUP[%d]?\n",
           term_aux(proj0), term_aux(proj1));
    printf("Status: %s\n\n", pass ? "PASS" : "FAIL");
    
    inet_free(net);
}

void test_app_sup(void) {
    printf("=== Test: APP-SUP (apply superposition) ===\n");
    
    INet* net = inet_init(1);
    ThreadMem* tm = net->threads[0];
    
    /* Test: (&1{λx.x+1, λx.x+2}) 10
     * 
     * For this test, we'll verify APP-SUP creates the right structure
     * by applying to simple numbers instead of lambdas, since full 
     * reduction requires internal reduce_term which is static.
     * 
     * Alternative test: ((&1{1, 2}) + 10) should give us &1{11, 12}
     * But OPR doesn't distribute over SUP by default.
     * 
     * So we'll test that APP-SUP at least produces the right structure.
     */
    
    /* Create λx.x+1 */
    Loc var1_slot = inet_alloc(net, tm, 1);
    inet_set(net, var1_slot, term_new(TAG_NIL, 0, 0));
    Term body1 = inet_opr(net, tm, OP_ADD, term_new(TAG_NIL, 0, var1_slot), inet_num(1));
    Term lam1 = inet_lam(net, tm, var1_slot, body1);
    
    /* Create λx.x+2 */
    Loc var2_slot = inet_alloc(net, tm, 1);
    inet_set(net, var2_slot, term_new(TAG_NIL, 0, 0));
    Term body2 = inet_opr(net, tm, OP_ADD, term_new(TAG_NIL, 0, var2_slot), inet_num(2));
    Term lam2 = inet_lam(net, tm, var2_slot, body2);
    
    /* Create SUP{lam1, lam2} */
    Term sup = inet_sup(net, tm, 1, lam1, lam2);
    
    /* Test inet_interact_app_sup directly */
    Term result = inet_interact_app_sup(net, tm, sup, inet_num(10), 1);
    
    /* Result should be SUP{APP(lam1, arg0), APP(lam2, arg1)} */
    int pass = 0;
    if (term_tag(result) == TAG_SUP) {
        Loc sup_loc = term_loc(result);
        Term left = inet_get(net, sup_loc);
        Term right = inet_get(net, sup_loc + 1);
        
        /* Both should be APP nodes */
        pass = (term_tag(left) == TAG_APP && term_tag(right) == TAG_APP);
        printf("APP-SUP: result=SUP{APP, APP}? left=%02x, right=%02x\n",
               term_tag(left), term_tag(right));
    } else {
        printf("APP-SUP: result tag=%02x (expected SUP)\n", term_tag(result));
    }
    
    printf("Status: %s\n\n", pass ? "PASS" : "FAIL");
    
    inet_free(net);
}

void test_dup_lam(void) {
    printf("=== Test: DUP-LAM (duplicate lambda) ===\n");
    
    INet* net = inet_init(1);
    ThreadMem* tm = net->threads[0];
    
    /* Test: !{f0 f1} &1 = λx.x; both f0 and f1 should be lambdas */
    
    /* Create λx.x */
    Loc var_slot = inet_alloc(net, tm, 1);
    inet_set(net, var_slot, term_new(TAG_NIL, 0, 0));
    Term lam = inet_lam(net, tm, var_slot, term_new(TAG_NIL, 0, var_slot));
    
    /* Create DUP */
    Loc proj0_slot, proj1_slot;
    Term dup = inet_dup_with_projs(net, tm, 1, lam, &proj0_slot, &proj1_slot);
    
    inet_interact_dup_lam(net, tm, dup, lam);
    
    /* Get the two lambdas */
    Term lam0 = inet_get(net, proj0_slot);
    Term lam1 = inet_get(net, proj1_slot);
    
    lam0 = term_clr_sub(lam0);
    lam1 = term_clr_sub(lam1);
    
    /* Both should be lambdas */
    int pass = (term_tag(lam0) == TAG_LAM && term_tag(lam1) == TAG_LAM);
    
    printf("DUP-LAM: proj0 tag=%02x (LAM=%02x), proj1 tag=%02x (LAM=%02x)\n",
           term_tag(lam0), TAG_LAM, term_tag(lam1), TAG_LAM);
    printf("Status: %s\n\n", pass ? "PASS" : "FAIL");
    
    inet_free(net);
}

void test_dup_in_reduction(void) {
    printf("=== Test: DUP in reduction (x + x where x = 21) ===\n");
    
    INet* net = inet_init(1);
    ThreadMem* tm = net->threads[0];
    
    /* Test: Manually trigger DUP-NUM and then use the results in addition.
     * 
     * The DUP interaction needs to happen first before we can use the projections.
     * In a real compiler-generated graph, the DUP would be properly linked.
     */
    
    /* Create DUP of 21 */
    Loc a_slot, b_slot;
    Term dup = inet_dup_with_projs(net, tm, 1, inet_num(21), &a_slot, &b_slot);
    
    /* Trigger the DUP-NUM interaction */
    inet_interact_dup_num(net, tm, dup, inet_num(21));
    
    /* Now the projection slots have the duplicated values */
    Term a_val = inet_get(net, a_slot);
    Term b_val = inet_get(net, b_slot);
    
    /* Create a + b using the actual values */
    Term add = inet_opr(net, tm, OP_ADD, a_val, b_val);
    
    /* Reduce */
    int64_t result = inet_reduce(net, add);
    
    printf("(!{a b} &1 = 21; a + b) = %ld (expected 42)\n", result);
    printf("Status: %s\n\n", result == 42 ? "PASS" : "FAIL");
    
    inet_free(net);
}

void test_nested_dup(void) {
    printf("=== Test: Nested DUP (x + x + x + x) ===\n");
    
    INet* net = inet_init(1);
    ThreadMem* tm = net->threads[0];
    
    /* Test: let x = 10 in x + x + x + x = 40
     * This requires multiple DUPs, each manually triggered.
     */
    
    /* Start with x = 10 */
    Term x = inet_num(10);
    
    /* First DUP: !{a b} = x */
    Loc a_slot, b_slot;
    Term dup1 = inet_dup_with_projs(net, tm, 1, x, &a_slot, &b_slot);
    inet_interact_dup_num(net, tm, dup1, x);
    
    /* Second DUP: !{c d} = a (which is now 10) */
    Term a_val = inet_get(net, a_slot);
    Loc c_slot, d_slot;
    Term dup2 = inet_dup_with_projs(net, tm, 2, a_val, &c_slot, &d_slot);
    inet_interact_dup_num(net, tm, dup2, term_clr_sub(a_val));
    
    /* Third DUP: !{e f} = b (which is now 10) */
    Term b_val = inet_get(net, b_slot);
    Loc e_slot, f_slot;
    Term dup3 = inet_dup_with_projs(net, tm, 3, b_val, &e_slot, &f_slot);
    inet_interact_dup_num(net, tm, dup3, term_clr_sub(b_val));
    
    /* Build: (c + d) + (e + f) */
    Term c_val = inet_get(net, c_slot);
    Term d_val = inet_get(net, d_slot);
    Term e_val = inet_get(net, e_slot);
    Term f_val = inet_get(net, f_slot);
    
    Term add1 = inet_opr(net, tm, OP_ADD, c_val, d_val);
    Term add2 = inet_opr(net, tm, OP_ADD, e_val, f_val);
    Term add3 = inet_opr(net, tm, OP_ADD, add1, add2);
    
    int64_t result = inet_reduce(net, add3);
    
    printf("Nested DUP: x + x + x + x = %ld (expected 40)\n", result);
    printf("Status: %s\n\n", result == 40 ? "PASS" : "FAIL");
    
    inet_free(net);
}

/*============================================================================
 * Lambda/Closure Tests
 *===========================================================================*/

void test_lambda_identity(void) {
    printf("=== Test: Lambda Identity ===\n");
    
    INet* net = inet_init(1);
    ThreadMem* tm = net->threads[0];
    
    /* Test: (λx.x) 42 = 42 */
    /* Build: APP(LAM(x, x), 42) */
    
    /* Allocate variable slot */
    Loc var_slot = inet_alloc(net, tm, 1);
    inet_set(net, var_slot, term_new(TAG_NIL, 0, 0));
    
    /* Create lambda: λx.x (body is just the variable) */
    Term var_ref = term_new(TAG_NIL, 0, var_slot);
    Term lam = inet_lam(net, tm, var_slot, var_ref);
    
    /* Create application: (λx.x) 42 */
    Term app = inet_app(net, tm, lam, inet_num(42));
    
    int64_t result = inet_reduce(net, app);
    
    printf("(λx.x) 42 = %ld (expected 42)\n", result);
    printf("Status: %s\n\n", result == 42 ? "PASS" : "FAIL");
    
    inet_free(net);
}

void test_lambda_const(void) {
    printf("=== Test: Lambda Const ===\n");
    
    INet* net = inet_init(1);
    ThreadMem* tm = net->threads[0];
    
    /* Test: (λx.λy.x) 1 2 = 1 */
    /* This tests nested lambdas and ignoring an argument */
    
    /* Allocate variable slots */
    Loc var_x = inet_alloc(net, tm, 1);
    Loc var_y = inet_alloc(net, tm, 1);
    inet_set(net, var_x, term_new(TAG_NIL, 0, 0));
    inet_set(net, var_y, term_new(TAG_NIL, 0, 0));
    
    /* Inner lambda: λy.x (returns x, ignores y) */
    Term inner_lam = inet_lam(net, tm, var_y, term_new(TAG_NIL, 0, var_x));
    
    /* Outer lambda: λx.(λy.x) */
    Term outer_lam = inet_lam(net, tm, var_x, inner_lam);
    
    /* Apply twice: ((λx.λy.x) 1) 2 */
    Term app1 = inet_app(net, tm, outer_lam, inet_num(1));
    Term app2 = inet_app(net, tm, app1, inet_num(2));
    
    int64_t result = inet_reduce(net, app2);
    
    printf("(λx.λy.x) 1 2 = %ld (expected 1)\n", result);
    printf("Status: %s\n\n", result == 1 ? "PASS" : "FAIL");
    
    inet_free(net);
}

void test_lambda_add(void) {
    printf("=== Test: Lambda with Arithmetic ===\n");
    
    INet* net = inet_init(1);
    ThreadMem* tm = net->threads[0];
    
    /* Test: (λx. x + x) 21 = 42 */
    
    /* Allocate variable slot */
    Loc var_x = inet_alloc(net, tm, 1);
    inet_set(net, var_x, term_new(TAG_NIL, 0, 0));
    
    /* Body: x + x */
    Term x_ref1 = term_new(TAG_NIL, 0, var_x);
    Term x_ref2 = term_new(TAG_NIL, 0, var_x);
    Term body = inet_opr(net, tm, OP_ADD, x_ref1, x_ref2);
    
    /* Lambda: λx. x + x */
    Term lam = inet_lam(net, tm, var_x, body);
    
    /* Application: (λx. x + x) 21 */
    Term app = inet_app(net, tm, lam, inet_num(21));
    
    int64_t result = inet_reduce(net, app);
    
    printf("(λx. x + x) 21 = %ld (expected 42)\n", result);
    printf("Status: %s\n\n", result == 42 ? "PASS" : "FAIL");
    
    inet_free(net);
}

void test_closure(void) {
    printf("=== Test: Closure ===\n");
    
    INet* net = inet_init(1);
    ThreadMem* tm = net->threads[0];
    
    /* Test a closure with captured environment */
    /* We'll create: let add = λx.λy. x + y in (add 10) 32 = 42 */
    
    /* For this test, we'll use the CLO representation directly */
    /* Create a closure that adds its environment to its argument */
    
    /* Register a function that reads env[0] + arg */
    /* add_closure(clo) where clo has env = [x], returns x + arg */
    
    /* For simplicity, test identity closure first */
    Term env[1] = { inet_num(10) };
    
    /* Create closure: func_idx=0, arity=1, env=[10] */
    /* We need a function that does: env[0] + arg */
    
    /* Actually let's just verify closure creation/cloning works */
    Term clo = inet_closure(net, tm, 0, 1, env, 1);
    Term clo_copy = inet_clone_closure(net, tm, clo);
    
    /* Verify both are CLO tags */
    int pass = (term_tag(clo) == TAG_CLO && term_tag(clo_copy) == TAG_CLO);
    
    /* Verify they have different locations (shallow copy) */
    pass = pass && (term_loc(clo) != term_loc(clo_copy));
    
    /* Verify env was copied */
    Loc loc1 = term_loc(clo);
    Loc loc2 = term_loc(clo_copy);
    Term env1 = inet_get(net, loc1 + 2);
    Term env2 = inet_get(net, loc2 + 2);
    pass = pass && (inet_get_num(env1) == 10 && inet_get_num(env2) == 10);
    
    printf("Closure creation and cloning: %s\n", pass ? "PASS" : "FAIL");
    printf("Status: %s\n\n", pass ? "PASS" : "FAIL");
    
    inet_free(net);
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
    
    /* Interaction Calculus tests */
    test_dup_num();
    test_dup_era();
    test_dup_sup_annihilate();
    test_dup_sup_commute();
    test_dup_lam();
    test_app_sup();
    test_dup_in_reduction();
    test_nested_dup();
    
    /* Lambda tests */
    test_lambda_identity();
    test_lambda_const();
    test_lambda_add();
    test_closure();
    
    /* Fib tests */
    test_fib(10);
    test_fib(20);
    
    printf("\nAll tests completed!\n");
    
    return 0;
}
