/*
 * Soma Hybrid Runtime
 *
 * This runtime wraps the base soma_runtime with:
 * - Memory pool initialization (always, for INETS memory management)
 * - Optional fork-join parallelism (via SOMA_PARALLEL env var)
 *
 * Use this runtime for hybrid mode compilation (-m hybrid).
 *
 * Compilation:
 *   clang -O2 program.ll runtime/soma_hybrid.c -lpthread -o program
 *
 * Environment variables:
 *   SOMA_PARALLEL=N   Enable N worker threads for fork-join parallelism
 *   SOMA_PAR_STATS=1  Print parallel runtime statistics on exit
 */

/* Include the base runtime without its main() */
#define SOMA_NO_MAIN
#include "soma_runtime.c"

/*
 * Main entry point for hybrid mode
 *
 * Always initializes memory pools (needed for lazy duplication).
 * Optionally initializes parallel runtime if SOMA_PARALLEL is set.
 */
extern int soma_main(void);

int main(void) {
    /* Always initialize memory pools - hybrid mode uses INETS for memory */
    soma_pool_init();

    /* Optionally enable parallelism */
    const char* par_env = getenv("SOMA_PARALLEL");
    if (par_env != NULL) {
        int num_workers = atoi(par_env);
        if (num_workers > 0) {
            soma_par_init(num_workers);
        }
    }

    /* Run the program */
    int result = soma_main();

    /* Cleanup */
    if (par_env != NULL && soma_par_enabled()) {
        if (getenv("SOMA_PAR_STATS") != NULL) {
            soma_par_print_stats();
        }
        soma_par_shutdown();
    }

    soma_pool_cleanup();
    return result;
}
