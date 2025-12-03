/*
 * Soma Hybrid Runtime Header
 *
 * This runtime wraps the base soma_runtime with:
 * - Memory pool initialization (always, for INETS memory management)
 * - Optional fork-join parallelism (via SOMA_WORKERS env var)
 *
 * Use this runtime for hybrid mode compilation (-m hybrid).
 *
 * Compilation:
 *   clang -O2 program.ll runtime/soma_hybrid.c -lpthread -o program
 *
 * Environment variables:
 *   SOMA_WORKERS=N    Enable N worker threads for fork-join parallelism
 *   SOMA_PAR_STATS=1  Print parallel runtime statistics on exit
 */

#ifndef SOMA_HYBRID_H
#define SOMA_HYBRID_H

#include "soma_runtime.h"

/*
 * Main entry point for hybrid mode programs.
 * Must be defined by the compiled program.
 */
extern int soma_main(void);

#endif /* SOMA_HYBRID_H */
