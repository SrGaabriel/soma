#define _POSIX_C_SOURCE 200112L

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <sys/wait.h>
#include <unistd.h>
#include <fcntl.h>
#include <math.h>

#define DEFAULT_ITERATIONS 10
#define DEFAULT_MAX_WORKERS 4

typedef struct {
    double *times;
    int count;
    double mean;
    double stddev;
    double min;
    double max;
} BenchmarkResult;

static double get_time_ms(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1000.0 + ts.tv_nsec / 1000000.0;
}

static void calculate_stats(BenchmarkResult *result) {
    if (result->count == 0) return;

    result->min = result->times[0];
    result->max = result->times[0];
    double sum = 0.0;

    for (int i = 0; i < result->count; i++) {
        sum += result->times[i];
        if (result->times[i] < result->min) result->min = result->times[i];
        if (result->times[i] > result->max) result->max = result->times[i];
    }

    result->mean = sum / result->count;

    double variance = 0.0;
    for (int i = 0; i < result->count; i++) {
        double diff = result->times[i] - result->mean;
        variance += diff * diff;
    }
    result->stddev = sqrt(variance / result->count);
}

static int compile_program(const char *source, const char *mode, const char *output) {
    char cmd[1024];
    snprintf(cmd, sizeof(cmd), "cabal run somac -- %s -m %s -o %s -O3 2>&1", source, mode, output);

    FILE *fp = popen(cmd, "r");
    if (!fp) {
        fprintf(stderr, "Failed to run compiler\n");
        return -1;
    }

    char buffer[256];
    while (fgets(buffer, sizeof(buffer), fp) != NULL) {}

    int status = pclose(fp);
    if (WIFEXITED(status) && WEXITSTATUS(status) != 0) {
        fprintf(stderr, "Compilation failed for mode '%s'\n", mode);
        fprintf(stderr, "%s", buffer);
        return -1;
    }

    return 0;
}

static double run_once(const char *executable, int workers) {
    pid_t pid = fork();
    if (pid == -1) {
        perror("fork");
        return -1.0;
    }

    if (pid == 0) {
        // Child process
        // Set environment variable
        if (workers > 0) {
            char workers_str[32];
            snprintf(workers_str, sizeof(workers_str), "%d", workers);
            setenv("SOMA_WORKERS", workers_str, 1);
        }

        // Redirect stdout and stderr to /dev/null
        int devnull = open("/dev/null", O_WRONLY);
        if (devnull >= 0) {
            dup2(devnull, STDOUT_FILENO);
            dup2(devnull, STDERR_FILENO);
            close(devnull);
        }

        // Execute the program
        execl(executable, executable, (char *)NULL);
        exit(1);
    }

    // Parent process
    double start = get_time_ms();

    int status;
    waitpid(pid, &status, 0);

    double end = get_time_ms();
    return end - start;
}

static BenchmarkResult *run_benchmark(const char *executable, int iterations, int workers) {
    BenchmarkResult *result = malloc(sizeof(BenchmarkResult));
    result->times = malloc(sizeof(double) * iterations);
    result->count = 0;

    // Warmup run
    run_once(executable, workers);

    for (int i = 0; i < iterations; i++) {
        double time = run_once(executable, workers);
        if (time < 0) {
            fprintf(stderr, "Execution failed\n");
            free(result->times);
            free(result);
            return NULL;
        }
        result->times[result->count++] = time;
    }

    calculate_stats(result);
    return result;
}

static void print_result(const char *label, BenchmarkResult *result) {
    if (!result) {
        printf("  %-20s FAILED\n", label);
        return;
    }

    printf("  %-20s mean: %8.2f ms | stddev: %6.2f ms | min: %8.2f ms | max: %8.2f ms\n",
           label, result->mean, result->stddev, result->min, result->max);
}

static void free_result(BenchmarkResult *result) {
    if (result) {
        free(result->times);
        free(result);
    }
}

static void print_separator(void) {
    printf("--------------------------------------------------------------------------------\n");
}

int main(int argc, char *argv[]) {
    if (argc < 2) {
        fprintf(stderr, "Usage: %s <source.soma> [iterations] [max_workers]\n", argv[0]);
        fprintf(stderr, "\nArguments:\n");
        fprintf(stderr, "  source.soma   Path to the .soma source file to benchmark\n");
        fprintf(stderr, "  iterations    Number of times to run each benchmark (default: %d)\n", DEFAULT_ITERATIONS);
        fprintf(stderr, "  max_workers   Maximum SOMA_WORKERS for hybrid/graph modes (default: %d)\n", DEFAULT_MAX_WORKERS);
        return 1;
    }

    const char *source = argv[1];
    int iterations = (argc >= 3) ? atoi(argv[2]) : DEFAULT_ITERATIONS;
    int max_workers = (argc >= 4) ? atoi(argv[3]) : DEFAULT_MAX_WORKERS;

    if (iterations <= 0) {
        fprintf(stderr, "Error: iterations must be positive\n");
        return 1;
    }

    if (max_workers <= 0) {
        fprintf(stderr, "Error: max_workers must be positive\n");
        return 1;
    }

    if (access(source, F_OK) != 0) {
        fprintf(stderr, "Error: source file '%s' not found\n", source);
        return 1;
    }

    printf("\n");
    printf("Soma Benchmark\n");
    print_separator();
    printf("Source:     %s\n", source);
    printf("Iterations: %d\n", iterations);
    printf("Max workers: %d\n", max_workers);
    print_separator();

    const char *modes[] = {"standard", "graph", "hybrid"};
    const int num_modes = 3;

    char executables[3][256];
    for (int i = 0; i < num_modes; i++) {
        snprintf(executables[i], sizeof(executables[i]), "/tmp/soma_bench_%s_%d", modes[i], getpid());
    }

    printf("\nCompiling...\n");
    for (int i = 0; i < num_modes; i++) {
        printf("  Compiling %s mode...", modes[i]);
        fflush(stdout);
        if (compile_program(source, modes[i], executables[i]) != 0) {
            printf(" FAILED\n");
            for (int j = 0; j < i; j++) {
                unlink(executables[j]);
            }
            return 1;
        }
        printf(" OK\n");
    }

    print_separator();
    printf("\nBenchmarking...\n\n");

    printf("STANDARD MODE (sequential):\n");
    BenchmarkResult *standard_result = run_benchmark(executables[0], iterations, 0);
    print_result("standard", standard_result);
    printf("\n");

    printf("GRAPH MODE (interaction net reduction):\n");
    BenchmarkResult **graph_results = malloc(sizeof(BenchmarkResult*) * max_workers);
    for (int w = 1; w <= max_workers; w++) {
        char label[32];
        snprintf(label, sizeof(label), "workers=%d", w);
        graph_results[w-1] = run_benchmark(executables[2], iterations, w);
        print_result(label, graph_results[w-1]);
    }

    printf("HYBRID MODE (fork-join parallelism):\n");
    BenchmarkResult **hybrid_results = malloc(sizeof(BenchmarkResult*) * max_workers);
    for (int w = 1; w <= max_workers; w++) {
        char label[32];
        snprintf(label, sizeof(label), "workers=%d", w);
        hybrid_results[w-1] = run_benchmark(executables[1], iterations, w);
        print_result(label, hybrid_results[w-1]);
    }
    printf("\n");

    // Summary
    print_separator();
    printf("\nSUMMARY (speedup vs standard):\n");
    print_separator();

    if (standard_result && standard_result->mean > 0) {
        double baseline = standard_result->mean;

        printf("  %-20s %8.2f ms (baseline)\n", "standard", baseline);

        for (int w = 1; w <= max_workers; w++) {
            if (hybrid_results[w-1]) {
                char label[32];
                snprintf(label, sizeof(label), "hybrid (w=%d)", w);
                double speedup = baseline / hybrid_results[w-1]->mean;
                printf("  %-20s %8.2f ms (%.2fx)\n", label, hybrid_results[w-1]->mean, speedup);
            }
        }

        for (int w = 1; w <= max_workers; w++) {
            if (graph_results[w-1]) {
                char label[32];
                snprintf(label, sizeof(label), "graph (w=%d)", w);
                double speedup = baseline / graph_results[w-1]->mean;
                printf("  %-20s %8.2f ms (%.2fx)\n", label, graph_results[w-1]->mean, speedup);
            }
        }
    }

    printf("\n");

    // Cleanup
    free_result(standard_result);
    for (int w = 0; w < max_workers; w++) {
        free_result(hybrid_results[w]);
        free_result(graph_results[w]);
    }
    free(hybrid_results);
    free(graph_results);

    for (int i = 0; i < num_modes; i++) {
        unlink(executables[i]);
    }

    return 0;
}
