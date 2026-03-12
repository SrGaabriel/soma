import os
import statistics
import subprocess
import sys
import time


def run_once(exe):
    start = time.perf_counter_ns()
    result = subprocess.run(
        [exe],
        stdout=subprocess.DEVNULL,
        stderr=subprocess.PIPE,
    )
    elapsed_ns = time.perf_counter_ns() - start
    if result.returncode != 0:
        print(f"ERROR: {exe} exited with code {result.returncode}", file=sys.stderr)
        if result.stderr:
            print(result.stderr.decode(errors="replace"), file=sys.stderr)
        sys.exit(1)
    return elapsed_ns


def fmt_ns(ns):
    if ns < 1_000_000:
        return f"{ns / 1_000:.1f}µs"
    elif ns < 1_000_000_000:
        return f"{ns / 1_000_000:.2f}ms"
    else:
        return f"{ns / 1_000_000_000:.3f}s"


def main():
    import argparse

    parser = argparse.ArgumentParser(description="Soma benchmark runner")
    parser.add_argument("exe", nargs="?", default=os.path.join("target", "example.exe"))
    parser.add_argument("--runs", type=int, default=10)
    parser.add_argument("--warmup", type=int, default=2)
    args = parser.parse_args()

    exe = os.path.abspath(args.exe)
    if not os.path.isfile(exe):
        print(f"ERROR: executable not found: {exe}", file=sys.stderr)
        sys.exit(1)

    total_runs = args.warmup + args.runs
    print(f"Benchmark: {os.path.basename(exe)}")
    print(f"  Warmup: {args.warmup}  Measured: {args.runs}")
    print()

    times = []
    for i in range(total_runs):
        ns = run_once(exe)
        is_warmup = i < args.warmup
        label = "warmup" if is_warmup else f"run {i - args.warmup + 1:>2}"
        print(f"  [{label}] {fmt_ns(ns)}")
        if not is_warmup:
            times.append(ns)

    times.sort()
    print()
    print(f"  Results ({args.runs} runs):")
    print(f"    Min:    {fmt_ns(times[0])}")
    print(f"    Median: {fmt_ns(statistics.median(times))}")
    print(f"    Mean:   {fmt_ns(statistics.mean(times))}")
    print(f"    Max:    {fmt_ns(times[-1])}")
    print(f"    Stdev:  {fmt_ns(statistics.stdev(times))}" if len(times) > 1 else "")


if __name__ == "__main__":
    main()
