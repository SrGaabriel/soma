import os
import statistics
import subprocess
import sys
import time
import shutil


BENCH_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bench")
TARGET_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "target")


def find_tool(name):
    return shutil.which(name)


def compile_targets():
    """Compile all benchmark targets. Returns list of (name, cmd) tuples where cmd is a list."""
    os.makedirs(TARGET_DIR, exist_ok=True)
    targets = []

    # Soma (already built)
    soma_exe = os.path.join(TARGET_DIR, "example.exe")
    if os.path.isfile(soma_exe):
        targets.append(("Soma", [soma_exe]))
    else:
        print("  [skip] Soma: not built (run 'haoma build --release' first)")

    # C (gcc -O2)
    gcc = find_tool("gcc")
    if gcc:
        c_src = os.path.join(BENCH_DIR, "main.c")
        c_exe = os.path.join(TARGET_DIR, "bench_c.exe")
        r = subprocess.run([gcc, "-O2", "-o", c_exe, c_src], capture_output=True)
        if r.returncode == 0:
            targets.append(("C (gcc -O2)", [c_exe]))
        else:
            print(f"  [skip] C: compile failed: {r.stderr.decode(errors='replace')[:200]}")
    else:
        print("  [skip] C: gcc not found")

    # Rust (rustc -O)
    rustc = find_tool("rustc")
    if rustc:
        rs_src = os.path.join(BENCH_DIR, "main.rs")
        rs_exe = os.path.join(TARGET_DIR, "bench_rust.exe")
        r = subprocess.run([rustc, "-O", "-o", rs_exe, rs_src], capture_output=True)
        if r.returncode == 0:
            targets.append(("Rust (rustc -O)", [rs_exe]))
        else:
            print(f"  [skip] Rust: compile failed: {r.stderr.decode(errors='replace')[:200]}")
    else:
        print("  [skip] Rust: rustc not found")

    # Zig (zig build-exe -OReleaseFast)
    zig = find_tool("zig")
    if zig:
        zig_src = os.path.join(BENCH_DIR, "main.zig")
        zig_exe = os.path.join(TARGET_DIR, "bench_zig.exe")
        r = subprocess.run(
            [zig, "build-exe", "-OReleaseFast", "-lc", "-femit-bin=" + zig_exe, zig_src],
            capture_output=True,
        )
        if r.returncode == 0:
            targets.append(("Zig (ReleaseFast)", [zig_exe]))
        else:
            print(f"  [skip] Zig: compile failed: {r.stderr.decode(errors='replace')[:200]}")
    else:
        print("  [skip] Zig: zig not found")

    # Go
    go = find_tool("go")
    if go:
        go_src = os.path.join(BENCH_DIR, "main.go")
        go_exe = os.path.join(TARGET_DIR, "bench_go.exe")
        r = subprocess.run([go, "build", "-o", go_exe, go_src], capture_output=True)
        if r.returncode == 0:
            targets.append(("Go", [go_exe]))
        else:
            print(f"  [skip] Go: compile failed: {r.stderr.decode(errors='replace')[:200]}")
    else:
        print("  [skip] Go: go not found")

    # Haskell (ghc -O2)
    ghc = find_tool("ghc")
    if ghc:
        hs_src = os.path.join(BENCH_DIR, "main.hs")
        hs_exe = os.path.join(TARGET_DIR, "bench_haskell.exe")
        r = subprocess.run([ghc, "-O2", "-o", hs_exe, hs_src, "-no-keep-hi-files", "-no-keep-o-files"],
                           capture_output=True)
        if r.returncode == 0:
            targets.append(("Haskell (ghc -O2)", [hs_exe]))
        else:
            print(f"  [skip] Haskell: compile failed: {r.stderr.decode(errors='replace')[:200]}")
    else:
        print("  [skip] Haskell: ghc not found")

    # OCaml (ocamlfind/ocamlopt)
    ocamlopt = find_tool("ocamlfind") or find_tool("ocamlopt")
    if ocamlopt:
        ml_src = os.path.join(BENCH_DIR, "main.ml")
        ml_exe = os.path.join(TARGET_DIR, "bench_ocaml.exe")
        if "ocamlfind" in ocamlopt:
            cmd = [ocamlopt, "ocamlopt", "-package", "stdlib", "-linkpkg", "-O2", "-o", ml_exe, ml_src]
        else:
            cmd = [ocamlopt, "-O2", "-o", ml_exe, ml_src]
        r = subprocess.run(cmd, capture_output=True)
        if r.returncode == 0:
            targets.append(("OCaml (ocamlopt -O2)", [ml_exe]))
        else:
            print(f"  [skip] OCaml: compile failed: {r.stderr.decode(errors='replace')[:200]}")
    else:
        print("  [skip] OCaml: ocamlopt not found")

    # V8 / Node.js
    js_src = os.path.join(BENCH_DIR, "main.js")
    node = find_tool("node")
    if node:
        targets.append(("Node.js (V8)", [node, js_src]))
    else:
        print("  [skip] Node.js: node not found")

    # Bun
    bun = find_tool("bun")
    if bun:
        targets.append(("Bun", [bun, "run", js_src]))
    else:
        print("  [skip] Bun: bun not found")

    # Python
    py_src = os.path.join(BENCH_DIR, "main.py")
    python = find_tool("python3") or find_tool("python")
    if python:
        targets.append(("Python", [python, py_src]))
    else:
        print("  [skip] Python: python not found")

    return targets


def run_once(cmd):
    start = time.perf_counter_ns()
    result = subprocess.run(
        cmd,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.PIPE,
    )
    elapsed_ns = time.perf_counter_ns() - start
    if result.returncode != 0:
        print(f"ERROR: {cmd[0]} exited with code {result.returncode}", file=sys.stderr)
        if result.stderr:
            print(result.stderr.decode(errors="replace"), file=sys.stderr)
        return None
    return elapsed_ns


def fmt_ns(ns):
    if ns < 1_000_000:
        return f"{ns / 1_000:.1f}us"
    elif ns < 1_000_000_000:
        return f"{ns / 1_000_000:.2f}ms"
    else:
        return f"{ns / 1_000_000_000:.3f}s"


def bench_target(name, cmd, runs=10, warmup=2):
    total_runs = warmup + runs
    times = []
    for i in range(total_runs):
        ns = run_once(cmd)
        if ns is None:
            return None
        if i >= warmup:
            times.append(ns)
    times.sort()
    return {
        "name": name,
        "min": times[0],
        "median": statistics.median(times),
        "mean": statistics.mean(times),
        "max": times[-1],
        "stdev": statistics.stdev(times) if len(times) > 1 else 0,
    }


def main():
    import argparse

    parser = argparse.ArgumentParser(description="Soma cross-language benchmark")
    parser.add_argument("--runs", type=int, default=10)
    parser.add_argument("--warmup", type=int, default=3)
    args = parser.parse_args()

    print("=" * 60)
    print("  Soma Cross-Language Benchmark")
    print("=" * 60)
    print()
    print("Compiling targets...")
    targets = compile_targets()
    print(f"  {len(targets)} target(s) ready")
    print()

    results = []
    for name, cmd in targets:
        print(f"Benchmarking: {name}")
        r = bench_target(name, cmd, runs=args.runs, warmup=args.warmup)
        if r:
            print(f"  median: {fmt_ns(r['median'])}  min: {fmt_ns(r['min'])}")
            results.append(r)
        else:
            print("  FAILED")
        print()

    if not results:
        print("No results.")
        return

    # Sort by median time
    results.sort(key=lambda r: r["median"])
    baseline = results[0]["median"]

    print("=" * 60)
    print("  RESULTS (sorted by median, lower is better)")
    print("=" * 60)
    print()
    print(f"  {'Language':<25} {'Median':>10} {'Min':>10} {'vs best':>10}")
    print(f"  {'-'*25} {'-'*10} {'-'*10} {'-'*10}")
    for r in results:
        ratio = r["median"] / baseline if baseline > 0 else 0
        ratio_str = f"{ratio:.2f}x" if ratio > 1.005 else "baseline"
        print(f"  {r['name']:<25} {fmt_ns(r['median']):>10} {fmt_ns(r['min']):>10} {ratio_str:>10}")
    print()


if __name__ == "__main__":
    main()
