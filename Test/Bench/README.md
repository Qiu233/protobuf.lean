# Engineering benchmark

This benchmark compares the same generated `bench.perf.Batch` workload across:

- `lean-binary`: this repository's generated binary codec;
- `cpp-binary`: the official C++ protobuf runtime;
- `go-binary`: the official Go protobuf runtime;
- `haskell-binary`: `proto-lens`, with decoded values forced to normal form;
- `lean-json`: hand-written instances using Lean's `Lean.Data.Json` AST,
  parser, and compact printer;
- `lean-protojson`: this repository's reflection-based ProtoJSON codec.

`lean-json` is deliberately not called ProtoJSON: its field naming and scalar
mapping are ordinary application JSON choices. The binary comparison is exact:
the runner rejects a sample unless Lean, C++, Go, and Haskell produce identical
bytes.
Every path also checks a stable fingerprint covering every workload field.

## Run

From any directory in the repository:

```bash
Test/Bench/run.sh
```

The chain pins protobuf C++ and `protoc` to 35.0, Go to 1.26.5, the official Go
protobuf module to v1.36.11, GHC to 8.8.4, `cabal-install` to 3.10.3.0,
`proto-lens` to 0.7.1.7, and `proto-lens-runtime` to 0.7.0.8. If
`BENCH_PROTOC` or `PROTOC` names
the pinned compiler version, it is reused; otherwise the runner downloads the
official architecture-specific compiler and Go toolchain and verifies their
SHA-256 checksums. CMake fetches and caches the matching official C++ source
below `.lake/build/bench`; the Go runner builds from the checked-in exact Go
module checksums. Dependency compilation is not part of the measured program.

For a fast chain check:

```bash
BENCH_QUICK=1 Test/Bench/run.sh
```

Useful controls:

```bash
BENCH_SIZES=1,32,256 \
BENCH_REPEATS=7 \
BENCH_MEMORY_REPEATS=5 \
BENCH_TARGET_MS=250 \
BENCH_CPU=auto \
Test/Bench/run.sh
```

- `BENCH_TARGET_MS` calibrates the repeated loop independently for every
  implementation, direction, and message size.
- The default sizes stop at 256 items so the full engineering chain remains
  practical even when a codec has superlinear behavior. Larger stress cases
  remain available explicitly, for example `BENCH_SIZES=1,32,256,2000`.
- `BENCH_CPU=auto` pins all samples to the first CPU allowed by the current
  affinity set. Use an explicit logical CPU or `none` when appropriate.
- `BENCH_OUTPUT_DIR` selects the result directory. By default it is an ignored
  directory below `.lake/build/bench/results/`.
- `BENCH_BUILD_JOBS` controls the one-time C++ build parallelism and defaults
  to 2 to limit peak build memory.
- `BENCH_SEED` controls the reproducible random interleaving of independent
  process samples.

The runner requires Linux, GNU `time`, Python 3, CMake, Ninja, a C++17
compiler, curl, tar, unzip, sha256sum, taskset, and the pinned GHC/Cabal
toolchain. It bootstraps the pinned Go toolchain itself. The CI workflow installs
the pinned Haskell toolchain and caches Cabal dependencies.

## Fixed and growing costs

The output does not fold startup into per-operation throughput:

- `startup` is a separate whole-process run and includes runtime/static
  initialization before `main`;
- `data_setup_ns` constructs the logical workload once;
- `input_setup_ns` constructs a decoder's fixed encoded input once;
- `first_ns` measures the first operation after setup;
- `steady_ns_per_op` measures only repetitions after that first operation.

Time samples use an automatically calibrated repeated loop and independent
process repetitions. Memory samples are different processes that execute
exactly one codec operation, so a slow codec is not assigned a larger peak RSS
merely because its timing loop ran more times.

For memory, `max_rss_kib` is GNU `time`'s process peak RSS. The report shows:

- the runtime-only startup peak;
- the one-operation peak for every workload size;
- the peak delta from the matching runtime startup process;
- an ordinary least-squares RSS slope over the configured item counts.

The slope is an engineering growth estimate, not an allocator-level proof:
page granularity, garbage collection, and process layout can make small deltas
noisy.

## Artifacts

Each run writes:

- `raw.csv`: every independent process sample;
- `summary.csv`: medians and interquartile ranges;
- `metadata.json`: commit and dirty state, all toolchain/runtime versions, CPU model
  and affinity, configuration, calibration counts, and metric definitions;
- `REPORT.md`: fixed-cost, steady-state, memory, and growth tables.

The generated data is machine-specific and intentionally stays under the
ignored `.lake` build tree. The source, pinned dependency versions, commands,
correctness gates, and report generation are the reproducible artifact.

The two modules under `haskell/generated/` were generated from `Perf.proto` by
`proto-lens-protoc` 0.7.0.0 and are checked in so benchmark CI does not spend
most of its time compiling the historical GHC API-based code generator. Any
workload schema change must regenerate those modules and update every runner's
logical content fingerprint; the cross-runtime byte/hash gate will reject a
stale implementation for ordinary workload changes.
