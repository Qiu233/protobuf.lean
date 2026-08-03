#!/usr/bin/env python3
"""Run the reproducible engineering benchmark and write raw/summary reports."""

from __future__ import annotations

import argparse
import csv
import dataclasses
import datetime as dt
import json
import math
import os
import pathlib
import random
import shlex
import statistics
import subprocess
import tempfile
import time
from collections import defaultdict
from typing import Iterable, Sequence


IMPLEMENTATIONS = (
    "lean-binary",
    "cpp-binary",
    "go-binary",
    "haskell-binary",
    "lean-json",
    "lean-protojson",
)
OPERATIONS = ("encode", "decode")
NUMERIC_RESULT_FIELDS = (
    "items",
    "iterations",
    "data_setup_ns",
    "input_setup_ns",
    "first_ns",
    "steady_ns",
    "steady_ns_per_op",
    "output_bytes",
    "content_hash",
    "output_hash",
    "checksum",
    "validation",
)
RAW_FIELDS = (
    "phase",
    "sample",
    "implementation",
    "operation",
    *NUMERIC_RESULT_FIELDS,
    "wall_ns",
    "user_seconds",
    "system_seconds",
    "max_rss_kib",
    "minor_faults",
    "major_faults",
    "cpu",
    "command",
)


@dataclasses.dataclass(frozen=True)
class Case:
    implementation: str
    operation: str
    items: int


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--lean", required=True, type=pathlib.Path)
    parser.add_argument("--cpp", required=True, type=pathlib.Path)
    parser.add_argument("--go", required=True, type=pathlib.Path)
    parser.add_argument("--haskell", required=True, type=pathlib.Path)
    parser.add_argument("--protoc", required=True, type=pathlib.Path)
    parser.add_argument("--repo", required=True, type=pathlib.Path)
    parser.add_argument("--output", required=True, type=pathlib.Path)
    parser.add_argument("--sizes", default="1,32,256")
    parser.add_argument("--repeats", type=int, default=7)
    parser.add_argument("--memory-repeats", type=int, default=5)
    parser.add_argument("--target-ms", type=float, default=250.0)
    parser.add_argument("--max-iterations", type=int, default=1_000_000)
    parser.add_argument("--seed", type=int, default=20260731)
    parser.add_argument(
        "--cpu",
        default="auto",
        help="logical CPU number, auto (first allowed CPU), or none",
    )
    return parser.parse_args()


def parse_sizes(value: str) -> list[int]:
    sizes = [int(part) for part in value.split(",") if part]
    if not sizes or any(size < 0 for size in sizes):
        raise ValueError("--sizes must be a comma-separated list of nonnegative integers")
    if len(set(sizes)) != len(sizes):
        raise ValueError("--sizes contains duplicates")
    return sorted(sizes)


def choose_cpu(value: str) -> int | None:
    if value == "none":
        return None
    allowed = sorted(os.sched_getaffinity(0))
    if not allowed:
        raise RuntimeError("the process has an empty CPU affinity set")
    cpu = allowed[0] if value == "auto" else int(value)
    if cpu not in allowed:
        raise RuntimeError(f"CPU {cpu} is not in the allowed affinity set {allowed}")
    return cpu


def executable_command(
    args: argparse.Namespace,
    implementation: str,
    operation: str,
    items: int,
    iterations: int,
    validate: bool,
) -> list[str]:
    external_executables = {
        "cpp-binary": args.cpp,
        "go-binary": args.go,
        "haskell-binary": args.haskell,
    }
    if implementation in external_executables:
        executable = external_executables[implementation]
        return [
            str(executable),
            operation,
            str(items),
            str(iterations),
            "1" if validate else "0",
        ]
    return [
        str(args.lean),
        implementation,
        operation,
        str(items),
        str(iterations),
        "1" if validate else "0",
    ]


def startup_command(args: argparse.Namespace, runtime: str) -> list[str]:
    executables = {
        "lean-runtime": args.lean,
        "cpp-runtime": args.cpp,
        "go-runtime": args.go,
        "haskell-runtime": args.haskell,
    }
    executable = executables[runtime]
    return [str(executable), "startup"]


def parse_key_values(line: str, prefix: str) -> dict[str, str]:
    if not line.startswith(prefix):
        raise RuntimeError(f"expected output beginning with {prefix!r}, got {line!r}")
    values: dict[str, str] = {}
    for token in shlex.split(line[len(prefix) :].strip()):
        key, separator, value = token.partition("=")
        if not separator:
            raise RuntimeError(f"malformed result token {token!r}")
        values[key] = value
    return values


def run_measured(
    command: Sequence[str],
    phase: str,
    sample: int,
    cpu: int | None,
) -> dict[str, object]:
    measured_command = list(command)
    if cpu is not None:
        measured_command = ["taskset", "-c", str(cpu), *measured_command]

    with tempfile.NamedTemporaryFile(mode="w+", encoding="utf-8") as usage_file:
        timed_command = [
            "/usr/bin/time",
            "-f",
            "user_seconds=%U system_seconds=%S max_rss_kib=%M minor_faults=%R major_faults=%F",
            "-o",
            usage_file.name,
            "--",
            *measured_command,
        ]
        start = time.monotonic_ns()
        completed = subprocess.run(
            timed_command,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            check=False,
        )
        stop = time.monotonic_ns()
        usage_file.seek(0)
        usage_text = usage_file.read().strip()

    if completed.returncode != 0:
        raise RuntimeError(
            f"benchmark command failed ({completed.returncode}): "
            f"{shlex.join(command)}\nstdout:\n{completed.stdout}\nstderr:\n{completed.stderr}"
        )
    result_lines = [
        line for line in completed.stdout.splitlines() if line.startswith("BENCH_RESULT ")
    ]
    if len(result_lines) != 1:
        raise RuntimeError(
            f"expected one BENCH_RESULT line from {shlex.join(command)}, "
            f"got {len(result_lines)}:\n{completed.stdout}"
        )

    result = parse_key_values(result_lines[0], "BENCH_RESULT ")
    usage = parse_key_values(usage_text, "")
    row: dict[str, object] = {
        "phase": phase,
        "sample": sample,
        "implementation": result["implementation"],
        "operation": result["operation"],
        "wall_ns": stop - start,
        "user_seconds": float(usage["user_seconds"]),
        "system_seconds": float(usage["system_seconds"]),
        "max_rss_kib": int(usage["max_rss_kib"]),
        "minor_faults": int(usage["minor_faults"]),
        "major_faults": int(usage["major_faults"]),
        "cpu": "none" if cpu is None else cpu,
        "command": shlex.join(command),
    }
    for field in NUMERIC_RESULT_FIELDS:
        row[field] = int(result[field])
    return row


def percentile(values: Sequence[float], fraction: float) -> float:
    ordered = sorted(values)
    if len(ordered) == 1:
        return ordered[0]
    position = (len(ordered) - 1) * fraction
    lower = math.floor(position)
    upper = math.ceil(position)
    if lower == upper:
        return ordered[lower]
    weight = position - lower
    return ordered[lower] * (1.0 - weight) + ordered[upper] * weight


def median(rows: Sequence[dict[str, object]], field: str) -> float:
    return statistics.median(float(row[field]) for row in rows)


def linear_fit(points: Sequence[tuple[float, float]]) -> tuple[float, float]:
    if len(points) < 2:
        return (points[0][1] if points else 0.0, 0.0)
    mean_x = statistics.fmean(point[0] for point in points)
    mean_y = statistics.fmean(point[1] for point in points)
    denominator = sum((x - mean_x) ** 2 for x, _ in points)
    if denominator == 0:
        return mean_y, 0.0
    slope = sum((x - mean_x) * (y - mean_y) for x, y in points) / denominator
    return mean_y - slope * mean_x, slope


def group_rows(
    rows: Iterable[dict[str, object]],
) -> dict[tuple[str, str, str, int], list[dict[str, object]]]:
    grouped: dict[tuple[str, str, str, int], list[dict[str, object]]] = defaultdict(list)
    for row in rows:
        key = (
            str(row["phase"]),
            str(row["implementation"]),
            str(row["operation"]),
            int(row["items"]),
        )
        grouped[key].append(row)
    return dict(grouped)


def check_results(rows: Sequence[dict[str, object]], sizes: Sequence[int]) -> None:
    workload_rows = [row for row in rows if row["operation"] != "startup"]
    for size in sizes:
        at_size = [row for row in workload_rows if row["items"] == size]
        content_hashes = {row["content_hash"] for row in at_size}
        if len(content_hashes) != 1:
            raise RuntimeError(
                f"implementations constructed different logical messages at size {size}: "
                f"{sorted(content_hashes)}"
            )
        for implementation in IMPLEMENTATIONS:
            implementation_rows = [
                row for row in at_size if row["implementation"] == implementation
            ]
            output_hashes = {row["output_hash"] for row in implementation_rows}
            output_sizes = {row["output_bytes"] for row in implementation_rows}
            if len(output_hashes) != 1 or len(output_sizes) != 1:
                raise RuntimeError(
                    f"{implementation} encode/decode inputs differ at size {size}"
                )
        binary_rows = [
            row
            for row in at_size
            if row["implementation"]
            in ("lean-binary", "cpp-binary", "go-binary", "haskell-binary")
        ]
        binary_hashes = {row["output_hash"] for row in binary_rows}
        binary_sizes = {row["output_bytes"] for row in binary_rows}
        if len(binary_hashes) != 1 or len(binary_sizes) != 1:
            raise RuntimeError(
                f"Lean, C++, Go, and Haskell binary protobuf bytes differ at size {size}"
            )


def capture(command: Sequence[str], cwd: pathlib.Path) -> str:
    completed = subprocess.run(
        command,
        cwd=cwd,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        check=False,
    )
    return completed.stdout.strip()


def cpu_model() -> str:
    try:
        for line in pathlib.Path("/proc/cpuinfo").read_text().splitlines():
            if line.startswith("model name"):
                return line.partition(":")[2].strip()
    except OSError:
        pass
    return "unknown"


def write_metadata(
    args: argparse.Namespace,
    sizes: Sequence[int],
    cpu: int | None,
    iterations: dict[Case, int],
) -> None:
    metadata = {
        "generated_at_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
        "repository": str(args.repo),
        "git_commit": capture(["git", "rev-parse", "HEAD"], args.repo),
        "git_status": capture(["git", "status", "--short"], args.repo),
        "lean_version": capture(["lake", "env", "lean", "--version"], args.repo),
        "protoc_version": capture([str(args.protoc), "--version"], args.repo),
        "cpp_runtime_version": capture([str(args.cpp), "version"], args.repo),
        "go_runtime_version": capture([str(args.go), "version"], args.repo),
        "haskell_runtime_version": capture(
            [str(args.haskell), "version"], args.repo
        ),
        "cpp_compiler": capture(["c++", "--version"], args.repo).splitlines()[0],
        "kernel": capture(["uname", "-a"], args.repo),
        "cpu_model": cpu_model(),
        "allowed_cpus": sorted(os.sched_getaffinity(0)),
        "pinned_cpu": cpu,
        "sizes": list(sizes),
        "time_repeats": args.repeats,
        "memory_repeats": args.memory_repeats,
        "target_steady_ms": args.target_ms,
        "max_iterations": args.max_iterations,
        "random_seed": args.seed,
        "calibrated_iterations": {
            f"{case.implementation}/{case.operation}/{case.items}": count
            for case, count in sorted(
                iterations.items(),
                key=lambda item: (
                    item[0].implementation,
                    item[0].operation,
                    item[0].items,
                ),
            )
        },
        "metric_definitions": {
            "startup": "whole-process runtime initialization measured by an outer process timer",
            "data_setup_ns": "construct the logical Batch once inside main",
            "input_setup_ns": "encode the fixed input once for a decode benchmark",
            "first_ns": "first codec operation after setup",
            "steady_ns_per_op": "repeated codec loop after the first operation",
            "max_rss_kib": "GNU time maximum resident set size for a dedicated process",
            "memory_delta": "workload max RSS minus the matching runtime startup max RSS",
        },
    }
    (args.output / "metadata.json").write_text(
        json.dumps(metadata, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def write_raw(args: argparse.Namespace, rows: Sequence[dict[str, object]]) -> None:
    with (args.output / "raw.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=RAW_FIELDS, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(rows)


def write_summary(
    args: argparse.Namespace,
    grouped: dict[tuple[str, str, str, int], list[dict[str, object]]],
) -> None:
    fields = (
        "phase",
        "implementation",
        "operation",
        "items",
        "samples",
        "iterations",
        "data_setup_ns_median",
        "input_setup_ns_median",
        "first_ns_median",
        "steady_ns_per_op_median",
        "steady_ns_per_item_median",
        "steady_ns_per_op_q1",
        "steady_ns_per_op_q3",
        "output_bytes",
        "wall_ns_median",
        "max_rss_kib_median",
        "max_rss_kib_q1",
        "max_rss_kib_q3",
    )
    with (args.output / "summary.csv").open(
        "w", newline="", encoding="utf-8"
    ) as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for key, rows in sorted(grouped.items()):
            phase, implementation, operation, items = key
            steady = [float(row["steady_ns_per_op"]) for row in rows]
            rss = [float(row["max_rss_kib"]) for row in rows]
            writer.writerow(
                {
                    "phase": phase,
                    "implementation": implementation,
                    "operation": operation,
                    "items": items,
                    "samples": len(rows),
                    "iterations": int(median(rows, "iterations")),
                    "data_setup_ns_median": round(median(rows, "data_setup_ns")),
                    "input_setup_ns_median": round(median(rows, "input_setup_ns")),
                    "first_ns_median": round(median(rows, "first_ns")),
                    "steady_ns_per_op_median": round(statistics.median(steady)),
                    "steady_ns_per_item_median": round(
                        statistics.median(steady) / items if items else 0
                    ),
                    "steady_ns_per_op_q1": round(percentile(steady, 0.25)),
                    "steady_ns_per_op_q3": round(percentile(steady, 0.75)),
                    "output_bytes": round(median(rows, "output_bytes")),
                    "wall_ns_median": round(median(rows, "wall_ns")),
                    "max_rss_kib_median": round(statistics.median(rss)),
                    "max_rss_kib_q1": round(percentile(rss, 0.25)),
                    "max_rss_kib_q3": round(percentile(rss, 0.75)),
                }
            )


def fmt_ms(ns: float) -> str:
    return f"{ns / 1_000_000:.3f}"


def fmt_us(ns: float) -> str:
    return f"{ns / 1000:.3f}"


def fmt_mib(kib: float) -> str:
    return f"{kib / 1024:.2f}"


def write_report(
    args: argparse.Namespace,
    sizes: Sequence[int],
    grouped: dict[tuple[str, str, str, int], list[dict[str, object]]],
) -> None:
    lines = [
        "# Protobuf engineering benchmark",
        "",
        "The tables deliberately separate process/runtime startup, one-time data/input setup,",
        "the first codec call, and the repeated steady-state operation. Memory cases execute",
        "one codec operation in a dedicated process; time-loop iteration counts therefore do",
        "not affect the reported peak RSS.",
        "",
        "## Runtime startup (fixed process cost)",
        "",
        "| Runtime | Wall ms | Peak RSS MiB |",
        "|---|---:|---:|",
    ]
    startup_rss: dict[str, float] = {}
    for runtime in (
        "lean-runtime",
        "cpp-runtime",
        "go-runtime",
        "haskell-runtime",
    ):
        rows = grouped[("startup", runtime, "startup", 0)]
        rss = median(rows, "max_rss_kib")
        startup_rss[runtime] = rss
        lines.append(
            f"| {runtime} | {fmt_ms(median(rows, 'wall_ns'))} | {fmt_mib(rss)} |"
        )

    for operation in OPERATIONS:
        lines.extend(
            [
                "",
                f"## {operation.capitalize()} time",
                "",
                "| Items | Implementation | Data setup ms | Input setup ms | First ms | "
                "Steady µs/op | Steady IQR µs/op | Steady µs/item | "
                "Relative latency | Output bytes |",
                "|---:|---|---:|---:|---:|---:|---:|---:|---:|---:|",
            ]
        )
        for size in sizes:
            binary_rows = grouped[("time", "lean-binary", operation, size)]
            binary_steady = median(binary_rows, "steady_ns_per_op")
            for implementation in IMPLEMENTATIONS:
                rows = grouped[("time", implementation, operation, size)]
                steady = [float(row["steady_ns_per_op"]) for row in rows]
                steady_median = statistics.median(steady)
                per_item = (
                    f"{steady_median / size / 1000:.3f}" if size else "n/a"
                )
                lines.append(
                    f"| {size} | {implementation} | "
                    f"{fmt_ms(median(rows, 'data_setup_ns'))} | "
                    f"{fmt_ms(median(rows, 'input_setup_ns'))} | "
                    f"{fmt_ms(median(rows, 'first_ns'))} | "
                    f"{fmt_us(steady_median)} | "
                    f"{fmt_us(percentile(steady, 0.25))}–"
                    f"{fmt_us(percentile(steady, 0.75))} | "
                    f"{per_item} | "
                    f"{steady_median / binary_steady:.2f}× | "
                    f"{round(median(rows, 'output_bytes'))} |"
                )

        lines.extend(
            [
                "",
                f"## {operation.capitalize()} memory",
                "",
                "| Items | Implementation | Peak RSS MiB | Runtime-baseline delta MiB | "
                "Delta KiB/item |",
                "|---:|---|---:|---:|---:|",
            ]
        )
        for size in sizes:
            for implementation in IMPLEMENTATIONS:
                rows = grouped[("memory", implementation, operation, size)]
                rss = median(rows, "max_rss_kib")
                runtime = {
                    "cpp-binary": "cpp-runtime",
                    "go-binary": "go-runtime",
                    "haskell-binary": "haskell-runtime",
                }.get(implementation, "lean-runtime")
                delta = rss - startup_rss[runtime]
                delta_per_item = f"{delta / size:+.3f}" if size else "n/a"
                lines.append(
                    f"| {size} | {implementation} | {fmt_mib(rss)} | "
                    f"{delta / 1024:+.2f} | {delta_per_item} |"
                )

    lines.extend(
        [
            "",
            "## Growth estimates",
            "",
            "Ordinary least-squares fits over the configured item counts. The intercept is a",
            "diagnostic rather than a literal zero-item cost; the measured startup and first-call",
            "tables above are the authoritative fixed-cost measurements.",
            "",
            "| Operation | Implementation | Time intercept ms | Time slope µs/item | "
            "RSS intercept MiB | RSS slope KiB/item |",
            "|---|---|---:|---:|---:|---:|",
        ]
    )
    for operation in OPERATIONS:
        for implementation in IMPLEMENTATIONS:
            time_points = []
            rss_points = []
            for size in sizes:
                time_rows = grouped[("time", implementation, operation, size)]
                memory_rows = grouped[("memory", implementation, operation, size)]
                time_points.append((size, median(time_rows, "steady_ns_per_op")))
                rss_points.append((size, median(memory_rows, "max_rss_kib")))
            time_intercept, time_slope = linear_fit(time_points)
            rss_intercept, rss_slope = linear_fit(rss_points)
            lines.append(
                f"| {operation} | {implementation} | "
                f"{fmt_ms(time_intercept)} | {time_slope / 1000:.3f} | "
                f"{fmt_mib(rss_intercept)} | {rss_slope:.3f} |"
            )

    lines.extend(
        [
            "",
            "## Reproduction and interpretation",
            "",
            "- `raw.csv` contains every independent process sample.",
            "- `summary.csv` contains medians and interquartile ranges.",
            "- `metadata.json` records the commit, dirty state, toolchain, CPU affinity,",
            "  calibration, and metric definitions.",
            "- `lean-json` is the hand-written `Lean.Data.Json` AST baseline; it is not",
            "  ProtoJSON. `lean-protojson` is this repository's reflection-based ProtoJSON.",
            "- Binary Lean, C++, Go, and Haskell output hashes and sizes are checked for",
            "  exact equality.",
            "  Every codec also validates a full-field logical content fingerprint outside",
            "  the timed region.",
            "",
        ]
    )
    (args.output / "REPORT.md").write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    args = parse_args()
    sizes = parse_sizes(args.sizes)
    if args.repeats <= 0 or args.memory_repeats <= 0:
        raise ValueError("repeat counts must be positive")
    if args.target_ms <= 0:
        raise ValueError("--target-ms must be positive")
    cpu = choose_cpu(args.cpu)
    args.output.mkdir(parents=True, exist_ok=True)

    cases = [
        Case(implementation, operation, items)
        for items in sizes
        for operation in OPERATIONS
        for implementation in IMPLEMENTATIONS
    ]

    print("Calibrating and validating every implementation/case...", flush=True)
    iterations: dict[Case, int] = {}
    pilot_rows: list[dict[str, object]] = []
    for index, case in enumerate(cases):
        row = run_measured(
            executable_command(
                args,
                case.implementation,
                case.operation,
                case.items,
                1,
                True,
            ),
            "pilot",
            index,
            cpu,
        )
        pilot_rows.append(row)
        per_operation = max(int(row["steady_ns_per_op"]), 1)
        count = math.ceil(args.target_ms * 1_000_000 / per_operation)
        iterations[case] = max(1, min(count, args.max_iterations))
    check_results(pilot_rows, sizes)

    jobs: list[tuple[str, int, list[str]]] = []
    for sample in range(args.repeats):
        jobs.append(("startup", sample, startup_command(args, "lean-runtime")))
        jobs.append(("startup", sample, startup_command(args, "cpp-runtime")))
        jobs.append(("startup", sample, startup_command(args, "go-runtime")))
        jobs.append(("startup", sample, startup_command(args, "haskell-runtime")))
        for case in cases:
            jobs.append(
                (
                    "time",
                    sample,
                    executable_command(
                        args,
                        case.implementation,
                        case.operation,
                        case.items,
                        iterations[case],
                        True,
                    ),
                )
            )
    for sample in range(args.memory_repeats):
        for case in cases:
            jobs.append(
                (
                    "memory",
                    sample,
                    executable_command(
                        args,
                        case.implementation,
                        case.operation,
                        case.items,
                        0,
                        False,
                    ),
                )
            )

    random.Random(args.seed).shuffle(jobs)
    rows: list[dict[str, object]] = []
    for index, (phase, sample, command) in enumerate(jobs, start=1):
        print(f"\rRunning sample {index}/{len(jobs)}", end="", flush=True)
        rows.append(run_measured(command, phase, sample, cpu))
    print()

    check_results(rows, sizes)
    rows.sort(
        key=lambda row: (
            str(row["phase"]),
            str(row["implementation"]),
            str(row["operation"]),
            int(row["items"]),
            int(row["sample"]),
        )
    )
    grouped = group_rows(rows)
    write_raw(args, rows)
    write_summary(args, grouped)
    write_metadata(args, sizes, cpu, iterations)
    write_report(args, sizes, grouped)
    print(f"Results written to {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
