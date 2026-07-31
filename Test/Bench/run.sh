#!/usr/bin/env bash

set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"

readonly protobuf_version="35.0"
readonly protoc_x86_64_sha256="a45cda0989c17dd950db55f6fbe1e5814c50fda08e87aa422980ac1f89dddbbc"
readonly protoc_aarch64_sha256="36b518ac14d90351cc6598228ed2bbe5afe4e357b1af470b07e0ec1609875de2"

build_root="${BENCH_BUILD_DIR:-$repo_root/.lake/build/bench}"
tool_root="$build_root/toolchain/protoc-$protobuf_version"
cpp_build="$build_root/cpp"

for command_name in cmake curl ninja python3 sha256sum taskset unzip /usr/bin/time; do
  if ! command -v "$command_name" >/dev/null 2>&1; then
    echo "missing benchmark dependency: $command_name" >&2
    exit 2
  fi
done

protoc_path="${BENCH_PROTOC:-${PROTOC:-}}"
if [[ -n "$protoc_path" ]]; then
  actual_version="$("$protoc_path" --version 2>/dev/null || true)"
  if [[ "$actual_version" != "libprotoc $protobuf_version" ]]; then
    echo "BENCH_PROTOC/PROTOC is '$actual_version'; expected libprotoc $protobuf_version" >&2
    exit 2
  fi
elif command -v protoc >/dev/null 2>&1 &&
    [[ "$(protoc --version 2>/dev/null || true)" == "libprotoc $protobuf_version" ]]; then
  protoc_path="$(command -v protoc)"
else
  case "$(uname -m)" in
    x86_64)
      protoc_platform="linux-x86_64"
      protoc_sha256="$protoc_x86_64_sha256"
      ;;
    aarch64|arm64)
      protoc_platform="linux-aarch_64"
      protoc_sha256="$protoc_aarch64_sha256"
      ;;
    *)
      echo "no pinned protoc binary for architecture $(uname -m); set BENCH_PROTOC" >&2
      exit 2
      ;;
  esac
  mkdir -p "$tool_root"
  archive="$tool_root/protoc-$protobuf_version-$protoc_platform.zip"
  if [[ ! -f "$archive" ]] ||
      [[ "$(sha256sum "$archive" | awk '{print $1}')" != "$protoc_sha256" ]]; then
    download="$archive.download"
    curl --fail --location --retry 3 \
      "https://github.com/protocolbuffers/protobuf/releases/download/v$protobuf_version/protoc-$protobuf_version-$protoc_platform.zip" \
      --output "$download"
    actual_sha256="$(sha256sum "$download" | awk '{print $1}')"
    if [[ "$actual_sha256" != "$protoc_sha256" ]]; then
      echo "downloaded protoc checksum mismatch: $actual_sha256" >&2
      exit 2
    fi
    mv "$download" "$archive"
    unzip -q -o "$archive" -d "$tool_root"
  elif [[ ! -x "$tool_root/bin/protoc" ]]; then
    unzip -q -o "$archive" -d "$tool_root"
  fi
  protoc_path="$tool_root/bin/protoc"
fi

export PROTOC="$protoc_path"

echo "Building Lean benchmark with $("$PROTOC" --version)"
lake build benchCodec

echo "Building C++ protobuf $protobuf_version benchmark"
cmake \
  -S Test/Bench/cpp \
  -B "$cpp_build" \
  -G Ninja \
  -DCMAKE_BUILD_TYPE=Release \
  -DBENCH_PROTOBUF_VERSION="$protobuf_version" \
  -DBENCH_PROTOC="$PROTOC"
cmake --build "$cpp_build" --target benchCppCodec \
  --parallel "${BENCH_BUILD_JOBS:-2}"

if [[ "${BENCH_QUICK:-0}" == "1" ]]; then
  default_sizes="1,32"
  default_repeats="2"
  default_memory_repeats="2"
  default_target_ms="20"
else
  default_sizes="1,32,256"
  default_repeats="7"
  default_memory_repeats="5"
  default_target_ms="250"
fi

timestamp="$(date -u +%Y%m%dT%H%M%SZ)"
commit="$(git rev-parse --short HEAD)"
output_dir="${BENCH_OUTPUT_DIR:-$build_root/results/$timestamp-$commit}"

python3 Test/Bench/report.py \
  --lean "$repo_root/.lake/build/bin/benchCodec" \
  --cpp "$cpp_build/benchCppCodec" \
  --protoc "$PROTOC" \
  --repo "$repo_root" \
  --output "$output_dir" \
  --sizes "${BENCH_SIZES:-$default_sizes}" \
  --repeats "${BENCH_REPEATS:-$default_repeats}" \
  --memory-repeats "${BENCH_MEMORY_REPEATS:-$default_memory_repeats}" \
  --target-ms "${BENCH_TARGET_MS:-$default_target_ms}" \
  --max-iterations "${BENCH_MAX_ITERATIONS:-1000000}" \
  --seed "${BENCH_SEED:-20260731}" \
  --cpu "${BENCH_CPU:-auto}"
