#!/usr/bin/env bash

set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"

readonly protobuf_version="35.0"
readonly protoc_x86_64_sha256="a45cda0989c17dd950db55f6fbe1e5814c50fda08e87aa422980ac1f89dddbbc"
readonly protoc_aarch64_sha256="36b518ac14d90351cc6598228ed2bbe5afe4e357b1af470b07e0ec1609875de2"
readonly go_version="1.26.5"
readonly go_protobuf_version="1.36.11"
readonly ghc_version="8.8.4"
readonly cabal_version="3.10.3.0"
readonly proto_lens_version="0.7.1.7"
readonly proto_lens_runtime_version="0.7.0.8"
readonly go_x86_64_sha256="5c2c3b16caefa1d968a94c1daca04a7ca301a496d9b086e17ad77bb81393f053"
readonly go_aarch64_sha256="fe4789e92b1f33358680864bbe8704289e7bb5fc207d80623c308935bd696d49"

build_root="${BENCH_BUILD_DIR:-$repo_root/.lake/build/bench}"
tool_root="$build_root/toolchain/protoc-$protobuf_version"
go_tool_root="$build_root/toolchain/go-$go_version"
cpp_build="$build_root/cpp"
go_build="$build_root/go"
haskell_build="$build_root/haskell"
haskell_source="$repo_root/Test/Bench/haskell"

for command_name in cabal cmake curl ghc ninja python3 sha256sum tar taskset unzip /usr/bin/time; do
  if ! command -v "$command_name" >/dev/null 2>&1; then
    echo "missing benchmark dependency: $command_name" >&2
    exit 2
  fi
done

if [[ "$(ghc --numeric-version)" != "$ghc_version" ]]; then
  echo "GHC $(ghc --numeric-version) is installed; expected $ghc_version" >&2
  exit 2
fi
if [[ "$(cabal --numeric-version)" != "$cabal_version" ]]; then
  echo "cabal $(cabal --numeric-version) is installed; expected $cabal_version" >&2
  exit 2
fi

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

case "$(uname -m)" in
  x86_64)
    go_arch="amd64"
    go_sha256="$go_x86_64_sha256"
    ;;
  aarch64|arm64)
    go_arch="arm64"
    go_sha256="$go_aarch64_sha256"
    ;;
  *)
    echo "no pinned Go binary for architecture $(uname -m)" >&2
    exit 2
    ;;
esac
go_archive="$go_tool_root/go$go_version.linux-$go_arch.tar.gz"
go_bin="$go_tool_root/go/bin/go"
if [[ ! -f "$go_archive" ]] ||
    [[ "$(sha256sum "$go_archive" | awk '{print $1}')" != "$go_sha256" ]]; then
  mkdir -p "$go_tool_root"
  download="$go_archive.download"
  curl --fail --location --retry 3 \
    "https://go.dev/dl/go$go_version.linux-$go_arch.tar.gz" \
    --output "$download"
  actual_sha256="$(sha256sum "$download" | awk '{print $1}')"
  if [[ "$actual_sha256" != "$go_sha256" ]]; then
    echo "downloaded Go checksum mismatch: $actual_sha256" >&2
    exit 2
  fi
  mv "$download" "$go_archive"
fi
if [[ ! -x "$go_bin" ]]; then
  tar -xzf "$go_archive" -C "$go_tool_root"
fi
case "$("$go_bin" version)" in
  "go version go$go_version "*) ;;
  *)
    echo "pinned Go toolchain failed version check" >&2
    exit 2
    ;;
esac

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

echo "Building Go protobuf $go_protobuf_version benchmark with $($go_bin version)"
go_src="$go_build/src"
go_bin_dir="$go_build/bin"
mkdir -p "$go_src/generated" "$go_bin_dir"
cp Test/Bench/go/go.mod Test/Bench/go/go.sum Test/Bench/go/benchmark.go "$go_src/"
export GOBIN="$go_bin_dir"
export GOMODCACHE="$go_build/modcache"
export GOCACHE="$go_build/cache"
"$go_bin" -C "$go_src" mod download
"$go_bin" install "google.golang.org/protobuf/cmd/protoc-gen-go@v$go_protobuf_version"
"$PROTOC" \
  --proto_path="$repo_root/Test/Bench" \
  --plugin="protoc-gen-go=$go_bin_dir/protoc-gen-go" \
  --go_out="$go_src/generated" \
  --go_opt=paths=source_relative \
  --go_opt=MPerf.proto=protobuf-lean-benchmark/generated\;benchperf \
  "$repo_root/Test/Bench/Perf.proto"
"$go_bin" -C "$go_src" build -trimpath -buildvcs=false \
  -ldflags "-X main.protobufVersion=v$go_protobuf_version" \
  -o "$go_build/benchGoCodec" .

echo "Building Haskell proto-lens $proto_lens_version / runtime $proto_lens_runtime_version benchmark with GHC $ghc_version"
export CABAL_DIR="${BENCH_CABAL_DIR:-$haskell_build/cabal}"
mkdir -p "$CABAL_DIR"
if [[ ! -f "$CABAL_DIR/packages/hackage.haskell.org/01-index.tar" ]]; then
  (
    cd "$haskell_source"
    cabal update
  )
fi
(
  cd "$haskell_source"
  cabal --builddir="$haskell_build/dist" build exe:benchHaskellCodec
)
haskell_exe="$(
  cd "$haskell_source"
  cabal --builddir="$haskell_build/dist" list-bin exe:benchHaskellCodec
)"
expected_haskell_version="proto-lens-$proto_lens_version proto-lens-runtime-$proto_lens_runtime_version ghc-$ghc_version"
if [[ "$($haskell_exe version)" != "$expected_haskell_version" ]]; then
  echo "pinned Haskell benchmark failed version check" >&2
  exit 2
fi

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
  --go "$go_build/benchGoCodec" \
  --haskell "$haskell_exe" \
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
