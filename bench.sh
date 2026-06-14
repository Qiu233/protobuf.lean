#!/usr/bin/env bash

set -euo pipefail

BIN_DIR="${BIN_DIR:-.lake/build/bin}"
ITEMS="${1:-2000}"
ITERS="${2:-200}"
PROTO_ITERS="${PROTO_ITERS:-$ITERS}"
JSON_ITERS="${JSON_ITERS:-${3:-$ITERS}}"

if command -v /usr/bin/time >/dev/null 2>&1; then
  BENCH_MODE="time"
elif command -v perf >/dev/null 2>&1; then
  BENCH_MODE="perf"
else
  BENCH_MODE="none"
fi

run_bench() {
  local name="$1"
  shift
  local out_file err_file summary elapsed
  out_file="$(mktemp)"
  err_file="$(mktemp)"
  case "$BENCH_MODE" in
    time)
      /usr/bin/time -f 'elapsed_seconds=%e' "$@" >"$out_file" 2>"$err_file"
      elapsed="$(sed -n 's/^elapsed_seconds=//p' "$err_file" | tail -n 1)"
      ;;
    perf)
      perf stat -x, -e task-clock "$@" >"$out_file" 2>"$err_file"
      elapsed="$(
        awk -F, '$3 ~ /^task-clock/ {
          if ($2 == "msec") printf "%.6f", $1 / 1000;
          else if ($2 == "sec") printf "%.6f", $1;
        }' "$err_file" | tail -n 1
      )"
      ;;
    *)
      "$@" >"$out_file" 2>"$err_file"
      elapsed="n/a"
      ;;
  esac
  summary="$(tr '\n' ' ' <"$out_file" | sed 's/[[:space:]]\+/ /g; s/^ //; s/ $//')"
  rm -f "$out_file" "$err_file"
  printf '%-16s elapsed_s=%s %s\n' "$name" "${elapsed:-unknown}" "$summary"
}

lake build benchProtoEncode benchProtoDecode benchJsonEncode benchJsonDecode

echo "items=$ITEMS proto_iters=$PROTO_ITERS json_iters=$JSON_ITERS mode=$BENCH_MODE"
echo

run_bench "protobuf encode" "$BIN_DIR/benchProtoEncode" "$ITEMS" "$PROTO_ITERS"
run_bench "protobuf decode" "$BIN_DIR/benchProtoDecode" "$ITEMS" "$PROTO_ITERS"
run_bench "json encode" "$BIN_DIR/benchJsonEncode" "$ITEMS" "$JSON_ITERS"
run_bench "json decode" "$BIN_DIR/benchJsonDecode" "$ITEMS" "$JSON_ITERS"
