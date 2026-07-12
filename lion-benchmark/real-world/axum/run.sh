#!/bin/bash
# Axum static-file-server benchmark — Lion (verified runtime) vs Tokio.
# Portable: paths relative to this script; topology from ../hosts.env or env;
# shared orchestration in ../lib/bench_common.sh. Per-run raw CSV (repo policy: per-run raw retained).
#
# Measures throughput (req/s) serving files, each runtime in turn, across the
# small/large/mixed wrk workloads (lua scripts in src/benchmark/). Local by
# default; set CLIENT_HOST / use ../lib/remote_launch.sh for cross-machine.
#
# Usage:  ./run.sh          # DURATION=30s x RUNS=10
#         DURATION=5 RUNS=2 CONNS=50 ./run.sh
set -euo pipefail

DIR="$(cd "$(dirname "$0")" && pwd)"
# shellcheck disable=SC1091
. "$DIR/../lib/bench_common.sh"
bench_setup "$DIR"
require_client_tool wrk
DURATION="${DURATION:-30}"

PORT="${PORT:-8788}"
CONNS="${CONNS:-50}"
ROOT="${BENCH_ROOT:-/tmp/axum-bench-files}"
LUA_DIR="$DIR/src/benchmark"
LION_T="$(bench_target_dir "$DIR/src/lion-axum")"
TOKIO_T="$(bench_target_dir "$DIR/src/tokio-axum")"
LION="$LION_T/release/axum-fileserver"
TOKIO="$TOKIO_T/release/axum-fileserver"
RAW="$OUTDIR/axum_raw.csv"

command -v wrk >/dev/null 2>&1 || { echo "wrk not found — run ../../setup.sh" >&2; exit 1; }

echo "== build =="
(cd "$DIR/src/tokio-axum" && CARGO_TARGET_DIR="$TOKIO_T" cargo build --release 2>&1 | tail -1)
(cd "$DIR/src/lion-axum" && CARGO_TARGET_DIR="$LION_T" cargo build --release 2>&1 | tail -1)

# test files
if [ ! -d "$ROOT/small" ]; then
  echo "== creating test files in $ROOT =="
  mkdir -p "$ROOT/small" "$ROOT/large"
  for i in $(seq 1 100); do dd if=/dev/urandom of="$ROOT/small/f${i}.bin" bs=4096 count=1 2>/dev/null; done
  for i in $(seq 1 100); do dd if=/dev/urandom of="$ROOT/large/f${i}.bin" bs=1024 count=64 2>/dev/null; done
fi

pkill -x axum-fileserver 2>/dev/null || true
sleep 1

WORKLOADS="${WORKLOADS:-small large mixed}"
echo "system,runtime,workload,conns,run,rps,latency" > "$RAW"
echo "== run (server=$SERVER_HOST client=$CLIENT_HOST ${DURATION}s x ${RUNS}) =="
# The paper measures axum in BOTH deployments: cross-machine (bandwidth-bound
# sanity rows) and localhost (the rows that expose runtime differences).
# deployment=cross drives wrk from CLIENT_HOST; deployment=local runs wrk on
# this machine against 127.0.0.1. Interleaved A-B protocol in both (run outer,
# runtime inner, server restart per cell).
RAW_LOCAL="$OUTDIR/axum_local_raw.csv"
echo "system,runtime,workload,conns,run,rps,latency" > "$RAW_LOCAL"
# DEPLOYMENTS knob: run a subset (e.g. DEPLOYMENTS=local to (re)collect only
# the localhost rows). Default = both, the paper protocol.
DEPLOYMENTS="${DEPLOYMENTS:-cross local}"
for deployment in $DEPLOYMENTS; do
  for r in $(seq 1 "$RUNS"); do
    for rt in tokio lion; do
      [ "$rt" = tokio ] && BIN="$TOKIO" || BIN="$LION"
      server_start "/tmp/axum_$rt.log" "$BIN" --host 0.0.0.0 --port "$PORT" --root "$ROOT"
      sleep 3
      if ! curl -s -m 3 "http://127.0.0.1:$PORT/small/f1.bin" >/dev/null 2>&1; then
        echo "  $rt: server not ready ($(tail -1 /tmp/axum_$rt.log))"; server_stop; continue
      fi
      for wl in $WORKLOADS; do
        lua="$LUA_DIR/$wl.lua"; [ -f "$lua" ] || lua=""
        if [ "$deployment" = cross ]; then
          target="http://$SERVER_HOST:$PORT"; sink="$RAW"
          if [ -n "$lua" ]; then
            out=$(on_client wrk -t2 -c"$CONNS" -d"${DURATION}s" -s "$lua" "$target" 2>&1)
          else
            out=$(on_client wrk -t2 -c"$CONNS" -d"${DURATION}s" "$target/small/f1.bin" 2>&1)
          fi
        else
          target="http://127.0.0.1:$PORT"; sink="$RAW_LOCAL"
          if [ -n "$lua" ]; then
            out=$(wrk -t2 -c"$CONNS" -d"${DURATION}s" -s "$lua" "$target" 2>&1)
          else
            out=$(wrk -t2 -c"$CONNS" -d"${DURATION}s" "$target/small/f1.bin" 2>&1)
          fi
        fi
        rps=$(echo "$out" | awk '/Requests\/sec/{print $2}')
        lat=$(echo "$out" | awk '/Latency/{print $2; exit}')
        echo "axum,$rt,$wl,$CONNS,$r,${rps:-0},${lat:-0}" | tee -a "$sink"
      done
      server_stop; sleep 2
    done
  done
done
echo "== summary (cross-machine) =="
cat "$(summarize_raw "$RAW" 6 axum)"
echo "== summary (localhost — the paper's Axum-local rows) =="
cat "$(summarize_raw "$RAW_LOCAL" 6 axum)"
