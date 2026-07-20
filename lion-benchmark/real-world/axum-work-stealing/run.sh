#!/bin/bash
# Work-stealing benchmark: axum service with a CPU-heavy endpoint, Lion
# (thread-per-core) vs Tokio (multi-thread, work-stealing).
#
# Sweeps the coefficient of variation (CV) of per-request CPU cost at a FIXED
# mean, on a FIXED core count. Produces one CSV -> plotted as two panels:
#   left  = p99 latency vs CV,   right = throughput vs CV.
#
# Usage:  ./run.sh
#         CORES=8 MEAN=20000 CVS="0.5 1 2 4 8" DURATION=30 CONNS=64 RUNS=3 ./run.sh
#
# The server is pinned to CORES cores; run wrk on a separate machine (or reserve
# cores) so the load generator does not steal the server's CPU. Keep CONNS so the
# server runs at ~60-70% utilisation (queuing, not saturation).
set -euo pipefail

DIR="$(cd "$(dirname "$0")" && pwd)"

CORES="${CORES:-8}"
MEAN="${MEAN:-20000}"        # mean SHA-256 iters/request (calibrate for target util)
CVS="${CVS:-0.5 1 2 4 8}"
DURATION="${DURATION:-30}"
CONNS="${CONNS:-64}"
WRK_THREADS="${WRK_THREADS:-8}"
RUNS="${RUNS:-3}"
HOST="${HOST:-127.0.0.1}"
PORT="${PORT:-8791}"
URL="http://${HOST}:${PORT}"

OUTDIR="${OUTDIR:-$DIR/results/$(date +%Y%m%d-%H%M%S)}"
mkdir -p "$OUTDIR"
CSV="$OUTDIR/work_stealing.csv"

command -v wrk >/dev/null 2>&1 || { echo "wrk not found — install it (../../setup.sh)"; exit 1; }
command -v taskset >/dev/null 2>&1 || { echo "taskset not found (util-linux)"; exit 1; }

echo "== build =="
(cd "$DIR" && cargo build --release --bin ws-tokio --bin ws-lion 2>&1 | tail -1)
BIN_DIR="$DIR/target/release"

CPUSET="0-$((CORES - 1))"

start_server() {  # $1 = binary
  taskset -c "$CPUSET" "$BIN_DIR/$1" --host 0.0.0.0 --port "$PORT" --cores "$CORES" >"$OUTDIR/$1.log" 2>&1 &
  SRV_PID=$!
  # wait for readiness
  for _ in $(seq 1 50); do
    curl -sf "$URL/health" >/dev/null 2>&1 && return 0
    sleep 0.2
  done
  echo "server $1 failed to start"; cat "$OUTDIR/$1.log"; exit 1
}

stop_server() {
  kill "$SRV_PID" 2>/dev/null || true
  wait "$SRV_PID" 2>/dev/null || true
}

run_wrk() {  # $1 = cv ; echoes "rps,p50,p99"
  WS_MEAN="$MEAN" WS_CV="$1" \
    wrk -t"$WRK_THREADS" -c"$CONNS" -d"${DURATION}s" --latency \
        -s "$DIR/bench/work_cv.lua" "$URL/work" 2>/dev/null \
  | awk '
      /Requests\/sec:/      { rps=$2 }
      /^ *50\.000%/         { p50=$2 }
      /^ *99\.000%/         { p99=$2 }
      END { printf "%s,%s,%s", rps, p50, p99 }'
}

echo "system,runtime,cores,mean,cv,run,rps,p50,p99" > "$CSV"
echo "== sweep (cores=$CORES mean=$MEAN cv={$CVS} ${DURATION}s x $RUNS) =="

for rt in tokio lion; do
  bin="ws-$rt"
  for cv in $CVS; do
    for run in $(seq 1 "$RUNS"); do
      start_server "$bin"
      # warm up
      WS_MEAN="$MEAN" WS_CV="$cv" wrk -t2 -c8 -d5s -s "$DIR/bench/work_cv.lua" "$URL/work" >/dev/null 2>&1 || true
      line="$(run_wrk "$cv")"
      stop_server
      echo "work-stealing,$rt,$CORES,$MEAN,$cv,$run,$line" | tee -a "$CSV"
      sleep 1
    done
  done
done

echo "== done -> $CSV =="
