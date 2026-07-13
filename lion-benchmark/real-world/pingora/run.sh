#!/bin/bash
# Pingora HTTP reverse-proxy benchmark — Lion (verified runtime) vs Tokio.
# Portable: paths resolve relative to this script; topology (hosts) comes from
# ../hosts.env or env vars; shared orchestration is ../lib/bench_common.sh. Every
# run is recorded to a per-run raw CSV (repo policy: per-run raw retained); a trimmed summary follows.
#
# Measures throughput (req/s) of the HTTP echo service across a connection sweep,
# both runtimes under a single-threaded config.
#
# CANONICAL TOPOLOGY: LOCAL (server + wrk on this host). This benchmark is
# pinned to the single-host setup — the reference dataset and the paper's
# pingora rows are local measurements; any hosts.env cross-machine topology
# is ignored here unless ALLOW_CROSS=1 is set explicitly.
#
# Usage:
#   ./run.sh                       # DURATION=10s x RUNS=10, conns 50 200 + payload10k
#   DURATION=3 RUNS=2 ./run.sh     # quick smoke
#   CONNS="10 100 500" ./run.sh    # custom connection sweep
set -euo pipefail

DIR="$(cd "$(dirname "$0")" && pwd)"
# shellcheck disable=SC1091
. "$DIR/../lib/bench_common.sh"
bench_setup "$DIR"
if [ "${ALLOW_CROSS:-0}" != "1" ]; then
  SERVER_HOST=127.0.0.1
  CLIENT_HOST=127.0.0.1
fi
require_client_tool wrk

PORT="${PORT:-6145}"
# ${VAR-default} (no colon): an explicitly EMPTY value skips that sweep,
# only an unset variable falls back to the default.
CONNS="${CONNS-50 200}"
# Large-payload workload: a 10 KB POST body the echo app returns verbatim
# (the paper table's "Large-10KB" row), run at PAYLOAD_CONNS connections.
# Set PAYLOAD_CONNS="" to skip. Like axum's lua workloads, the script path
# must resolve on the client host (same repo path there).
PAYLOAD_CONNS="${PAYLOAD_CONNS-50}"
PAYLOAD_LUA="$DIR/src/benchmark/post10k.lua"
LION_T="$(bench_target_dir "$DIR/src/lion-pingora")"
TOKIO_T="$(bench_target_dir "$DIR/src/tokio-pingora")"
LION="$LION_T/release/examples/server"
TOKIO="$TOKIO_T/release/examples/server"
RAW="$OUTDIR/pingora_raw.csv"

command -v wrk >/dev/null 2>&1 || { echo "wrk not found — run ../../setup.sh" >&2; exit 1; }

echo "== build =="
(cd "$DIR/src/tokio-pingora" && CARGO_TARGET_DIR="$TOKIO_T" cargo build --release --example server -p pingora 2>&1 | tail -1)
(cd "$DIR/src/lion-pingora"  && CARGO_TARGET_DIR="$LION_T" cargo build --release --example server -p pingora 2>&1 | tail -1)

# grace/shutdown windows pinned to 1s: the default graceful drain waits ~5
# minutes on SIGTERM, which dominated wall time (5 min dead time per cell
# under the interleaved per-cell server lifecycle).
cat > /tmp/pingora_bench.yaml <<'EOF'
---
version: 1
threads: 1
work_stealing: false
grace_period_seconds: 1
graceful_shutdown_timeout_seconds: 1
EOF

# clear any orphaned 'server' processes from prior/interrupted runs (they bind the
# example's ports and would otherwise be measured instead of this run's server).
# pkill -x matches comm exactly ('server') — never the shell/wrk, unlike pkill -f.
pkill -x server 2>/dev/null || true
sleep 1

echo "system,runtime,workload,conns,run,rps,latency" > "$RAW"
echo "== run (server=$SERVER_HOST client=$CLIENT_HOST ${DURATION}s x ${RUNS}, conns: $CONNS) =="
# Interleaved A-B protocol: the run index is the OUTER loop so slow drift in
# machine state (thermal, cache, neighbors) averages across both runtimes
# instead of biasing whichever arm ran last. Server restarts per (run,runtime).
for r in $(seq 1 "$RUNS"); do
  for rt in tokio lion; do
    [ "$rt" = tokio ] && BIN="$TOKIO" || BIN="$LION"
    server_start "/tmp/srv_$rt.log" "$BIN" -c /tmp/pingora_bench.yaml
    sleep 4
    if ! curl -s -m 3 "http://$SERVER_HOST:$PORT" -d ping >/dev/null 2>&1; then
      echo "  $rt: server not ready ($(tail -1 /tmp/srv_$rt.log))"; server_stop; continue
    fi
    for c in $CONNS; do
      out=$(on_client wrk -t2 -c"$c" -d"${DURATION}s" "http://$SERVER_HOST:$PORT" 2>&1)
      rps=$(echo "$out" | awk '/Requests\/sec/{print $2}')
      lat=$(echo "$out" | awk '/Latency/{print $2; exit}')
      echo "pingora,$rt,conns$c,$c,$r,${rps:-0},${lat:-0}" | tee -a "$RAW"
    done
    if [ -n "$PAYLOAD_CONNS" ]; then
      out=$(on_client wrk -t2 -c"$PAYLOAD_CONNS" -d"${DURATION}s" -s "$PAYLOAD_LUA" "http://$SERVER_HOST:$PORT" 2>&1)
      rps=$(echo "$out" | awk '/Requests\/sec/{print $2}')
      lat=$(echo "$out" | awk '/Latency/{print $2; exit}')
      echo "pingora,$rt,payload10k,$PAYLOAD_CONNS,$r,${rps:-0},${lat:-0}" | tee -a "$RAW"
    fi
    server_stop; sleep 2
  done
done

echo "== summary =="
cat "$(summarize_raw "$RAW" 6 pingora)"
