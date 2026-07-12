#!/bin/bash
# rumqtt MQTT-broker benchmark — Lion (verified runtime) vs Tokio.
# Portable: paths relative to this script; topology from ../hosts.env or env;
# shared orchestration in ../lib/bench_common.sh. Per-run raw CSV (repo policy: per-run raw retained).
#
# Measures pub/sub message throughput against rumqttd, each runtime in turn. The
# broker listens on 1883 (its rumqttd.toml); the mqtt-benchmark tool drives load.
# Local by default; set CLIENT_HOST / use ../lib/remote_launch.sh for cross-machine.
#
# Usage:  ./run.sh          # DURATION=30s x RUNS=10
#         DURATION=5 RUNS=2 ./run.sh
set -euo pipefail

DIR="$(cd "$(dirname "$0")" && pwd)"
# shellcheck disable=SC1091
. "$DIR/../lib/bench_common.sh"
bench_setup "$DIR"
DURATION="${DURATION:-30}"

PORT="${PORT:-1883}"
BENCH_T="$(bench_target_dir "$DIR/src/benchmark")"
LION_T="$(bench_target_dir "$DIR/src/lion-rumqtt")"
TOKIO_T="$(bench_target_dir "$DIR/src/tokio-rumqtt")"
BENCH="$BENCH_T/release/mqtt-benchmark"
LION_BROKER="$LION_T/release/rumqttd"
TOKIO_BROKER="$TOKIO_T/release/rumqttd"
LION_CFG="$DIR/src/lion-rumqtt/rumqttd/rumqttd.toml"
TOKIO_CFG="$DIR/src/tokio-rumqtt/rumqttd/rumqttd.toml"
RAW="$OUTDIR/rumqtt_raw.csv"

echo "== build =="
(cd "$DIR/src/benchmark" && CARGO_TARGET_DIR="$BENCH_T" cargo build --release 2>&1 | tail -1)

# The load generator runs on the client; machine-local build dirs are not
# shared, so stage it there (no-op in single mode).
BENCH_CLIENT="$BENCH"
if ! is_local "$CLIENT_HOST"; then
  BENCH_CLIENT="/tmp/${SSH_USER:-$USER}-lion-bench/mqtt-benchmark"
  client_push "$BENCH" "$BENCH_CLIENT"
fi
(cd "$DIR/src/tokio-rumqtt" && CARGO_TARGET_DIR="$TOKIO_T" cargo build --release -p rumqttd 2>&1 | tail -1)
(cd "$DIR/src/lion-rumqtt" && CARGO_TARGET_DIR="$LION_T" cargo build --release -p rumqttd 2>&1 | tail -1)

# mqtt-benchmark prints a human banner + progress AND csv rows to stdout; the data
# rows start with "rumqttd," (system field). Keep only those, run index prepended.
# Columns: system,runtime,workload,pub_mps,sub_mps,p50_ms,p95_ms,p99_ms,p999_ms,max_ms
pkill -x rumqttd 2>/dev/null || true
sleep 1
echo "system,runtime,workload,pub_mps,sub_mps,p50_ms,p95_ms,p99_ms,p999_ms,max_ms,run" > "$RAW"
echo "== run (server=$SERVER_HOST client=$CLIENT_HOST ${DURATION}s x ${RUNS}) =="
# Interleaved A-B protocol (run outer, runtime inner): machine-state drift
# averages across arms; broker restarts per (run,runtime).
for r in $(seq 1 "$RUNS"); do
  for rt in tokio lion; do
    [ "$rt" = tokio ] && { BROKER="$TOKIO_BROKER"; CFG="$TOKIO_CFG"; } || { BROKER="$LION_BROKER"; CFG="$LION_CFG"; }
    server_start "/tmp/rumqttd_$rt.log" "$BROKER" -c "$CFG"
    sleep 3
    out=$(on_client "$BENCH_CLIENT" --host "$SERVER_HOST" --port "$PORT" --duration "$DURATION" --runtime "$rt" --csv 2>/dev/null)
    echo "$out" | grep "^rumqttd," | sed "s/$/,$r/" | tee -a "$RAW"
    server_stop; sleep 2
  done
done
echo "== summary (trim-2 mean +/- std, pub_mps) =="
cat "$(summarize_raw "$RAW" 4 rumqttd)"
