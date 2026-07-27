#!/bin/bash
# Attribution experiment driver: decompose the Lion-vs-Tokio Axum-localhost
# delta into (a) serve-path shape, (b) fs/blocking-pool path, (c) residual
# runtime core. Five configs, interleaved A-B, wrk protocol matching ../run.sh
# (wrk -t2 -c50, small.lua). See ../../attribution_note.md for the design,
# reference results, and interpretation.
#
# Usage:  ./drive.sh            # DURATION=10s x RUNS=3
#         DURATION=30 RUNS=10 ./drive.sh
set -u
DIR="$(cd "$(dirname "$0")" && pwd)"
AXUM="$DIR/../.."             # lion-benchmark/real-world/axum
PORT="${PORT:-8899}"
ROOT="${BENCH_ROOT:-/tmp/axum-bench-files}"
LUA="$AXUM/src/benchmark/small.lua"
DURATION="${DURATION:-10}"
RUNS="${RUNS:-3}"
CSV="$DIR/results.csv"

echo "== build (4 crates) =="
(cd "$AXUM/src/tokio-axum" && cargo build --release 2>&1 | tail -1)
(cd "$AXUM/src/lion-axum" && cargo build --release 2>&1 | tail -1)
(cd "$DIR/tokio-manual" && cargo build --release 2>&1 | tail -1)
(cd "$DIR/lion-var" && cargo build --release 2>&1 | tail -1)

if [ ! -d "$ROOT/small" ]; then
  mkdir -p "$ROOT/small" "$ROOT/large"
  for i in $(seq 1 100); do dd if=/dev/urandom of="$ROOT/small/f${i}.bin" bs=4096 count=1 2>/dev/null; done
  for i in $(seq 1 100); do dd if=/dev/urandom of="$ROOT/large/f${i}.bin" bs=1024 count=64 2>/dev/null; done
fi

declare -A BIN FLAG
BIN[tokio-serve-fs]="$AXUM/src/tokio-axum/target/release/axum-fileserver";   FLAG[tokio-serve-fs]=""
BIN[tokio-manual-fs]="$DIR/tokio-manual/target/release/axum-fileserver";     FLAG[tokio-manual-fs]=""
BIN[tokio-manual-nofs]="$DIR/tokio-manual/target/release/axum-fileserver";   FLAG[tokio-manual-nofs]="--nofs"
BIN[lion-manual-fs]="$AXUM/src/lion-axum/target/release/axum-fileserver";    FLAG[lion-manual-fs]=""
BIN[lion-manual-nofs]="$DIR/lion-var/target/release/axum-fileserver";        FLAG[lion-manual-nofs]="--nofs"
ORDER="tokio-serve-fs tokio-manual-fs tokio-manual-nofs lion-manual-fs lion-manual-nofs"

echo "config,run,rps,lat" > "$CSV"
for r in $(seq 1 "$RUNS"); do
  for cfg in $ORDER; do
    pkill -x axum-fileserver 2>/dev/null; sleep 0.5
    "${BIN[$cfg]}" --host 127.0.0.1 --port "$PORT" --root "$ROOT" ${FLAG[$cfg]} >/dev/null 2>&1 &
    SRV=$!
    sleep 1
    if ! curl -s -m 3 "http://127.0.0.1:$PORT/small/f1.bin" >/dev/null; then
      echo "$cfg,$r,START_FAIL,0" | tee -a "$CSV"; kill $SRV 2>/dev/null; continue
    fi
    out=$(wrk -t2 -c50 -d"${DURATION}s" -s "$LUA" "http://127.0.0.1:$PORT" 2>&1)
    rps=$(echo "$out" | awk '/Requests\/sec/{print $2}')
    lat=$(echo "$out" | awk '/Latency/{print $2; exit}')
    echo "$cfg,$r,${rps:-0},${lat:-0}" | tee -a "$CSV"
    kill $SRV 2>/dev/null; wait $SRV 2>/dev/null
  done
done
pkill -x axum-fileserver 2>/dev/null
echo "== medians =="
for cfg in $ORDER; do
  med=$(grep "^$cfg," "$CSV" | cut -d, -f3 | sort -n | awk '{a[NR]=$1} END{print a[int((NR+1)/2)]}')
  echo "$cfg  median_rps=$med"
done
