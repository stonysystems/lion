#!/bin/bash
# Runtime correctness stress test — Tokio / Lion (+ libevent/libuv in their own dirs).
#
# One unified workload (see shared/workload.rs) compiled unchanged against every
# runtime — each runtime crate differs only by which runtime its `rt` dependency
# renames. The workload is a neutral liveness stress (deadline-guarded requests,
# cooperative compute, fan-out, heartbeat, echo I/O, plus the config's idiomatic
# setup/offload pattern); it carries no bug-specific code. It is run in the two
# standard deployment configurations (argv: "current" / "multi"). The FINDING
# below is what running it reveals — which runtimes fail to keep every task live:
#   current-thread:  Tokio 1.21       hangs   (maps to issue #5020)
#   multi-thread:    Tokio 1.42/1.44  hang    (maps to issue #7209)
# so every tested Tokio version hangs in at least one standard config (a different
# bug in a different subsystem), while the formally-verified Lion passes both.
#
# Oracle: timeout == hang. These liveness failures are PERMANENT stalls (a task is
# left unscheduled forever), so they never complete. The workload's critical path
# is bounded to a couple of seconds (every wait is a bounded sleep, and request
# timeouts are cancelled as soon as the inner op finishes). A timeout an order of
# magnitude above that bound therefore separates a permanent hang from normal
# completion with no false positives.
#
# Because these failures can trigger PROBABILISTICALLY (timing/flag races), a
# single run can miss them. We therefore run each
# (test, runtime) REPS times (default 3; raise for tighter rate estimates) and
# report the HANG RATE (hangs/REPS); every run is
# recorded raw in results.jsonl (repo policy: per-run raw retained). A verified runtime (Lion) is
# expected 0/REPS; a buggy one shows a non-zero rate.
#
#   ./run.sh                 # REPS=3, TIMEOUT_SECS=15
#   REPS=5 TIMEOUT_SECS=10 ./run.sh   # quick
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
# shellcheck disable=SC1091
[ -f "$HOME/.cargo/env" ] && . "$HOME/.cargo/env"
export PATH="$HOME/.local/bin:$PATH"
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-${BENCH_TARGET_ROOT:-/tmp/${USER}-lion-bench}/correctness-stress}"
mkdir -p "$CARGO_TARGET_DIR"
TIMEOUT_SECS=${TIMEOUT_SECS:-15}
REPS=${REPS:-3}
TESTS="current multi"
RUNTIMES="tokio-1.21 tokio-1.42 tokio-1.44 tokio-latest lion"
RESULTS="$SCRIPT_DIR/results.jsonl"

echo "=========================================="
echo " Runtime Correctness Stress Test"
echo " REPS=$REPS  timeout=${TIMEOUT_SECS}s per run"
echo "=========================================="

for rt in $RUNTIMES; do
  echo "Building $rt..."
  (cd "$SCRIPT_DIR/$rt" && cargo build --release 2>&1 | tail -1)
done
echo ""

> "$RESULTS"

median_ms() {  # median of the integer args
  [ "$#" -eq 0 ] && { echo "-"; return; }
  printf '%s\n' "$@" | sort -n | awk '{a[NR]=$1} END{print (NR%2)? a[(NR+1)/2] : int((a[NR/2]+a[NR/2+1])/2)}'
}

printf "%-16s" "Test"
for rt in $RUNTIMES; do printf "%-20s" "$rt"; done
echo
printf '%0.s─' {1..120}; echo

for test in $TESTS; do
  printf "%-16s" "$test"
  for rt in $RUNTIMES; do
    BIN_NAME=$(grep '^name' "$SCRIPT_DIR/$rt/Cargo.toml" | head -1 | sed 's/.*= *"//;s/".*//')
    BIN="$CARGO_TARGET_DIR/release/$BIN_NAME"
    if [ ! -f "$BIN" ]; then printf "%-20s" "BUILD_ERR"; continue; fi

    hangs=0; passes=0; errs=0; ptimes=()
    for ((r=1; r<=REPS; r++)); do
      start=$(($(date +%s%N)/1000000))
      if timeout "${TIMEOUT_SECS}s" "$BIN" "$test" >/dev/null 2>&1; then
        el=$(( $(($(date +%s%N)/1000000)) - start )); passes=$((passes+1)); ptimes+=("$el")
        echo "{\"test\":\"$test\",\"runtime\":\"$rt\",\"run\":$r,\"outcome\":\"PASS\",\"elapsed_ms\":$el}" >> "$RESULTS"
      elif [ $? -eq 124 ]; then
        hangs=$((hangs+1))
        echo "{\"test\":\"$test\",\"runtime\":\"$rt\",\"run\":$r,\"outcome\":\"HANG\",\"elapsed_ms\":${TIMEOUT_SECS}000}" >> "$RESULTS"
      else
        errs=$((errs+1))
        echo "{\"test\":\"$test\",\"runtime\":\"$rt\",\"run\":$r,\"outcome\":\"ERROR\",\"elapsed_ms\":0}" >> "$RESULTS"
      fi
    done

    if [ "$hangs" -gt 0 ]; then
      printf "\033[31m%-20s\033[0m" "${hangs}/${REPS} HANG"
    elif [ "$errs" -gt 0 ]; then
      printf "\033[33m%-20s\033[0m" "${errs}/${REPS} ERR"
    else
      med=$(median_ms "${ptimes[@]}")
      printf "\033[32m%-20s\033[0m" "0/${REPS} (${med}ms)"
    fi
  done
  echo
done

echo ""
echo "Per-run raw results: $RESULTS"
echo "(hang rate = hangs/REPS; 0/REPS = liveness held across all runs)"

# Heatmap input: one extra lion "current" run with the event log captured
# (the matrix runs above discard stdout for speed). HEATMAP=0 to skip.
if [ "${HEATMAP:-1}" = "1" ]; then
  LION_BIN="$CARGO_TARGET_DIR/release/cs-lion"
  if [ -x "$LION_BIN" ]; then
    echo "Capturing heatmap event log (lion, current) -> events.tsv"
    timeout "${TIMEOUT_SECS}s" "$LION_BIN" current > "$SCRIPT_DIR/events.tsv" 2>/dev/null       || echo "WARNING: heatmap capture run did not complete"
    PLOTPY="$SCRIPT_DIR/../micro/.venv/bin/python"
    if [ -x "$PLOTPY" ]; then
      "$PLOTPY" "$SCRIPT_DIR/plot.py" "$SCRIPT_DIR/events.tsv" -o "$SCRIPT_DIR/stress_heatmap.pdf"         && echo "stress_heatmap.pdf rendered"         || echo "WARNING: heatmap render failed (events.tsv is kept)"
    else
      echo "NOTE: plotting venv missing — run lion-benchmark/setup.sh, then: plot.py events.tsv"
    fi
  fi
fi
