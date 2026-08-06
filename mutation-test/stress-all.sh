#!/bin/bash
# stress-all.sh — supplemental run: correctness-stress against EVERY mutant.
#
# The locked protocol (README.md rule 3) ran the stress suite only as a
# validity spot-check on M04/M05/M07/C1/C3. This script extends that column to
# the full mutant list: a mutant the stress suite ACCEPTS (passes) while the
# verifier rejects it is itself a finding — the static catch is the only line
# of defense for that fault (M04 was the first such case). Protocol otherwise
# unchanged: same workload (shared/workload.rs), same oracle (timeout == hang),
# one mutant at a time, apply -> build -> run -> revert, raw per-run retained.
#
#   ./stress-all.sh          # all mutants, REPS=3, TIMEOUT_SECS=15, TEST=current
#   ./stress-all.sh M01      # single mutant
set -uo pipefail
DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(dirname "$DIR")"
CS="$ROOT/lion-benchmark/correctness-stress/lion"
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-${BENCH_TARGET_ROOT:-/tmp/${USER}-lion-bench}/correctness-stress-mutants}"
mkdir -p "$CARGO_TARGET_DIR"
TIMEOUT_SECS=${TIMEOUT_SECS:-15}
REPS=${REPS:-3}
TEST=${TEST:-current}
RES="$DIR/results/stress-matrix.md"
RAW="$DIR/results/stress-runs.jsonl"
BIN="$CARGO_TARGET_DIR/release/cs-lion"
mkdir -p "$DIR/results"

revert() { git -C "$ROOT" checkout -- lion-timer-wheel/src lion-executor/src lion-reactor/src; }

median_ms() {
  [ "$#" -eq 0 ] && { echo "-"; return; }
  printf '%s\n' "$@" | sort -n | awk '{a[NR]=$1} END{print (NR%2)? a[(NR+1)/2] : int((a[NR/2]+a[NR/2+1])/2)}'
}

# run_reps <label>: runs the built binary REPS times, appends raw jsonl,
# and emits a matrix row "| label | build | pass | hang | err | median |".
run_reps() {
  local label="$1" build="$2"
  local pass=0 hang=0 err=0 ptimes=()
  for ((r=1; r<=REPS; r++)); do
    local start el outcome
    start=$(($(date +%s%N)/1000000))
    timeout "${TIMEOUT_SECS}s" "$BIN" "$TEST" >/dev/null 2>&1
    local rc=$?
    el=$(( $(($(date +%s%N)/1000000)) - start ))
    if [ $rc -eq 0 ]; then outcome=pass; pass=$((pass+1)); ptimes+=("$el")
    elif [ $rc -eq 124 ]; then outcome=hang; hang=$((hang+1))
    else outcome=error; err=$((err+1)); fi
    echo "{\"mutant\":\"$label\",\"test\":\"$TEST\",\"rep\":$r,\"outcome\":\"$outcome\",\"ms\":$el,\"rc\":$rc,\"timeout_secs\":$TIMEOUT_SECS}" >> "$RAW"
    echo "  rep $r: $outcome (${el}ms)"
  done
  echo "| $label | $build | $pass | $hang | $err | $(median_ms ${ptimes[@]+"${ptimes[@]}"}) |" >> "$RES"
}

echo "| mutant | build | pass | hang | err | median pass ms |" > "$RES"
echo "|---|---|---|---|---|---|" >> "$RES"
> "$RAW"

# Baseline: unmutated tree, same binary/workload/oracle as every mutant row.
if [ $# -eq 0 ]; then
  revert
  echo "baseline: building..."
  if (cd "$CS" && cargo build --release >/dev/null 2>&1); then
    run_reps baseline OK
  else
    echo "| baseline | FAIL | - | - | - | - |" >> "$RES"; echo "baseline: BUILD FAILED"; exit 1
  fi
fi

for spec in "$DIR"/mutants/*.md; do
  m=$(basename "$spec" .md)
  if [ $# -ge 1 ] && [ "$m" != "${1%.md}" ] && [ "$m" != "$1" ]; then continue; fi
  patch="$DIR/patches/$m.patch"
  if [ ! -f "$patch" ]; then echo "| $m | NO PATCH | - | - | - | - |" >> "$RES"; continue; fi
  revert
  if ! git -C "$ROOT" apply "$patch"; then
    echo "| $m | APPLY FAIL | - | - | - | - |" >> "$RES"; echo "$m: APPLY FAILED"; continue
  fi
  echo "$m: building..."
  if ! (cd "$CS" && cargo build --release >/dev/null 2>&1); then
    echo "| $m | FAIL | - | - | - | - |" >> "$RES"; echo "$m: BUILD FAILED"; revert; continue
  fi
  run_reps "$m" OK
  revert
done

echo "done — matrix: $RES, raw: $RAW"
