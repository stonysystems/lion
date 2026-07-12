#!/bin/bash
# One-click local micro benchmark runner.
# Reproduces the paper's Figure (Micro Benchmarks, exp3) on the local machine.
# Every single run is recorded to per-benchmark raw CSV files (no averaging-away).
#
# Why single-machine (local) and not cross-machine?
#   The micro benchmarks exist to ISOLATE the runtime's own overhead — the
#   scheduler, waker, timer wheel, and I/O readiness dispatch — so that any gap
#   between Lion and Tokio is attributable to the runtime, not the environment.
#     - Timer cancel (a,d) and Filesystem (c) have NO network component at all;
#       cross-machine is meaningless for them.
#     - TCP echo (b,e) does have a socket path, but running it over a real
#       network would make throughput bandwidth/RTT-bound, which masks the
#       runtime differences we are trying to measure (the paper shows exactly
#       this: its Axum cross-server numbers are bandwidth-limited and become
#       identical for both runtimes, while only the localhost config exposes the
#       runtime gap). Loopback keeps the runtime itself as the bottleneck.
#   Cross-machine, end-to-end realism (server + clients on separate hosts over
#   1 Gbps Ethernet) is therefore deferred to the REAL-WORLD experiments
#   (rumqtt / Pingora / Axum, paper section "Real-World Applications"), where
#   measuring production behaviour over a real link is the actual goal.
#
# Usage:
#   ./run.sh                       # full run: DURATION=10s x RUNS=10
#   DURATION=3 RUNS=2 ./run.sh     # quick smoke run
#   OUTDIR=/tmp/mine ./run.sh      # custom output dir
set -euo pipefail

DIR="$(cd "$(dirname "$0")" && pwd)"
# shellcheck disable=SC1091
[ -f "$HOME/.cargo/env" ] && . "$HOME/.cargo/env"
DURATION="${DURATION:-10}"
RUNS="${RUNS:-10}"
RETRIES="${RETRIES:-3}"
OUTDIR="${OUTDIR:-$DIR/results/local}"

ulimit -n 65536 2>/dev/null || true

# Machine-local build dir: building inside an NFS home is slow and collides
# when several machines share one checkout (override root: BENCH_TARGET_ROOT).
BENCH_TARGET_ROOT="${BENCH_TARGET_ROOT:-/tmp/${USER}-lion-bench}"
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$BENCH_TARGET_ROOT/micro}"
mkdir -p "$CARGO_TARGET_DIR"
TIMER_BIN="$CARGO_TARGET_DIR/release/micro-timer"
TCP_BIN="$CARGO_TARGET_DIR/release/micro-tcp-echo"
FS_BIN="$CARGO_TARGET_DIR/release/micro-fs"

mkdir -p "$OUTDIR"

echo "========================================="
echo "  Micro Benchmark — Local Run"
echo "  Duration: ${DURATION}s x ${RUNS} runs"
echo "  Cores:    $(nproc)"
echo "  Output:   $OUTDIR/"
echo "========================================="
echo ""

cd "$DIR" && cargo build --release 2>&1 | tail -3
echo ""

port_idx=0

# ── Resilient run helpers ───────────────────────────────────────────────
# A single benchmark process can fail transiently (e.g. a momentary
# EADDRINUSE on a just-released port). Under `set -e` one such blip would
# abort the whole multi-hour run, so each measurement is retried up to
# RETRIES times; one that still fails is skipped (logged to stderr) instead
# of killing the batch. The accepted CSV line is returned via $RESULT.
RESULT=""

valid_csv() { [[ "$(printf '%s' "$1" | head -1 | cut -d',' -f6)" =~ ^[0-9]+$ ]]; }

# Every attempt is wrapped in `timeout` (grace = DURATION + 30 s): a wedged
# benchmark process (e.g. a lost-wakeup hang) becomes a retry, not an
# indefinite stall of the whole batch. timeout exits 124 on expiry; the
# process is SIGKILLed 5 s later if it ignores SIGTERM.
RUN_TIMEOUT_CMD() { timeout -k 5 $((DURATION + 30)) "$@"; }

# run_bin <cmd...> — timer / fs (no port). Use an `env VAR=v` prefix as needed.
run_bin() {
  local out rc a
  for a in $(seq 1 "$RETRIES"); do
    if out=$(RUN_TIMEOUT_CMD "$@" 2>&1); then rc=0; else rc=$?; fi
    if [ "$rc" -eq 0 ] && valid_csv "$out"; then RESULT="$out"; return 0; fi
    if [ "$rc" -eq 124 ]; then echo "      [HANG killed after $((DURATION + 30))s, retry $a/$RETRIES] $*" >&2
    else echo "      [retry $a/$RETRIES rc=$rc] $*" >&2; fi
    sleep 1
  done
  echo "      [FAILED after $RETRIES] $* -> $(printf '%s' "$out" | tail -1)" >&2
  RESULT=""; return 1
}

# run_tcp <runtime> <threads> <load> — allocates a FRESH port on every attempt.
run_tcp() {
  local out rc a port
  for a in $(seq 1 "$RETRIES"); do
    port_idx=$((port_idx + 1)); port=$((23000 + port_idx))
    if out=$(RUN_TIMEOUT_CMD $TCP_BIN --runtime "$1" --threads "$2" --load "$3" --duration "$DURATION" --port "$port" --csv 2>&1); then rc=0; else rc=$?; fi
    if [ "$rc" -eq 0 ] && valid_csv "$out"; then RESULT="$out"; return 0; fi
    if [ "$rc" -eq 124 ]; then echo "      [HANG killed after $((DURATION + 30))s, retry $a/$RETRIES port=$port] tcp $1 t=$2 load=$3" >&2
    else echo "      [retry $a/$RETRIES rc=$rc port=$port] tcp $1 t=$2 load=$3" >&2; fi
    sleep 1
  done
  echo "      [FAILED after $RETRIES] tcp $1 t=$2 load=$3 -> $(printf '%s' "$out" | tail -1)" >&2
  RESULT=""; return 1
}

# mean_ops <values...> — arithmetic mean, "n/a" when no values survived.
mean_ops() {
  if [ "$#" -eq 0 ]; then echo "n/a"; else printf '%s\n' "$@" | awk '{s+=$1}END{printf "%.0f",s/NR}'; fi
}

# ══════════════════════════════════════════
# (a) TIMER — single thread, varying load
# ══════════════════════════════════════════
echo "### (a) TIMER: single-thread ###"
RAW="$OUTDIR/timer_st_raw.csv"
echo "runtime,threads,load,run,ops_per_sec,p50_ms,p99_ms,p999_ms,max_ms" > "$RAW"

for rt in tokio lion monoio; do
  for load in 1000 5000 10000; do
    ops=()
    for run in $(seq 1 $RUNS); do
      if run_bin "$TIMER_BIN" --runtime $rt --threads 1 --load $load --duration $DURATION --csv; then
        echo "$rt,1,$load,$run,$(echo "$RESULT" | cut -d',' -f6-10)" >> "$RAW"
        ops+=($(echo "$RESULT" | cut -d',' -f6))
      else
        echo "  !! skipped $rt load=$load run=$run" >&2
      fi
    done
    printf "  %-10s load=%-5d  ops/s=%s\n" "$rt" "$load" "$(mean_ops "${ops[@]}")"
  done
done
echo ""

# ══════════════════════════════════════════
# (d) TIMER — multi-thread scaling (load=10000 per run)
# ══════════════════════════════════════════
echo "### (d) TIMER: multi-thread scaling (load=10000) ###"
RAW="$OUTDIR/timer_mt_raw.csv"
echo "runtime,threads,load,run,ops_per_sec,p50_ms,p99_ms,p999_ms,max_ms" > "$RAW"

# MT_THREADS: thread sweep for panel (d)/(e)-style scaling (default = the
# paper's 1..3; pass e.g. MT_THREADS="1 2 3 4 6 8" for the extended sweep).
MT_THREADS="${MT_THREADS:-1 2 3}"
for rt in tokio tokio-part lion; do
  for threads in $MT_THREADS; do
    ops=()
    for run in $(seq 1 $RUNS); do
      if run_bin "$TIMER_BIN" --runtime $rt --threads $threads --load 10000 --duration $DURATION --csv; then
        echo "$rt,$threads,10000,$run,$(echo "$RESULT" | cut -d',' -f6-10)" >> "$RAW"
        ops+=($(echo "$RESULT" | cut -d',' -f6))
      else
        echo "  !! skipped $rt threads=$threads run=$run" >&2
      fi
    done
    printf "  %-10s threads=%-2d  ops/s=%s\n" "$rt" "$threads" "$(mean_ops "${ops[@]}")"
  done
done
echo ""

# ══════════════════════════════════════════
# (b) TCP ECHO — single thread
# ══════════════════════════════════════════
echo "### (b) TCP ECHO: single-thread ###"
RAW="$OUTDIR/tcp_st_raw.csv"
echo "runtime,threads,load,run,ops_per_sec,p50_ms,p99_ms,p999_ms,max_ms" > "$RAW"

for rt in tokio lion monoio; do
  for load in 10 50 100 500; do
    ops=()
    for run in $(seq 1 $RUNS); do
      if run_tcp "$rt" 1 "$load"; then
        echo "$rt,1,$load,$run,$(echo "$RESULT" | cut -d',' -f6-10)" >> "$RAW"
        ops+=($(echo "$RESULT" | cut -d',' -f6))
      else
        echo "  !! skipped $rt load=$load run=$run" >&2
      fi
    done
    printf "  %-10s load=%-5d  rps=%s\n" "$rt" "$load" "$(mean_ops "${ops[@]}")"
  done
done
echo ""

# ══════════════════════════════════════════
# (e) TCP ECHO — multi-thread scaling (load=500)
# ══════════════════════════════════════════
echo "### (e) TCP ECHO: multi-thread scaling (load=500) ###"
RAW="$OUTDIR/tcp_mt_raw.csv"
echo "runtime,threads,load,run,ops_per_sec,p50_ms,p99_ms,p999_ms,max_ms" > "$RAW"

for rt in tokio tokio-part lion; do
  for threads in 1 2 4; do
    ops=()
    for run in $(seq 1 $RUNS); do
      if run_tcp "$rt" "$threads" 500; then
        echo "$rt,$threads,500,$run,$(echo "$RESULT" | cut -d',' -f6-10)" >> "$RAW"
        ops+=($(echo "$RESULT" | cut -d',' -f6))
      else
        echo "  !! skipped $rt threads=$threads run=$run" >&2
      fi
    done
    printf "  %-10s threads=%-2d  rps=%s\n" "$rt" "$threads" "$(mean_ops "${ops[@]}")"
  done
done
echo ""

# ══════════════════════════════════════════
# (c) FILESYSTEM — blocking pool scaling (load=50)
# ══════════════════════════════════════════
echo "### (c) FILESYSTEM: blocking pool scaling (load=50) ###"
RAW="$OUTDIR/fs_raw.csv"
echo "runtime,blocking_threads,load,run,ops_per_sec,p50_ms,p99_ms,p999_ms,max_ms" > "$RAW"

for rt in tokio lion; do
  for bt in 1 2 4 8; do
    ops=()
    for run in $(seq 1 $RUNS); do
      if run_bin env LION_BLOCKING_THREADS=$bt "$FS_BIN" --runtime $rt --threads 1 --load 50 --duration $DURATION --csv; then
        echo "$rt,$bt,50,$run,$(echo "$RESULT" | cut -d',' -f6-10)" >> "$RAW"
        ops+=($(echo "$RESULT" | cut -d',' -f6))
      else
        echo "  !! skipped $rt bt=$bt run=$run" >&2
      fi
    done
    printf "  %-6s bt=%-2d  ops/s=%s\n" "$rt" "$bt" "$(mean_ops "${ops[@]}")"
  done
done

# Monoio: OS-level async file I/O via io_uring (no blocking pool)
ops=()
for run in $(seq 1 $RUNS); do
  if run_bin env LION_BLOCKING_THREADS=1 "$FS_BIN" --runtime monoio --threads 1 --load 50 --duration $DURATION --csv; then
    echo "monoio,1,50,$run,$(echo "$RESULT" | cut -d',' -f6-10)" >> "$RAW"
    ops+=($(echo "$RESULT" | cut -d',' -f6))
  else
    echo "  !! skipped monoio run=$run" >&2
  fi
done
printf "  monoio bt=1   ops/s=%s\n" "$(mean_ops "${ops[@]}")"
echo ""

echo "========================================="
echo "  Done. Raw per-run data in: $OUTDIR/"
ls -la "$OUTDIR/"
echo "========================================="
