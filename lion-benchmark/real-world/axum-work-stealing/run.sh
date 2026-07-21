#!/bin/bash
# Work-stealing benchmark: axum service with a CPU-heavy, high-variance endpoint.
# Lion (thread-per-core, no stealing) vs Tokio (multi-thread, work-stealing).
#
# OPEN LOOP. Load is offered at a constant rate with vegeta, chosen so the
# server targets a given CPU utilisation:
#
#     lambda = rho * CORES / E[S]        E[S] = MEAN * SEC_PER_ITER
#
# This matters for two reasons, and is why this benchmark does not use the
# closed-loop wrk that drives the rest of the suite:
#
#  1. Utilisation is the x-axis, so it must be an INDEPENDENT variable. Under
#     closed-loop wrk, CONNS connections doing pure CPU work drive the server to
#     saturation regardless of MEAN — rho is an output, pinned near 100%.
#  2. Closed-loop load suffers coordinated omission: when the server stalls the
#     generator stops issuing, systematically understating the tail. The headline
#     metric here IS p99, and the bias flatters thread-per-core — exactly the
#     arm we expect to lose.
#
# WHY VEGETA AND NOT WRK2. wrk2 was tried first and rejected on measurement, not
# preference. Against a server whose true service time is ~4.4ms, at 556 rps:
#
#     ground truth (sequential probe, idle server) : 8.6-10.2ms  (de-boosted)
#     wrk2 -t16 -c256 : p50 34.7ms  p99 114.8ms   sampling interval 135-152ms
#     wrk2 -t2  -c16  : p50 10.3ms  p99  15.6ms   sampling interval 24ms
#     vegeta          : p50  5.1ms  p99  11.4ms   rate 556.09/556 requested
#
# wrk2 issues in batches sized by an internally calibrated sampling interval;
# the recorded latency then includes each request's wait inside that batch. The
# inflation tracks the interval and lands squarely on p99, the headline metric,
# and the interval depends on threads and connections — so any per-cell tuning
# would vary the instrument along the x-axis. (wrk2 also segfaulted at -t16
# -c64.) vegeta paces per request, hits the requested rate to within 0.02%, and
# its p50 of 5.1ms matches the boosted service time as queueing theory requires
# at rho~0.3.
#
# PAIRED WORKLOAD. The per-request cost sequence is pre-generated to a file
# (bench/gen_targets.py) and replayed identically by both runtimes and every
# repetition, so the comparison is paired and free of workload sampling noise.
#
# Sweeps rho x CV. The plotted x-axis is the MEASURED utilisation (sampled from
# /proc/<pid>/stat), not the requested rho, so any shortfall in offered load is
# visible rather than assumed away.
#
# Usage:  ./run.sh
#         CORES=8 RHOS="0.2 0.5 0.8" CVS="1 4" DURATION=60 RUNS=5 ./run.sh
#
# Requires results/calibration.env (see ./calibrate.sh) for SEC_PER_ITER.
set -euo pipefail

DIR="$(cd "$(dirname "$0")" && pwd)"
# shellcheck disable=SC1091
. "$DIR/../lib/bench_common.sh"
bench_setup "$DIR"
require_client_tool vegeta

CORES="${CORES:-8}"
# MEAN=20000 iters ~= 4.3ms of CPU at the calibrated 215.7 ns/iter, so the fixed
# ~119us HTTP overhead is only 2.7% of E[S]. A smaller MEAN would dilute the
# per-request cost variance -- the very thing being swept -- with fixed cost.
MEAN="${MEAN:-20000}"
# CAP=400 bounds one request at 1.76s (well inside the TIMEOUT below) while
# still admitting realized CVs of {1.0, 2.0, 3.7, 5.4} for nominal {1,2,4,8}.
# Tighter caps collapse the top of the CV range: at CAP=100 nominal 4 and 8 give
# realized 3.1 and 3.9, nearly the same distribution.
CAP="${CAP:-400}"
CVS="${CVS:-1 4 8}"
# Lower bound 0.2, not 0.05: below that the request rate is too low for a stable
# p99 in a short run, and the cores sit de-boosted (1.5 vs 3.3 GHz), which
# inflates latency on BOTH arms and contaminates exactly the region where the
# absolute numbers would otherwise be most interesting.
RHOS="${RHOS:-0.2 0.35 0.5 0.65 0.8 0.9}"
DURATION="${DURATION:-25}"
RUNS="${RUNS:-3}"
WARMUP="${WARMUP:-5}"
# Request timeout, ~3x the 1.76s worst-case service time (CAP*MEAN*SEC_PER_ITER).
# At high rho and high CV the thread-per-core arm goes over-saturated: per-core
# imbalance costs it enough effective capacity that the offered load exceeds what
# it can serve, and the queue grows without bound. A 30s timeout then makes each
# such cell take minutes to drain and reports a "p99" that is really the depth of
# a queue that never emptied. Bounding it at 3x max service time keeps cells
# bounded AND is the honest measurement: anything slower than this is a failure,
# and vegeta records it as one (success_ratio, non_2xx) rather than as latency.
TIMEOUT="${TIMEOUT:-5}"
OFFLOAD="${OFFLOAD:-0}"               # 1 = run heavy work via spawn_blocking
BLOCKING_THREADS="${BLOCKING_THREADS:-8}"  # blocking-pool size on BOTH arms when OFFLOAD=1
CHUNK="${CHUNK:-0}"                   # >0 = yield every N iters (head-of-line mitigation)
CHUNK_ARMS="${CHUNK_ARMS:-lion}"     # which arms get --chunk (default: lion only, the idiomatic TPC fix)
MAX_WORKERS="${MAX_WORKERS:-1024}"   # in-flight ceiling; must exceed lambda * p99
TARGET_COUNT="${TARGET_COUNT:-60000}" # distinct pre-generated requests per CV
PORT="${PORT:-8791}"
SEED="${WS_SEED:-1}"

TARGET_DIR="$(bench_target_dir "$DIR")"
RAW="$OUTDIR/work_stealing_raw.csv"

# --- service time ------------------------------------------------------------
CALIB="${CALIB:-$DIR/results/calibration.env}"
if [ -z "${SEC_PER_ITER:-}" ]; then
  [ -f "$CALIB" ] || { echo "FATAL: no $CALIB — run ./calibrate.sh on the server first" >&2; exit 1; }
  # shellcheck disable=SC1090
  . "$CALIB"
fi
: "${SEC_PER_ITER:?not set by calibration}"
ES=$(python3 -c "print($MEAN * $SEC_PER_ITER)")
echo "[bench] E[S] = ${ES}s per request (MEAN=$MEAN iters, SEC_PER_ITER=$SEC_PER_ITER)"

# --- core pinning ------------------------------------------------------------
# Pin to DISTINCT PHYSICAL cores. Taking cpus 0..N-1 blindly can land on SMT
# sibling pairs, which would give the server N hardware threads on N/2 physical
# cores — halving real capacity and silently breaking the rho calibration.
CPUSET="${CPUSET:-$(python3 - "$CORES" <<'PY'
import sys, subprocess
want = int(sys.argv[1])
seen, out = set(), []
for line in subprocess.run(["lscpu", "-p=CPU,CORE"], capture_output=True, text=True).stdout.splitlines():
    if line.startswith("#"):
        continue
    cpu, core = line.split(",")[:2]
    if core not in seen:              # first hardware thread of each physical core
        seen.add(core)
        out.append(cpu)
    if len(out) == want:
        break
if len(out) < want:
    sys.exit(f"only {len(out)} physical cores available, need {want}")
print(",".join(out))
PY
)}"
echo "[bench] server pinned to physical cpus: $CPUSET"

CLK_TCK="$(getconf CLK_TCK)"

server_cpu_ticks() {  # total utime+stime of the server process, in ticks
  awk '{print $14 + $15}' "/proc/$SERVER_PID/stat" 2>/dev/null || echo 0
}

# --- CPU frequency and per-core load ------------------------------------------
# This host runs the schedutil governor and we have no root to pin it to
# `performance`. MEASURED on zoo-002: an idle core sits at 1.50 GHz and a
# sustained-busy core reaches 3.31 GHz — a 2.21x swing (scaling_max_freq reports
# only 2.18 GHz; AMD core performance boost goes above it). So E[S] is NOT
# constant across the sweep, and absolute latencies at low rho are inflated
# because the cores there are partly de-boosted.
#
# The headline metric is the Lion/Tokio ratio at matched MEASURED utilisation,
# and both arms meet the same governor, so the ratio is largely protected. But
# NOT automatically: the two arms distribute load differently — thread-per-core
# concentrates a heavy request on one core while others idle, work-stealing
# spreads it — and on EPYC the achievable boost depends on how many cores are
# active. That could clock Lion's busy cores HIGHER than Tokio's evenly-loaded
# ones and partly mask the effect under study. We therefore record the clock,
# and the PER-CORE utilisation spread, for every cell of both arms, so the
# assumption is checkable rather than asserted.
#
# The per-core spread is also the direct mechanistic evidence for the result:
# thread-per-core should show high variance across cores (some idle while others
# are backlogged); work-stealing should show them near-uniform.
FREQ_FILES="$(echo "$CPUSET" | tr ',' '\n' \
  | sed 's#^#/sys/devices/system/cpu/cpu#; s#$#/cpufreq/scaling_cur_freq#' | tr '\n' ' ')"

FREQ_PID=""
freq_sample_start() {
  local f="$1"; : > "$f"
  # shellcheck disable=SC2086
  ( while :; do
      awk '{s+=$1; n++} END{if(n) print s/n}' $FREQ_FILES >> "$f" 2>/dev/null
      sleep 2
    done ) &
  FREQ_PID=$!
}
freq_sample_stop() {  # echoes mean kHz over the sampling window
  [ -n "$FREQ_PID" ] && { kill "$FREQ_PID" 2>/dev/null || true; wait "$FREQ_PID" 2>/dev/null || true; }
  FREQ_PID=""
  awk '{s+=$1; n++} END{printf "%.0f", (n ? s/n : 0)}' "$1" 2>/dev/null || echo 0
}

# Per-core busy time for the pinned cpus, from /proc/stat. Field 5 is `idle`
# and field 6 `iowait`; everything else in the line is busy.
percore_snapshot() {
  awk -v set="$CPUSET" '
    BEGIN { n = split(set, a, ","); for (i = 1; i <= n; i++) want["cpu" a[i]] = 1 }
    $1 in want {
      tot = 0; for (i = 2; i <= NF; i++) tot += $i
      printf "%s %d %d\n", $1, tot, $5 + $6
    }' /proc/stat
}
# percore_delta <before-file> <after-file> -> "mean min max stdev" busy fractions
percore_delta() {
  join "$1" "$2" | awk '
    { dtot = $4 - $2; didle = $5 - $3
      if (dtot > 0) { b = (dtot - didle) / dtot; s += b; ss += b * b; k++
                      if (mn == "" || b < mn) mn = b; if (b > mx) mx = b } }
    END { if (!k) { print "0 0 0 0"; exit }
          m = s / k; v = ss / k - m * m; if (v < 0) v = 0
          printf "%.4f %.4f %.4f %.4f", m, mn, mx, sqrt(v) }'
}

# --- one measurement cell ----------------------------------------------------
run_cell() {  # $1=runtime $2=cv $3=rho $4=run ; appends one CSV row
  local rt="$1" cv="$2" rho="$3" run="$4"
  local bin="$TARGET_DIR/release/ws-$rt"
  local targets="$TARGETS_DIR/cv${cv}.txt"
  local rcv; rcv="$(cat "$TARGETS_DIR/cv${cv}.realized_cv")"

  local rate
  rate=$(awk -v r="$rho" -v c="$CORES" -v e="$ES" 'BEGIN{printf "%d", r*c/e + 0.5}')

  # The Lion arm additionally pins each executor to one of those cpus: taskset
  # alone constrains the process, not individual threads, and MultiRuntime sets
  # no affinity of its own (measured: 8 executors on 7 cpus, one core unused).
  # Tokio's scheduler was verified to already land one worker per cpu under the
  # same taskset, so it keeps its default placement.
  local pin=()
  [ "$rt" = lion ] && pin=(--cpus "$CPUSET")
  # OFFLOAD=1 moves the CPU work onto each runtime's blocking pool, sized equally
  # (BLOCKING_THREADS) on both arms so the comparison is pool-for-pool rather than
  # against tokio's default of 512. Lion reads its pool size from the env var.
  local extra=() envp=()
  if [ "${OFFLOAD:-0}" = 1 ]; then
    extra=(--offload)
    [ "$rt" = tokio ] && extra+=(--blocking-threads "$BLOCKING_THREADS")
    [ "$rt" = lion ] && envp=(env "LION_BLOCKING_THREADS=$BLOCKING_THREADS")
  elif [ "$CHUNK" -gt 0 ] && [[ " $CHUNK_ARMS " == *" $rt "* ]]; then
    extra=(--chunk "$CHUNK")
  fi
  server_start "$OUTDIR/ws-$rt.log" "${envp[@]}" taskset -c "$CPUSET" \
    "$bin" --host 0.0.0.0 --port "$PORT" --cores "$CORES" "${pin[@]}" "${extra[@]}"
  local ready=0 i
  for i in $(seq 1 50); do
    curl -sf -m 2 "http://127.0.0.1:$PORT/health" >/dev/null 2>&1 && { ready=1; break; }
    sleep 0.2
  done
  [ "$ready" = 1 ] || { echo "  !! $rt server not ready"; tail -3 "$OUTDIR/ws-$rt.log"; server_stop; return 1; }

  # Warm up at the measurement rate, outside the window. Also brings the cores
  # up to their boost clock so the window is not measuring the ramp.
  on_client "\$HOME/.local/bin/vegeta attack -rate=$rate -duration=${WARMUP}s \
      -max-workers=$MAX_WORKERS -timeout=${TIMEOUT}s -targets='$targets' > /dev/null" >/dev/null 2>&1 || true

  local t0 c0 t1 c1 freq percore
  local freqfile="$OUTDIR/.freq.$$"
  local pc0="$OUTDIR/.pc0.$$" pc1="$OUTDIR/.pc1.$$"
  local jsonf="$OUTDIR/vegeta_${rt}_cv${cv}_rho${rho}_r${run}.json"

  percore_snapshot > "$pc0"
  c0=$(server_cpu_ticks); t0=$(date +%s.%N)
  freq_sample_start "$freqfile"
  on_client "\$HOME/.local/bin/vegeta attack -rate=$rate -duration=${DURATION}s \
      -max-workers=$MAX_WORKERS -timeout=${TIMEOUT}s -targets='$targets' \
      | \$HOME/.local/bin/vegeta report -type=json" > "$jsonf" 2>"$OUTDIR/.vegeta.err"
  t1=$(date +%s.%N); c1=$(server_cpu_ticks)
  freq=$(freq_sample_stop "$freqfile")
  percore_snapshot > "$pc1"
  percore=$(percore_delta "$pc0" "$pc1")
  rm -f "$freqfile" "$pc0" "$pc1"
  server_stop

  python3 - "$rt" "$cv" "$rho" "$run" "$rate" "$rcv" "$c0" "$c1" "$t0" "$t1" \
           "$CORES" "$CLK_TCK" "$MEAN" "$freq" "$percore" "$jsonf" <<'PY' >> "$RAW"
import sys, json

(rt, cv, rho, run, rate, rcv, c0, c1, t0, t1, cores, tck, mean, freq,
 percore, path) = sys.argv[1:17]
pc_mean, pc_min, pc_max, pc_sd = (percore.split() + ["0"] * 4)[:4]

NAN = float("nan")
try:
    d = json.load(open(path))
except Exception:
    d = {}

lat = d.get("latencies", {})
ms = lambda k: lat[k] / 1e6 if k in lat else NAN   # vegeta reports nanoseconds

# status_codes maps code -> count; anything not 200 is lost goodput, not latency.
codes = d.get("status_codes", {}) or {}
non2xx = sum(v for k, v in codes.items() if not k.startswith("2"))

# Measured utilisation: server CPU-seconds / (wall seconds * cores allotted).
cpu_s = (float(c1) - float(c0)) / float(tck)
wall = float(t1) - float(t0)
util = cpu_s / (wall * float(cores)) if wall > 0 else NAN

print(",".join(str(x) for x in [
    "work-stealing", rt, cores, mean, cv, rcv, rho, run, rate,
    f"{d.get('rate', NAN):.2f}", f"{d.get('throughput', NAN):.2f}", f"{util:.4f}",
    f"{ms('50th'):.3f}", f"{ms('90th'):.3f}", f"{ms('99th'):.3f}", f"{ms('max'):.3f}",
    freq, pc_mean, pc_min, pc_max, pc_sd,
    d.get("requests", -1), f"{d.get('success', NAN):.6f}", non2xx,
    (d.get("errors") or ["-"])[0].replace(",", ";")[:60],
]))
PY
  tail -1 "$RAW"
}

# --- sweep -------------------------------------------------------------------
# ARMS selects which runtimes to run (default both). Use ARMS="lion" to collect
# only the chunked Lion arm without re-running an unchanged Tokio-inline arm.
ARMS="${ARMS:-tokio lion}"
for rt in $ARMS; do
  [ -x "$TARGET_DIR/release/ws-$rt" ] || { echo "FATAL: ws-$rt not built in $TARGET_DIR" >&2; exit 1; }
done

# --- pre-generate the paired request streams ---------------------------------
# One file per CV, shared by both runtimes and all repetitions: the comparison
# replays an identical cost sequence rather than two independent samples.
TARGETS_DIR="$OUTDIR/targets"
mkdir -p "$TARGETS_DIR"
echo "== generating request streams (${TARGET_COUNT} requests per CV) =="
for cv in $CVS; do
  f="$TARGETS_DIR/cv${cv}.txt"
  out=$(python3 "$DIR/bench/gen_targets.py" "http://$SERVER_HOST:$PORT/work" \
        "$MEAN" "$cv" "$CAP" "$TARGET_COUNT" "$SEED" "$f")
  echo "$out" | awk '/^realized_cv /{print $2}' > "$TARGETS_DIR/cv${cv}.realized_cv"
  echo "  nominal cv=$cv -> $(echo "$out" | awk '/^realized_cv /{print $2}') realized," \
       "mean n=$(echo "$out" | awk '/^realized_mean /{print $2}')"
done

echo "system,runtime,cores,mean,cv_nominal,cv_realized,rho_target,run,rate_target,rate_achieved,throughput,util_measured,p50_ms,p90_ms,p99_ms,max_ms,cpu_khz,percore_util_mean,percore_util_min,percore_util_max,percore_util_sd,requests,success_ratio,non_2xx,first_error" > "$RAW"
echo "== sweep: cores=$CORES rho={$RHOS} cv={$CVS} ${DURATION}s x $RUNS =="

# Run outer / runtime inner: an A-B interleave, so slow drift in machine state
# hits both runtimes equally instead of biasing whichever ran second.
for run in $(seq 1 "$RUNS"); do
  for rho in $RHOS; do
    for cv in $CVS; do
      for rt in $ARMS; do
        run_cell "$rt" "$cv" "$rho" "$run" || true
        sleep 2
      done
    done
  done
done

echo "== done -> $RAW =="
