#!/bin/bash
# Calibrate the per-iteration service time of the /work handler on THIS machine.
#
# The work-stealing experiment sets offered load open-loop, as a request rate:
#
#     lambda = rho * CORES / E[S]      with   E[S] = MEAN * SEC_PER_ITER
#
# so a target CPU utilisation rho can only be requested once SEC_PER_ITER is
# known for the server hardware.
#
# FREQUENCY. SEC_PER_ITER is NOT a hardware constant on this class of machine.
# Measured on the EPYC 7702P: an idle core sits at 1.50 GHz and a sustained-busy
# core boosts to 3.31 GHz — a 2.21x swing, which showed up directly as a 2.26x
# spread in per-iteration cost between isolated and sustained requests. Probing
# with one-shot requests therefore measures the DE-BOOSTED clock and overstates
# SEC_PER_ITER by ~2x.
#
# So we calibrate under SUSTAINED load: for each n, a long keep-alive burst whose
# first half is discarded, leaving only the boosted steady state. The resulting
# SEC_PER_ITER describes a busy core, which is the regime the sweep runs in.
# At low target rho the cores will not be fully boosted and the achieved
# utilisation will exceed the target — which is why run.sh plots MEASURED
# utilisation rather than the requested rho.
#
# Fits  latency(n) = intercept + n * SEC_PER_ITER ; the intercept absorbs
# HTTP/TCP overhead so the slope is the pure SHA-256 cost.
# Writes SEC_PER_ITER to results/calibration.env for run.sh to source.
#
# Usage:  ./calibrate.sh            # uses the tokio binary, 1 core
set -euo pipefail

DIR="$(cd "$(dirname "$0")" && pwd)"
# shellcheck disable=SC1091
. "$DIR/../lib/bench_common.sh"
bench_setup "$DIR"

PORT="${PORT:-8791}"
TARGET_DIR="$(bench_target_dir "$DIR")"
BIN="$TARGET_DIR/release/ws-tokio"
[ -x "$BIN" ] || { echo "FATAL: $BIN not built" >&2; exit 1; }

# Sequential probes: no concurrency, so latency is pure service time + overhead.
#
# Each measurement is sized in SECONDS of continuous load rather than in a fixed
# request count: the core only holds its boost clock while it is continuously
# busy, and a fixed count means a short, low-duty-cycle burst at small n. Every n
# gets WARM_S seconds of discarded load followed by a TARGET_S measurement
# window, with no interpreter startup inside the loop to let the core idle.
NS="${NS:-100000 50000 20000 10000 5000}"
REPS="${REPS:-3}"
TARGET_S="${TARGET_S:-4}"
WARM_S="${WARM_S:-3}"
# Fixed path (not the dated OUTDIR): run.sh sources this, and the calibration is
# a property of the host, reused across sweeps.
OUT="$DIR/results/calibration.env"
mkdir -p "$DIR/results"
SAMPLES="$OUTDIR/calibration_samples.csv"

echo "== calibrate on $(hostname) ($(nproc) cpus) =="
# Pin to a single core: we want per-core service time, not an aggregate.
taskset -c 0 "$BIN" --host 127.0.0.1 --port "$PORT" --cores 1 >"$OUTDIR/calib_server.log" 2>&1 &
SERVER_PID=$!
trap 'kill "$SERVER_PID" 2>/dev/null || true' EXIT

for _ in $(seq 1 50); do
  curl -sf "http://127.0.0.1:$PORT/health" >/dev/null 2>&1 && break
  sleep 0.2
done
curl -sf "http://127.0.0.1:$PORT/health" >/dev/null || { echo "server did not start"; cat "$OUTDIR/calib_server.log"; exit 1; }

# A curl config file, not argv: at small n a 4-second window is thousands of
# requests, which would blow past a sane command line.
# NOTE the per-url `-o`. curl applies a single -o to ONE url only; without one
# per url it writes the 2nd-onward response BODY to stdout, where it
# concatenates with the -w timing ("7767" + "0.005038" -> "77670.005038") and
# silently corrupts the fit.
gen_cfg() {  # $1=count $2=n $3=outfile
  awk -v c="$1" -v n="$2" -v p="$PORT" 'BEGIN{
    for (i = 0; i < c; i++) {
      print "-o /dev/null"
      printf "url = \"http://127.0.0.1:%s/work?n=%s\"\n", p, n
    }
  }' > "$3"
}

# Bootstrap the per-iteration estimate used to size the bursts (and boost the
# core on the way). Refined by the real fit below; only needs to be within ~2x.
gen_cfg 200 100000 "$OUTDIR/.cfg.boot"
EST=$(curl -s -K "$OUTDIR/.cfg.boot" -w '%{time_total}\n' \
      | awk '{s+=$1; c++} END{print (c ? s/c/100000 : 2e-7)}')
echo "  bootstrap estimate: $(awk -v e="$EST" 'BEGIN{printf "%.1f", e*1e9}') ns/iter"

FREQ_LOG="$OUTDIR/calibration_freq.csv"
echo "n,rep,mean_khz" > "$FREQ_LOG"
echo "n,rep,seconds" > "$SAMPLES"

for n in $NS; do
  cnt=$(awk  -v t="$TARGET_S" -v n="$n" -v e="$EST" 'BEGIN{c=int(t/(n*e))+1; print (c<20?20:c)}')
  wcnt=$(awk -v t="$WARM_S"   -v n="$n" -v e="$EST" 'BEGIN{c=int(t/(n*e))+1; print (c<20?20:c)}')
  gen_cfg "$cnt"  "$n" "$OUTDIR/.cfg.m"
  gen_cfg "$wcnt" "$n" "$OUTDIR/.cfg.w"

  for rep in $(seq 1 "$REPS"); do
    curl -s -K "$OUTDIR/.cfg.w" >/dev/null 2>&1          # discarded warm-up
    # Sample the clock across the measured window only.
    ( while :; do cat /sys/devices/system/cpu/cpu0/cpufreq/scaling_cur_freq; sleep 0.5; done ) \
      > "$OUTDIR/.freqsamp" 2>/dev/null &
    fpid=$!
    per=$(curl -s -K "$OUTDIR/.cfg.m" -w '%{time_total}\n' \
          | awk -v c="$cnt" '{s+=$1; k++} END{if (k != c) exit 1; print s/k}') \
      || { echo "FATAL: expected $cnt timings from curl, got a different count" >&2; kill $fpid 2>/dev/null; exit 1; }
    kill $fpid 2>/dev/null; wait $fpid 2>/dev/null || true
    mhz=$(awk '{s+=$1; k++} END{printf "%.0f", (k ? s/k : 0)}' "$OUTDIR/.freqsamp")
    echo "$n,$rep,$per" >> "$SAMPLES"
    echo "$n,$rep,$mhz" >> "$FREQ_LOG"
  done
  echo "  n=$n done ($cnt req/window, cpu0 $(awk -F, -v N="$n" '$1==N{s+=$3;k++} END{printf "%.0f", (k?s/k/1000:0)}' "$FREQ_LOG") MHz)"
done
rm -f "$OUTDIR"/.cfg.* "$OUTDIR/.freqsamp"

kill "$SERVER_PID" 2>/dev/null || true
trap - EXIT

python3 - "$SAMPLES" "$OUT" <<'PY'
import sys, csv, statistics
from collections import defaultdict

samples_path, out_path = sys.argv[1], sys.argv[2]
by_n = defaultdict(list)
with open(samples_path) as fh:
    for row in csv.DictReader(fh):
        by_n[int(row["n"])].append(float(row["seconds"]))

# Median per n: robust to the occasional scheduling hiccup in a sequential probe.
pts = sorted((n, statistics.median(v)) for n, v in by_n.items())
print("\n   n        median latency")
for n, t in pts:
    print(f"  {n:>8}   {t*1e6:>12.1f} us")

# Least squares fit latency = a + b*n
nbar = sum(n for n, _ in pts) / len(pts)
tbar = sum(t for _, t in pts) / len(pts)
num = sum((n - nbar) * (t - tbar) for n, t in pts)
den = sum((n - nbar) ** 2 for n, _ in pts)
slope = num / den
intercept = tbar - slope * nbar

ss_tot = sum((t - tbar) ** 2 for _, t in pts)
ss_res = sum((t - (intercept + slope * n)) ** 2 for n, t in pts)
r2 = 1 - ss_res / ss_tot if ss_tot > 0 else float("nan")

print(f"\n  SEC_PER_ITER = {slope:.6e} s  ({slope*1e9:.2f} ns/iteration)")
print(f"  HTTP overhead (intercept) = {intercept*1e6:.1f} us")
print(f"  R^2 = {r2:.6f}")
if r2 < 0.999:
    print("  WARNING: poor linear fit — service time is not linear in n; check for noise")

with open(out_path, "w") as fh:
    fh.write(f"SEC_PER_ITER={slope:.6e}\n")
    fh.write(f"HTTP_OVERHEAD_S={intercept:.6e}\n")
    fh.write(f"CALIB_R2={r2:.6f}\n")
    fh.write(f"CALIB_HOST={__import__('socket').gethostname()}\n")
print(f"\n  -> {out_path}")
PY

# The clock this calibration was taken at: SEC_PER_ITER is only meaningful
# alongside it, since the same core runs 2.2x slower when not boosted. Mean over
# the measured windows only (warm-ups and inter-window gaps excluded), plus the
# spread — a wide range means the core never settled and the fit is suspect.
read -r CAL_KHZ CAL_MIN CAL_MAX <<EOF
$(awk -F, 'NR>1{s+=$3; k++; if(mn==""||$3<mn)mn=$3; if($3>mx)mx=$3}
           END{printf "%.0f %.0f %.0f", (k?s/k:0), mn, mx}' "$FREQ_LOG")
EOF
{
  echo "CALIB_CLOCK_KHZ=$CAL_KHZ"
  echo "CALIB_CLOCK_MIN_KHZ=$CAL_MIN"
  echo "CALIB_CLOCK_MAX_KHZ=$CAL_MAX"
} >> "$OUT"
echo "  calibrated at $((CAL_KHZ / 1000)) MHz (range $((CAL_MIN / 1000))-$((CAL_MAX / 1000)) MHz across measured windows)"
awk -v mn="$CAL_MIN" -v mx="$CAL_MAX" 'BEGIN{ if (mn > 0 && mx/mn > 1.15)
  print "  WARNING: clock varied >15% across windows — SEC_PER_ITER is not a single constant here" }'
