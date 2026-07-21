#!/bin/bash
# Isolate the per-request service path of the two runtimes, with NO queueing.
#
# The sweep shows Lion ahead at low utilisation on BOTH p50 and p99, with the
# two arms at matched clocks -- so it is not DVFS. The leading explanation is
# that Tokio's multi-threaded scheduler parks idle workers, and at low load
# every request pays a wake-up (futex + scheduler + C-state exit) that a
# thread-per-core executor with a resident poller does not.
#
# That hypothesis makes a sharp prediction: the penalty should GROW with the
# idle gap between requests (more time to park and drop into a deeper C-state)
# and VANISH when requests arrive back-to-back. This sweeps exactly that.
#
# Requests are sequential over one keep-alive connection, so there is never more
# than one request in flight and nothing can queue. Any difference is service
# path, not scheduling under load.
#
# Usage:  ./probe_idle.sh            # GAPS in ms, N iterations per request
set -euo pipefail

DIR="$(cd "$(dirname "$0")" && pwd)"
# shellcheck disable=SC1091
. "$DIR/../lib/bench_common.sh"
bench_setup "$DIR"

PORT="${PORT:-8796}"
N="${N:-20000}"
GAPS="${GAPS:-0 1 5 20 100}"
REPS="${REPS:-200}"
CORES="${CORES:-8}"
TARGET_DIR="$(bench_target_dir "$DIR")"
OUT="$OUTDIR/idle_probe.csv"

CPUSET="$(lscpu -p=CPU,CORE | grep -v '^#' | awk -F, '!seen[$2]++{print $1}' | head -"$CORES" | paste -sd,)"
echo "runtime,gap_ms,rep,seconds" > "$OUT"
echo "== idle-gap probe (n=$N, cores=$CORES, cpus=$CPUSET) =="

for rt in tokio lion; do
  bin="$TARGET_DIR/release/ws-$rt"
  [ -x "$bin" ] || { echo "FATAL: $bin missing" >&2; exit 1; }
  for gap in $GAPS; do
    taskset -c "$CPUSET" "$bin" --host 127.0.0.1 --port "$PORT" --cores "$CORES" \
      >"$OUTDIR/idle_$rt.log" 2>&1 &
    SERVER_PID=$!
    for _ in $(seq 1 50); do
      curl -sf -m 2 "http://127.0.0.1:$PORT/health" >/dev/null 2>&1 && break
      sleep 0.2
    done

    # One python process drives the whole gap series over a single connection:
    # a fresh curl per request would add process startup to every sample.
    python3 - "$rt" "$gap" "$N" "$REPS" "$PORT" <<'PY' >> "$OUT"
import http.client, sys, time

rt, gap_ms, n, reps, port = sys.argv[1], float(sys.argv[2]), sys.argv[3], int(sys.argv[4]), int(sys.argv[5])
conn = http.client.HTTPConnection("127.0.0.1", port, timeout=30)
path = f"/work?n={n}"

for _ in range(20):                       # warm the connection and the code path
    conn.request("GET", path); conn.getresponse().read()

out = []
for i in range(reps):
    if gap_ms > 0:
        time.sleep(gap_ms / 1000.0)       # let idle workers park / cores idle
    t = time.perf_counter()
    conn.request("GET", path)
    conn.getresponse().read()
    out.append(time.perf_counter() - t)
conn.close()
for i, s in enumerate(out):
    print(f"{rt},{gap_ms:g},{i},{s:.9f}")
PY
    kill "$SERVER_PID" 2>/dev/null || true
    wait "$SERVER_PID" 2>/dev/null || true
    echo "  $rt gap=${gap}ms done"
    sleep 1
  done
done

python3 - "$OUT" <<'PY'
import csv, statistics, sys
from collections import defaultdict

rows = defaultdict(list)
with open(sys.argv[1]) as fh:
    for r in csv.DictReader(fh):
        rows[(r["runtime"], float(r["gap_ms"]))].append(float(r["seconds"]))

gaps = sorted({g for _, g in rows})
print(f"\n  {'gap(ms)':>8}  {'tokio p50':>11}  {'lion p50':>11}  {'ratio':>7}   "
      f"{'tokio p99':>11}  {'lion p99':>11}")
for g in gaps:
    t = sorted(rows.get(("tokio", g), []))
    l = sorted(rows.get(("lion", g), []))
    if not t or not l:
        continue
    tp50, lp50 = statistics.median(t), statistics.median(l)
    tp99, lp99 = t[int(len(t) * 0.99)], l[int(len(l) * 0.99)]
    print(f"  {g:>8g}  {tp50*1e3:>9.3f}ms  {lp50*1e3:>9.3f}ms  {tp50/lp50:>7.2f}   "
          f"{tp99*1e3:>9.3f}ms  {lp99*1e3:>9.3f}ms")
print("\n  Prediction if idle-worker parking explains the gap: ratio ~1.0 at gap=0")
print("  and rising with the gap. A flat ratio means the difference is in the")
print("  per-request path itself, not in waking a parked scheduler.")
PY
echo "== raw -> $OUT =="
