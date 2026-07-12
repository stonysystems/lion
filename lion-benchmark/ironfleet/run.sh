#!/bin/bash
# IronFleet IronRSL (Multi-Paxos) — Lion async I/O vs C# IoScheduler.
#
# Keeps IronFleet's Dafny-verified Paxos core unchanged and swaps only the I/O
# layer: RUNTIME=lion loads the Lion async cdylib (ironfleet/lion-io) via P/Invoke;
# RUNTIME=csharp uses the original C# IoScheduler. 3-replica cluster + a client
# with NTHREADS concurrent connections, no batching, for DURATION seconds, in the
# two configurations the paper reports (unpinned / pinned to one core per replica).
#
# Prereqs (SETUP_IRONFLEET=1 ../setup.sh): Dafny 3.4.0, .NET 6.0, scons, cargo.
#
# Usage:
#   ./run.sh                                  # RUNTIME=lion CONFIG=unpin, localhost
#   RUNTIME=csharp ./run.sh                   # C# IoScheduler baseline
#   CONFIG=1core ./run.sh                     # pin each replica to one core
#   SERVER_HOST=<server-ip> CLIENT_HOST=<client-ip> ./run.sh   # two-host
#
# Cross-machine note: Zoo shares NFS, so generate certs once on the server side and
# run the client from the same path on CLIENT_HOST (set CLIENT_HOST + SSH_USER/PASS).
set -euo pipefail

DIR="$(cd "$(dirname "$0")" && pwd)"
# shellcheck disable=SC1091
[ -f "$HOME/.cargo/env" ] && . "$HOME/.cargo/env"
# ~/.dotnet first: a system dotnet with a different SDK may exist (on zoo-002 it
# silently produces no DLLs under scons); the setup.sh-installed user SDK wins.
export PATH="$HOME/.dotnet:$HOME/.local/bin:$PATH"
APP="$DIR/ironrsl-app"
CDYLIB="$DIR/lion-io"

RUNTIME="${RUNTIME:-lion}"          # lion | csharp
CONFIG="${CONFIG:-unpin}"           # unpin | 1core
NTHREADS="${NTHREADS:-2}"           # concurrent client connections (paper: 2)
DURATION="${DURATION:-30}"
SERVER_HOST="${SERVER_HOST:-127.0.0.1}"
CLIENT_HOST="${CLIENT_HOST:-$SERVER_HOST}"
if [ -z "${DOTNET:-}" ] && [ -x "$HOME/.dotnet/dotnet" ]; then DOTNET="$HOME/.dotnet/dotnet"; fi
DOTNET="${DOTNET:-dotnet}"
DAFNY_PATH="${DAFNY_PATH:-$HOME/.dafny/dafny-3.4.0/dafny/}"
PORTS=(4001 4002 4003)
SO="libironfleet_io_lion.so"
# OUTDIR: overridable (relative paths resolve against this script's dir);
# REP_SUFFIX distinguishes repetitions of the same cell (e.g. ".r2").
RESULTS_DIR="${OUTDIR:-$DIR/results}"
case "$RESULTS_DIR" in /*) ;; *) RESULTS_DIR="$DIR/$RESULTS_DIR";; esac
mkdir -p "$RESULTS_DIR"
# CRITICAL: unset OUTDIR before any dotnet invocation — MSBuild treats an
# exported OUTDIR as its reserved OutDir property and silently redirects all
# build outputs there (bin/*.dll then never appears).
unset OUTDIR
REP_SUFFIX="${REP_SUFFIX:-}"

command -v "$DOTNET" >/dev/null 2>&1 || { echo "dotnet not found (SETUP_IRONFLEET=1 ../setup.sh)"; exit 1; }
[ "$RUNTIME" = lion ] && LION=true || LION=false

echo "== build Lion I/O cdylib =="
(cd "$CDYLIB" && CARGO_TARGET_DIR="${BENCH_TARGET_ROOT:-/tmp/${USER}-lion-bench}/lion-io" cargo build --release 2>&1 | tail -1)

echo "== build C# IronRSL app (scons --no-verify) =="
# Functional check: on NFS-shared homes ~/.local/bin/scons may exist while this
# machine's python3 lacks the SCons module (per-python site-packages).
scons --version >/dev/null 2>&1 \
  || { echo "scons not functional for this python3 — run: python3 -m pip install --user scons (or SETUP_IRONFLEET=1 ../setup.sh)"; exit 1; }
# Build only the RSL targets we need; the unrelated Lock service does not include
# LionIoScheduler.cs and is not part of this experiment. Full scons output goes
# to a log so silent-no-op failures stay diagnosable.
SCONS_LOG="/tmp/${USER}-ironfleet-scons.log"
(cd "$APP" && scons --dafny-path="$DAFNY_PATH" --no-verify \
  bin/IronRSLCounterServer.dll bin/IronRSLCounterClient.dll bin/CreateIronServiceCerts.dll \
  > "$SCONS_LOG" 2>&1)
tail -3 "$SCONS_LOG"
for dll in IronRSLCounterServer IronRSLCounterClient CreateIronServiceCerts; do
  [ -f "$APP/bin/$dll.dll" ] || {
    echo "build incomplete: bin/$dll.dll missing — full scons output follows"; cat "$SCONS_LOG"; exit 1; }
done

# Make the cdylib discoverable by the .NET process (P/Invoke name ironfleet_io_lion).
cp "${BENCH_TARGET_ROOT:-/tmp/${USER}-lion-bench}/lion-io/release/$SO" "$APP/bin/$SO"
export LD_LIBRARY_PATH="$APP/bin:${LD_LIBRARY_PATH:-}"

cd "$APP"
echo "== generate certs (3 replicas @ $SERVER_HOST:${PORTS[*]}) =="
rm -rf certs
# useSSL=false: the LightRSLClient speaks plain TCP and the benchmark runs without
# SSL (the C# IoScheduler honors this service flag; the Lion cdylib ignores it).
"$DOTNET" bin/CreateIronServiceCerts.dll outputdir=certs name=MyRSL type=IronRSLCounter useSSL=false \
  addr1="$SERVER_HOST" port1="${PORTS[0]}" \
  addr2="$SERVER_HOST" port2="${PORTS[1]}" \
  addr3="$SERVER_HOST" port3="${PORTS[2]}" >/dev/null
SVC="certs/MyRSL.IronRSLCounter.service.txt"

echo "== start 3 servers (RUNTIME=$RUNTIME lion=$LION, CONFIG=$CONFIG) =="
pkill -x dotnet 2>/dev/null || true; sleep 1
for i in 1 2 3; do
  priv="certs/MyRSL.IronRSLCounter.server$i.private.txt"
  pin=""; [ "$CONFIG" = 1core ] && pin="taskset -c $((i-1))"
  # shellcheck disable=SC2086
  $pin "$DOTNET" bin/IronRSLCounterServer.dll "$SVC" "$priv" safeguard=false lion="$LION" \
    > "/tmp/rsl_server$i.log" 2>&1 &
done

echo -n "   waiting for [[READY]] "
READY_FAIL=0
for i in 1 2 3; do
  for _ in $(seq 1 40); do grep -q "\[\[READY\]\]" "/tmp/rsl_server$i.log" 2>/dev/null && break; sleep 0.5; done
  if grep -q "\[\[READY\]\]" "/tmp/rsl_server$i.log" 2>/dev/null; then
    echo -n "s$i "
  else
    echo -n "s$i:NOT-READY "; READY_FAIL=1
  fi
done
echo
if [ "$READY_FAIL" = 1 ]; then
  echo "FATAL: replica(s) never printed [[READY]] — aborting instead of running the client"
  echo "       (see /tmp/rsl_server*.log; a dead lion arm must fail the stage, not exit 0)"
  pkill -x dotnet 2>/dev/null || true
  exit 1
fi

# Archive which I/O arm actually ran (the Lion marker prints before [[READY]];
# the C# baseline prints no marker) so the results dir carries direct evidence.
ARM_LOG="$RESULTS_DIR/${RUNTIME}_${CONFIG}${REP_SUFFIX}.arm"
for i in 1 2 3; do
  m=$(grep -m1 "Using Lion async IO scheduler" "/tmp/rsl_server$i.log" 2>/dev/null || true)
  echo "s$i: ${m:-no-lion-marker (C# IoScheduler arm)}"
done > "$ARM_LOG"
if [ "$RUNTIME" = lion ] && grep -q "no-lion-marker" "$ARM_LOG"; then
  echo "FATAL: RUNTIME=lion but a ready replica lacks the Lion marker — mislabeled arm"
  pkill -x dotnet 2>/dev/null || true
  exit 1
fi

# Sample the servers' CPU during the run (best-effort leader-CPU proxy).
SRV_PIDS=$(pgrep -f IronRSLCounterServer.dll | tr '\n' ',' | sed 's/,$//')
CPU_LOG="/tmp/rsl_cpu.log"; : > "$CPU_LOG"
( for _ in $(seq 1 "$DURATION"); do
    ps -o %cpu= -p "$SRV_PIDS" 2>/dev/null | paste -sd' ' >> "$CPU_LOG"; sleep 1
  done ) &
CPU_SAMPLER=$!

RAW="$RESULTS_DIR/${RUNTIME}_${CONFIG}${REP_SUFFIX}.reqlog"
echo "== run client (nthreads=$NTHREADS duration=${DURATION}s) from $CLIENT_HOST =="
CLIENT_CMD=("$DOTNET" bin/IronRSLCounterClient.dll "$SVC" "nthreads=$NTHREADS" "duration=$DURATION")
if [ "$CLIENT_HOST" = "$SERVER_HOST" ] || [ "$CLIENT_HOST" = 127.0.0.1 ]; then
  "${CLIENT_CMD[@]}" > "$RAW" 2>&1 || true
else
  # remote client over NFS-shared path (set SSH_USER/SSH_PASS for zoo)
  sshpass -p "${SSH_PASS:?set SSH_PASS for remote client}" \
    ssh -o StrictHostKeyChecking=no -o ConnectTimeout=10 "${SSH_USER:?set SSH_USER}@$CLIENT_HOST" \
    "cd '$APP' && LD_LIBRARY_PATH='$APP/bin' ${CLIENT_CMD[*]}" > "$RAW" 2>&1 || true
fi

kill "$CPU_SAMPLER" 2>/dev/null || true
pkill -x dotnet 2>/dev/null || true
# Keep the per-run raw CPU samples next to the reqlog (project rule: per-run
# raw data is archived; summaries are recomputed from it afterwards).
cp "$CPU_LOG" "$RESULTS_DIR/${RUNTIME}_${CONFIG}${REP_SUFFIX}.cpulog" 2>/dev/null || true

echo "== results ($RUNTIME / $CONFIG) =="
python3 - "$RAW" "$DURATION" "$CPU_LOG" <<'PY'
import re, sys
raw, dur, cpulog = sys.argv[1], float(sys.argv[2]), sys.argv[3]
reqs = []
for l in open(raw, errors="ignore"):
    m = re.match(r'#req\s+(\d+)\s+(\d+)\s+([\d.]+)', l)
    if m: reqs.append((int(m.group(1)), int(m.group(2)), float(m.group(3))))
if not reqs:
    print("  no #req lines parsed; see", raw); sys.exit(0)
per = {}
for tid, seq, _ in reqs: per[tid] = max(per.get(tid, 0), seq)
total = sum(per.values())
lats = sorted(l for _, _, l in reqs)
n = len(lats)
# leader CPU proxy: peak per-process %cpu across the sampling window, skipping
# the first 5 samples (ps %cpu is a lifetime average; the .NET startup burst
# inflates the early seconds before decaying to steady state)
peak = 0.0
try:
    for i, line in enumerate(open(cpulog)):
        if i < 5: continue
        for v in line.split():
            try: peak = max(peak, float(v))
            except ValueError: pass
except FileNotFoundError:
    pass
print(f"  Throughput : {total/dur:.0f} req/s   ({total} reqs / {dur:.0f}s)")
print(f"  Avg latency: {sum(lats)/n:.2f} ms   p50 {lats[n//2]:.2f}  p99 {lats[int(n*0.99)]:.2f}")
print(f"  Peak server CPU (leader proxy): {peak:.0f}%")
PY
echo "  raw: $RAW   (compare to benchmark_results.md / paper tab:ironfleet)"
