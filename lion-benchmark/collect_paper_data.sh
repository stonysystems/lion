#!/bin/bash
# One-command regeneration of the paper's benchmark dataset, in the paper's
# exact topology: rumqtt/axum servers on THIS machine with the load generator
# on CLIENT_HOST (real-world/hosts.env), axum additionally in its localhost
# deployment, pingora fully local (its canonical topology — see pingora/run.sh),
# micro single-machine on this host, ironfleet replicas here + remote client.
#
# Usage:
#   ./collect_paper_data.sh                          # default stages: realworld micro
#   STAGES="realworld micro ironfleet" ./collect_paper_data.sh
#   MICRO_BATCHES=2 ./collect_paper_data.sh          # micro batch count (default 1)
#
# Every stage writes results under <experiment>/results/<UTC-stamp>-<mode>/
# together with a PROVENANCE.txt (commit, host, CPU, kernel, governor, link
# RTT for xmachine, protocol). Real-world runners use the interleaved A-B
# protocol; the shared statistic everywhere is trim-2 mean ± std.
set -uo pipefail
DIR="$(cd "$(dirname "$0")" && pwd)"
STAGES="${STAGES:-realworld micro}"
MICRO_BATCHES="${MICRO_BATCHES:-1}"
DURATION="${DURATION:-30}"          # real-world seconds per run (paper: 30)
MICRO_DURATION="${MICRO_DURATION:-10}"
RUNS="${RUNS:-10}"
STAMP="$(date -u +%Y%m%dT%H%M%SZ)"

provenance() { # <outfile> <protocol-desc>
  {
    echo "commit: $(git -C "$DIR/.." rev-parse --short HEAD)"
    echo "host: $(hostname) ($(lscpu | grep 'Model name' | sed 's/.*: *//'))"
    echo "threads: $(nproc), numa: $(lscpu | awk -F: '/NUMA node\(s\)/{gsub(/ /,"",$2);print $2}')"
    echo "kernel: $(uname -r), governor: $(cat /sys/devices/system/cpu/cpu0/cpufreq/scaling_governor 2>/dev/null || echo unknown)"
    # shellcheck disable=SC1091
    . "$DIR/real-world/hosts.env" 2>/dev/null || true
    # CLIENT_NAME (hosts.env) keeps raw addresses out of committed provenance.
    echo "client: ${CLIENT_NAME:-${CLIENT_HOST:-unset}}, rtt: $(ping -c 3 -q "${CLIENT_HOST:-127.0.0.1}" 2>/dev/null | awk -F/ '/rtt/{print $5" ms"}')"
    echo "protocol: $2"
  } > "$1"
}

run_stage_realworld() {
  # One consolidated pool, ref-result-shaped: <pool>/{rumqtt,pingora,axum}/…
  # plus the exported paper table (md/tex/csv) at the top level.
  local pool="$DIR/real-world/results/$STAMP-paper"
  for app in rumqtt pingora axum; do
    echo "===== [$(date -Is)] real-world/$app ====="
    mkdir -p "$pool/$app"
    (cd "$DIR/real-world/$app" \
      && DURATION="$DURATION" RUNS="$RUNS" OUTDIR="$pool/$app" ./run.sh) \
      || { echo "STAGE FAILED: $app"; return 1; }
    provenance "$pool/$app/PROVENANCE.txt" "interleaved A-B, ${DURATION}s x ${RUNS} runs, trim-2 mean±std"
  done
  echo "===== [$(date -Is)] exporting the paper table ====="
  python3 "$DIR/tools/export_paper_table.py" "$pool"                 > "$pool/table.md"
  python3 "$DIR/tools/export_paper_table.py" "$pool" --format=latex > "$pool/table.tex"
  python3 "$DIR/tools/export_paper_table.py" "$pool" --format=csv   > "$pool/table.csv"
  echo "results + tables: $pool"
}

run_stage_micro() {
  for b in $(seq 1 "$MICRO_BATCHES"); do
    local out="results/$STAMP-batch$b"
    echo "===== [$(date -Is)] micro batch $b/$MICRO_BATCHES ====="
    (cd "$DIR/micro" \
      && mkdir -p "$out" \
      && DURATION="$MICRO_DURATION" RUNS="$RUNS" OUTDIR="$out" \
         MT_THREADS="${MT_THREADS:-1 2 3}" ./run.sh) \
      || { echo "STAGE FAILED: micro batch $b"; return 1; }
    provenance "$DIR/micro/$out/PROVENANCE.txt" "DURATION=${MICRO_DURATION}s x RUNS=${RUNS}, MT_THREADS=${MT_THREADS:-1 2 3}, batch $b/$MICRO_BATCHES"
    # render the paper figure into the batch dir (best-effort: needs the
    # plotting venv from lion-benchmark/setup.sh)
    if [ -x "$DIR/micro/.venv/bin/python" ]; then
      (cd "$DIR/micro" && .venv/bin/python plot.py --data "$out") \
        || echo "WARNING: figure render failed for micro batch $b"
    else
      echo "NOTE: micro/.venv missing — run lion-benchmark/setup.sh, then: micro/plot.py --data micro/$out"
    fi
  done
}

run_stage_ironfleet() {
  local out="results/$STAMP-paper" reps="${IRONFLEET_REPS:-3}"
  # shellcheck disable=SC1091
  . "$DIR/real-world/hosts.env" 2>/dev/null || true
  local shost="${SERVER_HOST:?ironfleet needs SERVER_HOST (real-world/hosts.env)}" chost="${CLIENT_HOST:?and CLIENT_HOST}"
  for rep in $(seq 1 "$reps"); do
    for rt in lion csharp; do
      for cfg in unpin 1core; do
        echo "===== [$(date -Is)] ironfleet $rt/$cfg rep=$rep ====="
        (cd "$DIR/ironfleet" \
          && RUNTIME="$rt" CONFIG="$cfg" OUTDIR="$out" REP_SUFFIX=".r$rep" \
             SERVER_HOST="$shost" CLIENT_HOST="$chost" \
             SSH_USER="${SSH_USER:-}" SSH_PASS="${SSH_PASS:-}" ./run.sh) \
          || { echo "STAGE FAILED: ironfleet $rt/$cfg rep=$rep"; return 1; }
      done
    done
  done
  provenance "$DIR/ironfleet/$out/PROVENANCE.txt" "reps=$reps per cell (interleaved rep-outer), 30s each, cells={lion,csharp}x{unpin,1core}"
}

rc=0
for st in $STAGES; do
  case "$st" in
    realworld) run_stage_realworld || rc=1 ;;
    micro)     run_stage_micro     || rc=1 ;;
    ironfleet) run_stage_ironfleet || rc=1 ;;
    *) echo "unknown stage: $st"; rc=1 ;;
  esac
done
echo "===== collect done (rc=$rc, stamp=$STAMP) ====="
exit "$rc"
