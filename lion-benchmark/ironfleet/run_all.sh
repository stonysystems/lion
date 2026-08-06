#!/bin/bash
# All four IronFleet cells the paper reports, in one command:
# {lion, csharp} x {unpin, 1core}. Topology and knobs pass through to run.sh.
#
#   ./run_all.sh                                          # localhost
#   SERVER_HOST=<ip> CLIENT_HOST=<ip> ./run_all.sh        # two-host
#   REPS=3 ./run_all.sh                                   # repeat every cell
#
# Cells are interleaved rep-outer (all four cells, then the next repetition) so
# a drift in machine state spreads across arms instead of favouring one.
set -uo pipefail
DIR="$(cd "$(dirname "$0")" && pwd)"
REPS="${REPS:-1}"
STAMP="$(date -u +%Y%m%dT%H%M%SZ)"
OUT="${OUTDIR:-results/$STAMP-paper}"

rc=0
for rep in $(seq 1 "$REPS"); do
  for rt in lion csharp; do
    for cfg in unpin 1core; do
      echo "===== ironfleet $rt/$cfg rep=$rep ====="
      suffix=""; [ "$REPS" -gt 1 ] && suffix=".r$rep"
      (cd "$DIR" && RUNTIME="$rt" CONFIG="$cfg" OUTDIR="$OUT" REP_SUFFIX="$suffix" ./run.sh) \
        || { echo "CELL FAILED: $rt/$cfg rep=$rep"; rc=1; }
    done
  done
done
case "$OUT" in /*) where="$OUT";; *) where="$DIR/$OUT";; esac
echo "===== run_all done (rc=$rc) — results in $where ====="
exit "$rc"
