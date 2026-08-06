#!/bin/bash
# Axum static-file-server benchmark — Lion (verified runtime) vs Tokio.
# Portable: paths relative to this script; topology from ../hosts.env or env;
# shared orchestration in ../lib/bench_common.sh. Per-run raw CSV (repo policy: per-run raw retained).
#
# Measures throughput (req/s) serving files, each runtime in turn, across the
# small/large/mixed wrk workloads (lua scripts in src/benchmark/). Local by
# default; set CLIENT_HOST / use ../lib/remote_launch.sh for cross-machine.
#
# Usage:  ./run.sh          # DURATION=30s x RUNS=10
#         DURATION=5 RUNS=2 CONNS=50 ./run.sh
set -euo pipefail

DIR="$(cd "$(dirname "$0")" && pwd)"
# shellcheck disable=SC1091
. "$DIR/../lib/bench_common.sh"
bench_setup "$DIR"
require_client_tool wrk
DURATION="${DURATION:-30}"

PORT="${PORT:-8788}"
CONNS="${CONNS:-50}"
ROOT="${BENCH_ROOT:-/tmp/axum-bench-files}"
LUA_DIR="$DIR/src/benchmark"
LION_T="$(bench_target_dir "$DIR/src/lion-axum")"
TOKIO_T="$(bench_target_dir "$DIR/src/tokio-axum")"
LION="$LION_T/release/axum-fileserver"
TOKIO="$TOKIO_T/release/axum-fileserver"
RAW="$OUTDIR/axum_raw.csv"

command -v wrk >/dev/null 2>&1 || { echo "wrk not found — run ../../setup.sh" >&2; exit 1; }

echo "== build =="
(cd "$DIR/src/tokio-axum" && CARGO_TARGET_DIR="$TOKIO_T" cargo build --release 2>&1 | tail -1)
(cd "$DIR/src/lion-axum" && CARGO_TARGET_DIR="$LION_T" cargo build --release 2>&1 | tail -1)

# test files
if [ ! -d "$ROOT/small" ]; then
  echo "== creating test files in $ROOT =="
  mkdir -p "$ROOT/small" "$ROOT/large"
  for i in $(seq 1 100); do dd if=/dev/urandom of="$ROOT/small/f${i}.bin" bs=4096 count=1 2>/dev/null; done
  for i in $(seq 1 100); do dd if=/dev/urandom of="$ROOT/large/f${i}.bin" bs=1024 count=64 2>/dev/null; done
fi

pkill -x axum-fileserver 2>/dev/null || true
sleep 1

WORKLOADS="${WORKLOADS:-small large mixed}"
# Stage the wrk scripts on the client once. The remote wrk must be handed a path
# that exists THERE; a server-side path silently resolves only because our own
# cluster shares an NFS home. A missing script is fatal rather than a fallback
# to one fixed URL — that fallback would run all three workloads against the
# same object and report three near-identical numbers as if they were distinct.
for wl in $WORKLOADS; do
  [ -f "$LUA_DIR/$wl.lua" ] || { echo "FATAL: wrk script $LUA_DIR/$wl.lua missing" >&2; exit 4; }
  client_stage "$LUA_DIR/$wl.lua" >/dev/null
done
# client_lua <workload> — where the client finds that script (no associative
# arrays: this must run under the bash 3.2 that ships on macOS).
client_lua() {
  if is_local "$CLIENT_HOST"; then echo "$LUA_DIR/$1.lua"; else echo "$CLIENT_STAGE_DIR/$1.lua"; fi
}

# transfer_bps/non2xx/sockerr are recorded per run: req/s alone cannot separate
# a link-saturated cell from a 404 storm (an empty-body error sustains a high
# request rate at negligible bandwidth). rps stays field 6 for summarize_raw.
CSV_HEAD="system,runtime,workload,conns,run,rps,latency,transfer_bps,non2xx,sockerr"
echo "$CSV_HEAD" > "$RAW"
echo "== run (server=$SERVER_HOST client=$CLIENT_HOST ${DURATION}s x ${RUNS}) =="
# The paper measures axum in BOTH deployments: cross-machine (bandwidth-bound
# sanity rows) and localhost (the rows that expose runtime differences).
# deployment=cross drives wrk from CLIENT_HOST; deployment=local runs wrk on
# this machine against 127.0.0.1. Interleaved A-B protocol in both (run outer,
# runtime inner, server restart per cell).
RAW_LOCAL="$OUTDIR/axum_local_raw.csv"
echo "$CSV_HEAD" > "$RAW_LOCAL"
# DEPLOYMENTS knob: run a subset (e.g. DEPLOYMENTS=local to (re)collect only
# the localhost rows). Default = both, the paper protocol.
DEPLOYMENTS="${DEPLOYMENTS:-cross local}"
for deployment in $DEPLOYMENTS; do
  for r in $(seq 1 "$RUNS"); do
    for rt in tokio lion; do
      [ "$rt" = tokio ] && BIN="$TOKIO" || BIN="$LION"
      server_start "/tmp/axum_$rt.log" "$BIN" --host 0.0.0.0 --port "$PORT" --root "$ROOT"
      sleep 3
      # 200 AND a non-empty body: `curl -s` alone succeeds on a 404, so the
      # original check passed even when the test files were absent.
      probe=$(curl -s -o /dev/null -m 3 -w '%{http_code} %{size_download}' \
                "http://127.0.0.1:$PORT/small/f1.bin" 2>/dev/null || echo "000 0")
      if [ "${probe% *}" != 200 ] || [ "${probe#* }" -eq 0 ]; then
        echo "  $rt: server not serving files [$probe] ($(tail -1 /tmp/axum_$rt.log))"
        server_stop; continue
      fi
      for wl in $WORKLOADS; do
        if [ "$deployment" = cross ]; then
          target="http://$SERVER_HOST:$PORT"; sink="$RAW"
          out=$(on_client wrk -t2 -c"$CONNS" -d"${DURATION}s" -s "$(client_lua "$wl")" "$target" 2>&1) \
            || { echo "FATAL: wrk failed on client $CLIENT_HOST"; echo "$out"; server_stop; exit 5; }
        else
          target="http://127.0.0.1:$PORT"; sink="$RAW_LOCAL"
          out=$(wrk -t2 -c"$CONNS" -d"${DURATION}s" -s "$LUA_DIR/$wl.lua" "$target" 2>&1) \
            || { echo "FATAL: wrk failed locally"; echo "$out"; server_stop; exit 5; }
        fi
        # wrk EXITS 0 when -s cannot be opened: it warns on stderr and silently
        # falls back to requesting the bare URL, so every response is a 404 and
        # the cell reports a high request rate at negligible bandwidth. Catch
        # the warning itself, not just the symptom below.
        case "$out" in *"cannot open"*)
          echo "FATAL: wrk could not load its Lua script for $deployment/$wl:"
          printf '%s\n' "$out" | grep 'cannot open' | head -2 | sed 's/^/         /'
          echo "       Every request would have degenerated to GET / (a 404)."
          server_stop; exit 5;;
        esac
        IFS=, read -r rps lat tx n2 se <<<"$(wrk_parse "$out")"
        echo "axum,$rt,$wl,$CONNS,$r,$rps,$lat,$tx,$n2,$se" | tee -a "$sink"
        # An error storm must fail the cell, not be recorded as throughput.
        if [ "$n2" -gt 0 ]; then
          echo "FATAL: $deployment/$rt/$wl returned $n2 non-2xx responses at ${tx}B/s —"
          echo "       the client is not receiving file bodies; the number above measures errors."
          echo "       Check that $ROOT/{small,large} are populated and reachable from $CLIENT_HOST."
          server_stop; exit 5
        fi
      done
      server_stop; sleep 2
    done
  done
done
echo "== summary (cross-machine) =="
cat "$(summarize_raw "$RAW" 6 axum)"
echo "== summary (localhost — the paper's Axum-local rows) =="
cat "$(summarize_raw "$RAW_LOCAL" 6 axum)"
