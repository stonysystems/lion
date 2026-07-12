#!/bin/bash
# Shared helpers for the real-world benchmarks. Keeps every <app>/run.sh
# PORTABLE: topology (hosts, remote paths, SSH creds) lives in real-world/hosts.env
# (gitignored) or environment variables — NEVER hardcoded in a committed script.
#
# An <app>/run.sh sources this, calls `bench_setup "$DIR"`, then uses:
#   server_start <log> <cmd...> / server_stop   — run/stop a server by PID (never pkill -f)
#   on_client <cmd...>                           — run a command locally, or on CLIENT_HOST via ssh
#   summarize_raw <raw.csv> <rps_field> <app>    — trimmed-mean -> <...>_summary.csv (paper format)
#
# Knobs (env, with defaults): DURATION, RUNS, OUTDIR, SERVER_HOST, CLIENT_HOST.
# Remote client needs SSH_USER/SSH_PASS (from hosts.env; creds themselves live in
# your gitignored hosts.env; never committed).

bench_setup() {
  # Self-contained toolchain: the pinned rustup env and root-less installs
  # must not depend on the caller's shell profile.
  # shellcheck disable=SC1091
  [ -f "$HOME/.cargo/env" ] && . "$HOME/.cargo/env"
  export PATH="$HOME/.local/bin:$PATH"
  APP_DIR="$(cd "$1" && pwd)"
  RW_DIR="$(cd "$APP_DIR/.." && pwd)"
  # The suite reproduces the PAPER topology exactly: the server app runs on
  # this machine, the load generator on CLIENT_HOST (axum additionally runs
  # its localhost deployment — a paper row — from its own run.sh). Topology
  # comes from real-world/hosts.env (copy hosts.env.example).
  if [ ! -f "$RW_DIR/hosts.env" ]; then
    echo "FATAL: real-world/hosts.env not found — copy hosts.env.example and set SERVER_HOST/CLIENT_HOST/SSH_*" >&2
    exit 2
  fi
  # shellcheck disable=SC1091
  . "$RW_DIR/hosts.env"
  : "${CLIENT_HOST:?hosts.env must set CLIENT_HOST (the load-generator machine)}"
  DURATION="${DURATION:-10}"
  RUNS="${RUNS:-10}"
  SERVER_HOST="${SERVER_HOST:-127.0.0.1}"
  OUTDIR="${OUTDIR:-$APP_DIR/results/$(date +%Y%m%d)-paper}"
  mkdir -p "$OUTDIR"
  echo "[bench] server=$SERVER_HOST client=$CLIENT_HOST out=$OUTDIR"
}

is_local() { [ "$1" = "127.0.0.1" ] || [ "$1" = "localhost" ]; }

# Machine-local cargo target dir for a vendored tree. Building inside an NFS
# home is an order of magnitude slower and collides when several machines
# share one checkout; per-tree dirs under a local root fix both. Override the
# root with BENCH_TARGET_ROOT.
bench_target_dir() {
  local root="${BENCH_TARGET_ROOT:-/tmp/${USER}-lion-bench}"
  mkdir -p "$root/$(basename "$1")"
  echo "$root/$(basename "$1")"
}

# require_client_tool <tool> — fail fast if the load generator is missing on
# the client host (a silent miss would otherwise record rows of zeros).
require_client_tool() {
  local ok=1
  if is_local "$CLIENT_HOST"; then
    command -v "$1" >/dev/null 2>&1 || [ -x "$HOME/.local/bin/$1" ] || ok=0
  else
    on_client "command -v $1 >/dev/null 2>&1 || [ -x \$HOME/.local/bin/$1 ]" || ok=0
  fi
  if [ "$ok" -eq 0 ]; then
    echo "FATAL: '$1' not found on client $CLIENT_HOST (install it there, e.g. run lion-benchmark/setup.sh on the client)" >&2
    exit 3
  fi
}

# client_push <local-file> <remote-abs-path> — stage a binary on the client
# (machine-local build dirs are not visible across hosts; scp the tool over).
client_push() {
  is_local "$CLIENT_HOST" && return 0
  sshpass -p "${SSH_PASS:?}" ssh -o StrictHostKeyChecking=no "${SSH_USER:-$USER}@$CLIENT_HOST"     "mkdir -p $(dirname "$2")"
  sshpass -p "${SSH_PASS:?}" scp -q -o StrictHostKeyChecking=no "$1"     "${SSH_USER:-$USER}@$CLIENT_HOST:$2"
}

# Run a command on the client host: locally, or on CLIENT_HOST over ssh.
on_client() {
  if is_local "$CLIENT_HOST"; then
    "$@"
  else
    sshpass -p "${SSH_PASS:?set SSH_PASS in hosts.env for a remote CLIENT_HOST}" \
      ssh -o StrictHostKeyChecking=no -o ConnectTimeout=20 "${SSH_USER:-$USER}@$CLIENT_HOST" "$@"
  fi
}

SERVER_PID=""
# server_start <logfile> <cmd...> — start a server in the background, track its PID.
server_start() {
  local log="$1"; shift
  "$@" >"$log" 2>&1 &
  SERVER_PID=$!
}
# server_stop — kill ONLY the tracked server (never `pkill -f`, which can match
# and kill the calling shell whose argv contains the binary path). TERM first;
# if the server is still draining after 5 s (e.g. a long graceful-shutdown
# window), escalate to KILL — the per-cell server is disposable and the
# measurement is already on disk.
server_stop() {
  if [ -n "$SERVER_PID" ]; then
    kill "$SERVER_PID" 2>/dev/null || true
    for _ in 1 2 3 4 5; do
      kill -0 "$SERVER_PID" 2>/dev/null || break
      sleep 1
    done
    kill -9 "$SERVER_PID" 2>/dev/null || true
    wait "$SERVER_PID" 2>/dev/null || true
    SERVER_PID=""
  fi
}

# summarize_raw <raw.csv> <rps_field_index> <app>
# Per (runtime,workload) group: THE project-wide statistic — trim-2 (drop the
# two lowest and two highest runs when n > 4, else drop one of each when
# n > 2), mean +/- sample stddev of the kept runs. Identical to micro/plot.py
# so every published number uses one definition. Writes
# <raw_without_suffix>_summary.csv in the paper's format and echoes its path.
summarize_raw() {
  local raw="$1" col="$2" app="$3"
  local out="${raw%_raw.csv}_summary.csv"
  local tmp; tmp="$(mktemp)"
  awk -F, -v C="$col" -v APP="$app" '
    NR==1 { next }
    { k=$2"|"$3; n[k]++; v[k","n[k]]=$C+0; rt[k]=$2; wl[k]=$3 }
    END {
      print "system,runtime,workload,metric,mean,stddev,unit"
      for (k in n) {
        c=n[k]; delete a; for(i=1;i<=c;i++) a[i]=v[k","i]
        for(i=1;i<=c;i++) for(j=i+1;j<=c;j++) if(a[j]<a[i]){t=a[i];a[i]=a[j];a[j]=t}
        trim=(c>4)?2:((c>2)?1:0); lo=1+trim; hi=c-trim; s=0; cnt=0
        for(i=lo;i<=hi;i++){s+=a[i];cnt++}
        m=(cnt>0)?s/cnt:0; ss=0
        for(i=lo;i<=hi;i++){ d=a[i]-m; ss+=d*d }
        sd=(cnt>1)?sqrt(ss/(cnt-1)):0
        printf "%s,%s,%s,throughput,%.2f,%.2f,ops/s\n", APP, rt[k], wl[k], m, sd
      }
    }' "$raw" > "$tmp"
  { head -1 "$tmp"; tail -n +2 "$tmp" | sort; } > "$out"
  rm -f "$tmp"
  echo "$out"
}
