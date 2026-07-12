#!/bin/bash
# Run a real-world benchmark on the configured SERVER_HOST: sync this repo there,
# run <app>/run.sh on it (driving the load from CLIENT_HOST), pull results back.
# All topology/creds come from real-world/hosts.env (gitignored) — see
# hosts.env.example. Usage: lib/remote_launch.sh <pingora|rumqtt|axum>
set -euo pipefail

APP="${1:?usage: remote_launch.sh <pingora|rumqtt|axum>}"
LIB="$(cd "$(dirname "$0")" && pwd)"
RW="$(cd "$LIB/.." && pwd)"
[ -f "$RW/hosts.env" ] || { echo "no hosts.env — cp hosts.env.example hosts.env and edit" >&2; exit 1; }
# shellcheck disable=SC1091
. "$RW/hosts.env"
: "${SERVER_HOST:?set in hosts.env}" "${SSH_PASS:?set in hosts.env}" "${REMOTE_REPO:?set in hosts.env}"

USER_AT="${SSH_USER:-$USER}@$SERVER_HOST"
REPO_ROOT="$(git -C "$RW" rev-parse --show-toplevel)"
RUN_REL="lion-benchmark/real-world/$APP"
ZSSH() { sshpass -p "$SSH_PASS" ssh -o StrictHostKeyChecking=no -o ConnectTimeout=25 "$USER_AT" "$@"; }

# Sync the exact local working tree to the server (push-free), excluding build
# artifacts and git/venv. Incremental after the first run.
echo "==> rsync local repo -> $USER_AT:$REMOTE_REPO (excluding target/.git/.venv)"
ZSSH "mkdir -p '$REMOTE_REPO'"
sshpass -p "$SSH_PASS" rsync -az --delete \
  --exclude='target/' --exclude='.git/' --exclude='.venv/' --exclude='*/node_modules/' \
  -e "ssh -o StrictHostKeyChecking=no" \
  "$REPO_ROOT/" "$USER_AT:$REMOTE_REPO/" 2>&1 | tail -2

echo "==> run $APP/run.sh on $SERVER_HOST (client=$CLIENT_HOST, ${DURATION:-10}s x ${RUNS:-10})"
ZSSH "cd '$REMOTE_REPO/$RUN_REL' && CLIENT_HOST='${CLIENT_HOST:-127.0.0.1}' SSH_USER='${SSH_USER:-}' SSH_PASS='$SSH_PASS' DURATION='${DURATION:-10}' RUNS='${RUNS:-10}' bash run.sh"

echo "==> pull results"
mkdir -p "$RW/$APP/results"
sshpass -p "$SSH_PASS" rsync -az -e "ssh -o StrictHostKeyChecking=no" \
  "$USER_AT:$REMOTE_REPO/$RUN_REL/results/" "$RW/$APP/results/"
echo "Done -> $RW/$APP/results/"
