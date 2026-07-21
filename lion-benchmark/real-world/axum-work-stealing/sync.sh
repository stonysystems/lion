#!/bin/bash
# Push this benchmark's sources to SERVER_HOST (zoo) without touching results.
#
# `results/` is deliberately excluded from --delete: it holds calibration.env,
# which is a measured property of the server host and takes minutes to rebuild.
# A plain `rsync --delete` of the tree wipes it.
set -euo pipefail

DIR="$(cd "$(dirname "$0")" && pwd)"
RW="$(cd "$DIR/.." && pwd)"
[ -f "$RW/hosts.env" ] || { echo "no hosts.env" >&2; exit 1; }
# shellcheck disable=SC1091
. "$RW/hosts.env"

U="${SSH_USER:-$USER}@${SERVER_HOST:?}"
sshpass -p "${SSH_PASS:?}" rsync -az --delete \
  --exclude='target/' --exclude='.git/' --exclude='__pycache__/' --exclude='results/' \
  -e "ssh -o StrictHostKeyChecking=no" \
  "$RW/" "$U:${REMOTE_REPO:?}/lion-benchmark/real-world/"
echo "synced -> $U:$REMOTE_REPO/lion-benchmark/real-world/"
