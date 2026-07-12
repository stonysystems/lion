#!/bin/bash
set -e

cd "$(dirname "$0")"

if [ -f "$HOME/.cargo/env" ]; then
  . "$HOME/.cargo/env"
fi

echo "=========================================="
echo "lion CI: verify + build"
echo "=========================================="

run_verify() {
  local name="$1"
  echo ""
  echo "######################################################################"
  echo "### [$name] verifying"
  echo "######################################################################"
  (cd "$name" && ./verify.sh)
  echo "### [$name] PASSED"
}

# All verified crates, in dependency order: the shared framework and executor
# specs and the leaf data structures, the reactor and executor that build on
# them, the utility modules, and finally the lion-liveness composing layer.
run_verify lion-framework-spec
run_verify lion-executor-spec
run_verify lion-slab
run_verify lion-timer-wheel
run_verify lion-reactor-spec
run_verify lion-reactor
run_verify lion-executor
run_verify lion-utility
run_verify lion-liveness

echo ""
echo "=========================================="
echo "All checks passed"
echo "=========================================="
