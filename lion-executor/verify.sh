#!/bin/bash
set -e

cd "$(dirname "$0")"
PROJECT_ROOT="$(dirname "$0")/.."

CONFIG_FILE="$PROJECT_ROOT/verus.config"
if [ -f "$CONFIG_FILE" ]; then
  source "$CONFIG_FILE"
else
  echo "Error: Configuration file '$CONFIG_FILE' not found."
  exit 1
fi

if [ -z "$VERUS_PATH" ]; then
  echo "Error: VERUS_PATH is not set in $CONFIG_FILE"
  exit 1
fi

CARGO_VERUS="$VERUS_PATH/cargo-verus"
if [ ! -f "$CARGO_VERUS" ]; then
  echo "Error: cargo-verus not found at $CARGO_VERUS"
  exit 1
fi

echo "Using cargo-verus from: $CARGO_VERUS"
echo ""

start_time=$(date +%s)

echo "=========================================="
echo "Verifying lion-executor-v2..."
echo "=========================================="

"$CARGO_VERUS" build --release "$@"

end_time=$(date +%s)
elapsed=$((end_time - start_time))

echo ""
echo "=========================================="
echo "Verification completed in ${elapsed}s"
echo "=========================================="
