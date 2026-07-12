#!/bin/bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$SCRIPT_DIR"

TIMEOUT_SECS=${TIMEOUT_SECS:-15}
REPS=${REPS:-3}
TESTS="237_filter 984_phantom 232_ssl combined"
VERSIONS="2.1.5-beta 2.1.11-stable 2.1.12-stable"
RESULTS="$SCRIPT_DIR/results.jsonl"

echo "=========================================="
echo " libevent Correctness Stress Test"
echo " Timeout: ${TIMEOUT_SECS}s per test"
echo "=========================================="

# Build if needed
if [ ! -d build ]; then
  make all 2>&1 | tail -5
fi

> "$RESULTS"

# Header
printf "%-20s" "Test"
for ver in $VERSIONS; do
  printf "%-18s" "$ver"
done
echo ""
printf '%0.s─' {1..74}
echo ""

# Run tests
for test in $TESTS; do
  printf "%-20s" "issue_$test"
  for ver in $VERSIONS; do
    BIN="build/$ver/test_$test"

    if [ ! -f "$BIN" ]; then
      printf "\033[90m%-18s\033[0m" "— SKIP"
      echo "{\"test\":\"issue_${test}\",\"runtime\":\"libevent-${ver}\",\"outcome\":\"SKIP\",\"elapsed_ms\":0}" >> "$RESULTS"
      continue
    fi

    hangs=0; OUTCOME="PASS"
    for ((rep=1; rep<=REPS; rep++)); do
      EXIT_CODE=0
      OUTPUT=$(timeout ${TIMEOUT_SECS}s "$BIN" 2>/dev/null) || EXIT_CODE=$?
      if [ $EXIT_CODE -eq 124 ]; then
        hangs=$((hangs+1)); REP_OUT="HANG"; REP_MS=${TIMEOUT_SECS}000
      elif [ -n "$OUTPUT" ]; then
        REP_OUT=$(echo "$OUTPUT" | python3 -c "import sys,json; print(json.load(sys.stdin).get('outcome','?'))" 2>/dev/null || echo "PASS")
        REP_MS=$(echo "$OUTPUT" | python3 -c "import sys,json; print(json.load(sys.stdin).get('elapsed_ms',0))" 2>/dev/null || echo "0")
      else
        REP_OUT="ERROR"; REP_MS=0
      fi
      echo "{\"test\":\"issue_${test}\",\"runtime\":\"libevent-${ver}\",\"run\":${rep},\"outcome\":\"${REP_OUT}\",\"elapsed_ms\":${REP_MS}}" >> "$RESULTS"
    done
    if [ "$hangs" -gt 0 ]; then OUTCOME="HANG ${hangs}/${REPS}"; else OUTCOME="$REP_OUT"; fi

    case "$OUTCOME" in
      PASS) printf "\033[32m%-18s\033[0m" "✓ PASS" ;;
      HANG) printf "\033[31m%-18s\033[0m" "✗ HANG" ;;
      SKIP) printf "\033[90m%-18s\033[0m" "— SKIP" ;;
      N/A)  printf "\033[90m%-18s\033[0m" "— N/A"  ;;
      *)    printf "%-18s" "$OUTCOME" ;;
    esac
  done
  echo ""
done

echo ""
echo "Results saved to: $RESULTS"
