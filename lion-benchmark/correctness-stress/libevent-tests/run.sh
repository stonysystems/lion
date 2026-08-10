#!/bin/bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$SCRIPT_DIR"

TIMEOUT_SECS=${TIMEOUT_SECS:-15}
REPS=${REPS:-3}
TESTS="237_filter 984_phantom 232_ssl combined"
VERSIONS="2.1.5-beta 2.1.11-stable 2.1.12-stable"
RESULTS="$SCRIPT_DIR/results.jsonl"

# A cell with no binary is not a data point. Recording it as SKIP and exiting 0
# turned a failed dependency build into a run that looked complete: the matrix
# printed in milliseconds with every cell blank, and nothing said the
# measurements were absent rather than empty. Missing binaries are fatal now.
# ALLOW_MISSING=1 restores the degrade-and-continue behaviour for a partial
# toolchain, and even then the run exits non-zero.
ALLOW_MISSING="${ALLOW_MISSING:-0}"

# One cell is legitimately unmeasurable rather than unbuilt: 2.1.5-beta cannot
# compile the SSL test against OpenSSL 3.0 (opaque BIO struct), so it has no
# binary by design and both reference batches record it. Expected gaps are
# listed here as <version>:<test>; they are excluded from the preflight and
# from the exit status, and print as N/A rather than SKIP so the two cases are
# distinguishable on sight. Any other missing binary is a failed build.
EXPECTED_NA="2.1.5-beta:232_ssl"

is_expected_na() {  # <version> <test>
  case " $EXPECTED_NA " in *" $1:$2 "*) return 0 ;; esac
  return 1
}

echo "=========================================="
echo " libevent Correctness Stress Test"
echo " Timeout: ${TIMEOUT_SECS}s per test"
echo "=========================================="

# Each test reports its verdict as a line of JSON that this script parses with
# python3. Without it every cell that ran would be recorded as unreadable, which
# is accurate but says nothing about the cause — and before the outcome handling
# was tightened it was worse than that, since an unparseable result counted as a
# pass and a machine with no python3 produced a table of them.
if ! command -v python3 >/dev/null 2>&1; then
  echo "ERROR: python3 is required to read each test's JSON verdict." >&2
  echo "  Debian/Ubuntu: sudo apt-get install python3" >&2
  exit 1
fi

expected_bins() {
  for t in $TESTS; do
    for v in $VERSIONS; do
      is_expected_na "$v" "$t" || echo "build/$v/test_$t"
    done
  done
}
list_missing() {
  local b
  MISSING=()
  while read -r b; do [ -f "$b" ] || MISSING+=("$b"); done < <(expected_bins)
}

# Keying the build on the build/ directory alone let a half-built tree skip the
# build entirely, which is how every cell came to be missing at once.
list_missing
if [ ${#MISSING[@]} -gt 0 ]; then
  # A build failure is reported by the preflight below rather than aborting
  # here, so the message names what is missing and how to get it.
  make all 2>&1 | tail -5 || true
  list_missing
fi
if [ ${#MISSING[@]} -gt 0 ]; then
  echo ""
  echo "ERROR: ${#MISSING[@]} test binaries did not build:"
  printf '  %s\n' "${MISSING[@]}"
  echo "Build the C dependencies first (../build_deps.sh), then 'make all' here."
  if [ "$ALLOW_MISSING" != 1 ]; then exit 1; fi
  echo "ALLOW_MISSING=1: continuing; those cells are SKIP and this run still exits non-zero."
fi

INVALID=0
CELLS=0

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
    CELLS=$((CELLS+1))

    if [ ! -f "$BIN" ]; then
      if is_expected_na "$ver" "$test"; then
        # outcome stays SKIP so the archived reference batches remain
        # byte-comparable; the flag is what distinguishes it.
        printf "\033[90m%-18s\033[0m" "— N/A"
        echo "{\"test\":\"issue_${test}\",\"runtime\":\"libevent-${ver}\",\"outcome\":\"SKIP\",\"expected\":true,\"elapsed_ms\":0}" >> "$RESULTS"
      else
        printf "\033[90m%-18s\033[0m" "— SKIP"
        echo "{\"test\":\"issue_${test}\",\"runtime\":\"libevent-${ver}\",\"outcome\":\"SKIP\",\"elapsed_ms\":0}" >> "$RESULTS"
        INVALID=$((INVALID+1))
      fi
      continue
    fi

    hangs=0; errors=0; OUTCOME="PASS"
    for ((rep=1; rep<=REPS; rep++)); do
      EXIT_CODE=0
      OUTPUT=$(timeout ${TIMEOUT_SECS}s "$BIN" 2>/dev/null) || EXIT_CODE=$?
      if [ $EXIT_CODE -eq 124 ]; then
        hangs=$((hangs+1)); REP_OUT="HANG"; REP_MS=${TIMEOUT_SECS}000
      elif [ -n "$OUTPUT" ]; then
        # Output we cannot parse is not a result. This used to fall back to
        # PASS, so a binary emitting anything unexpected on stdout was recorded
        # as a success.
        REP_OUT=$(echo "$OUTPUT" | python3 -c "import sys,json; print(json.load(sys.stdin).get('outcome','ERROR'))" 2>/dev/null || echo "ERROR")
        REP_MS=$(echo "$OUTPUT" | python3 -c "import sys,json; print(json.load(sys.stdin).get('elapsed_ms',0))" 2>/dev/null || echo "0")
        if [ "$REP_OUT" = ERROR ]; then errors=$((errors+1)); fi
      else
        REP_OUT="ERROR"; REP_MS=0; errors=$((errors+1))
      fi
      echo "{\"test\":\"issue_${test}\",\"runtime\":\"libevent-${ver}\",\"run\":${rep},\"outcome\":\"${REP_OUT}\",\"elapsed_ms\":${REP_MS}}" >> "$RESULTS"
    done
    # A binary that runs but produces no parseable output is as absent as one
    # that never built; it must not pass silently either.
    if [ "$errors" -gt 0 ]; then INVALID=$((INVALID+1)); fi
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

# The invariant: a run that produced no valid measurement must not exit 0.
if [ "$INVALID" -gt 0 ]; then
  echo "FAILED: $INVALID of $CELLS cells produced no valid measurement (missing binary or no output)."
  exit 1
fi
