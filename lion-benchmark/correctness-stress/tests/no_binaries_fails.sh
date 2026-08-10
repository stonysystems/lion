#!/bin/bash
# Negative test: a stress runner whose binaries are absent must fail loudly.
#
# This is the check that was missing. Three separate harness defects of the same
# shape reached reviewers — a failed build, a client-side command that never ran,
# and a load generator that fell back to an empty request — each of which
# recorded a plausible-looking result and exited 0. Asserting the *failure* path
# is the only thing that catches that class, so it is asserted here rather than
# left to the next person who runs the suite on a fresh machine.
#
# Usage: ./tests/no_binaries_fails.sh
set -uo pipefail

DIR="$(cd "$(dirname "$0")/.." && pwd)"
FAILURES=0

# The runners try to build what is missing, which would defeat the test (and cost
# a full C build). Shadow make with a no-op so the binaries stay absent; the
# runner must then fail on its own preflight rather than on a build error.
STUB="$(mktemp -d)"
trap 'rm -rf "$STUB"' EXIT
printf '#!/bin/sh\nexit 0\n' > "$STUB/make"
chmod +x "$STUB/make"
export PATH="$STUB:$PATH"

# Hide the built binaries, run the suite, restore them whatever happens.
check() {
  local name="$1" runner="$2" build="$3"
  local stash="" rc=0 out=""

  if [ -d "$build" ]; then
    stash="${build}.negtest-stash"
    rm -rf "$stash"
    mv "$build" "$stash"
  fi

  # ALLOW_MISSING is deliberately unset: the default must be fatal.
  out="$(cd "$(dirname "$runner")" && timeout 300 ./"$(basename "$runner")" 2>&1)" || rc=$?

  if [ -n "$stash" ]; then
    rm -rf "$build"
    mv "$stash" "$build"
  fi

  if [ "$rc" -eq 0 ]; then
    echo "FAIL  $name: exited 0 with no binaries present"
    echo "$out" | tail -5 | sed 's/^/        /'
    FAILURES=$((FAILURES+1))
  else
    echo "ok    $name: exited $rc with no binaries present"
  fi
}

check libevent "$DIR/libevent-tests/run.sh" "$DIR/libevent-tests/build"
check libuv    "$DIR/libuv-tests/run.sh"    "$DIR/libuv-tests/build"

echo ""
if [ "$FAILURES" -gt 0 ]; then
  echo "$FAILURES runner(s) reported success without measuring anything."
  exit 1
fi
echo "All runners fail loudly when their binaries are absent."
