#!/bin/bash
# mutation-test driver: for each spec in mutants/*.md apply its patch from
# patches/, plain-build (validity), run verify.sh (verdict), record, revert.
# Verdict: CAUGHT iff verify reports a nonzero error count or a compile error.
set -uo pipefail
DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(dirname "$DIR")"
RES="$DIR/RESULTS.md"
mkdir -p "$DIR/results"
echo "| mutant | build | verify | first failure |" > "$RES"
echo "|---|---|---|---|" >> "$RES"
for spec in "$DIR"/mutants/*.md; do
  m=$(basename "$spec" .md)
  if [ $# -ge 1 ] && [ "$m" != "${1%.md}" ] && [ "$m" != "$1" ]; then continue; fi
  patch="$DIR/patches/$m.patch"
  if [ ! -f "$patch" ]; then echo "| $m | - | - | NO PATCH |" >> "$RES"; continue; fi
  crate=$(head -1 "$spec" | sed 's/.*crate: *//')
  git -C "$ROOT" checkout -- lion-timer-wheel/src lion-executor/src lion-reactor/src
  if ! git -C "$ROOT" apply "$patch"; then
    echo "| $m | - | - | PATCH APPLY FAILED |" >> "$RES"; echo "$m: APPLY FAILED"; continue
  fi
  build=OK
  (cd "$ROOT/$crate" && cargo build --release >/dev/null 2>&1) || build=FAIL
  log="$DIR/results/$m-verify.log"
  (cd "$ROOT/$crate" && timeout 900 ./verify.sh > "$log" 2>&1) || true
  if grep -qE "^error(\[|:)" "$log" || grep -qE "verification results:: .* [1-9][0-9]* error" "$log"; then
    verdict=CAUGHT
    first=$(grep -A3 -E "^error(\[|:)" "$log" | grep -oE "src/[a-z_/]+\.rs:[0-9]+" | head -1)
    [ -z "$first" ] && first="(see $m-verify.log)"
  else
    verdict=SURVIVED; first="-"
  fi
  git -C "$ROOT" checkout -- lion-timer-wheel/src lion-executor/src lion-reactor/src
  echo "| $m | $build | $verdict | $first |" >> "$RES"
  echo "$m: build=$build verify=$verdict first=$first"
done
