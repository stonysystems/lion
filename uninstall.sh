#!/bin/bash
# Undo what setup.sh installed — and only what it installed.
#
# Both setup.sh scripts append a line to .setup-manifest for each thing they
# actually install, skipping anything the machine already had. This script
# replays that manifest in reverse. Something you had before running setup.sh is
# never touched, because it was never recorded.
#
# It also removes the build artifacts and generated outputs the experiments
# leave behind, which are not in the manifest (nothing installs them) but are
# what "clean the test environment" means in practice.
#
# Usage:
#   ./uninstall.sh              # dry run: print exactly what would be removed
#   ./uninstall.sh --yes        # actually remove it
#   ./uninstall.sh --keep-results   # leave experiment output directories alone
#
# Without a manifest (setup.sh predates it, or was run from another checkout)
# the script falls back to listing the known install locations that exist, and
# refuses to remove them unless you pass --force-no-manifest — it cannot tell
# there which ones were already on the machine.
set -uo pipefail

cd "$(dirname "$0")"
ROOT="$(pwd)"
MANIFEST="$ROOT/.setup-manifest"
BENCH_ROOT="${BENCH_TARGET_ROOT:-/tmp/${USER}-lion-bench}"

APPLY=0 KEEP_RESULTS=0 FORCE_NM=0
for arg in "$@"; do
  case "$arg" in
    --yes|-y)             APPLY=1 ;;
    --keep-results)       KEEP_RESULTS=1 ;;
    --force-no-manifest)  FORCE_NM=1 ;;
    -h|--help)            sed -n '2,20p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "unknown option: $arg (try --help)" >&2; exit 2 ;;
  esac
done

say()  { printf '  %s\n' "$*"; }
plan() { printf '  %-14s %s\n' "$1" "$2"; }

rm_path() {  # rm_path <path> <label>
  [ -e "$1" ] || [ -L "$1" ] || return 0
  if [ "$APPLY" = 1 ]; then rm -rf "$1" && say "removed  $1"
  else plan "$2" "$1"; fi
}

echo "=========================================="
echo "lion uninstall  ($([ "$APPLY" = 1 ] && echo 'applying' || echo 'dry run — pass --yes to apply'))"
echo "=========================================="

# ---------------------------------------------------------------- manifest ---
if [ -f "$MANIFEST" ]; then
  echo ""
  echo "-- installed by setup.sh (from .setup-manifest) --"
  # Reverse order: dependants before what they depend on. macOS has no tac.
  reverse() { if command -v tac >/dev/null 2>&1; then tac "$1"; else tail -r "$1"; fi; }
  reverse "$MANIFEST" | while IFS=$'\t' read -r kind value; do
    [ -n "${kind:-}" ] || continue
    case "$kind" in
      path)   rm_path "$value" "remove" ;;
      rustup)
        if [ "$APPLY" = 1 ]; then
          command -v rustup >/dev/null 2>&1 && rustup self uninstall -y && say "removed  rustup (~/.rustup, ~/.cargo)"
        else plan "rustup" "rustup self uninstall -y  (~/.rustup + ~/.cargo)"; fi ;;
      rustup-toolchain)
        if [ "$APPLY" = 1 ]; then
          rustup toolchain uninstall "$value" >/dev/null 2>&1 && say "removed  rust toolchain $value"
        else plan "rustup" "rustup toolchain uninstall $value"; fi ;;
      pkg-apt)
        if [ "$APPLY" = 1 ]; then sudo apt-get remove -y "$value" && say "removed  apt package $value"
        else plan "apt" "sudo apt-get remove -y $value"; fi ;;
      pkg-dnf)
        if [ "$APPLY" = 1 ]; then sudo dnf remove -y "$value" && say "removed  dnf package $value"
        else plan "dnf" "sudo dnf remove -y $value"; fi ;;
      pkg-pacman)
        if [ "$APPLY" = 1 ]; then sudo pacman -R --noconfirm "$value" && say "removed  pacman package $value"
        else plan "pacman" "sudo pacman -R --noconfirm $value"; fi ;;
      pkg-brew)
        if [ "$APPLY" = 1 ]; then brew uninstall "$value" && say "removed  brew package $value"
        else plan "brew" "brew uninstall $value"; fi ;;
      pip-user)
        if [ "$APPLY" = 1 ]; then python3 -m pip uninstall -y "$value" >/dev/null 2>&1 && say "removed  pip --user $value"
        else plan "pip" "python3 -m pip uninstall -y $value"; fi ;;
      *) say "(unknown manifest entry: $kind $value)" ;;
    esac
  done
else
  echo ""
  echo "-- no .setup-manifest found --"
  echo "   setup.sh records what it installs; without that record this script"
  echo "   cannot tell what was already on this machine. Locations it would"
  echo "   look at, if they exist:"
  for p in "$ROOT/verus-toolchain" "$ROOT/verus.config" \
           "$ROOT/lion-benchmark/micro/.venv" "$HOME/.dafny/dafny-3.4.0" \
           "$HOME/.dotnet" "$HOME/.local/bin/wrk" "$HOME/.local/bin/scons" \
           "$HOME/.local/share/lion-scons-venv"; do
    [ -e "$p" ] && plan "candidate" "$p"
  done
  if [ "$FORCE_NM" = 1 ]; then
    echo "   --force-no-manifest given: removing the paths listed above."
    for p in "$ROOT/verus-toolchain" "$ROOT/verus.config" \
             "$ROOT/lion-benchmark/micro/.venv" "$HOME/.dafny/dafny-3.4.0" \
             "$HOME/.dotnet" "$HOME/.local/bin/wrk" "$HOME/.local/bin/scons" \
             "$HOME/.local/share/lion-scons-venv"; do
      rm_path "$p" "remove"
    done
  else
    echo "   Pass --force-no-manifest to remove them anyway (system packages"
    echo "   such as cmake/wrk/sshpass are never touched in this mode)."
  fi
fi

# ------------------------------------------------------ build + run outputs ---
echo ""
echo "-- build artifacts --"
rm_path "$BENCH_ROOT" "remove"
for d in "$ROOT"/lion-*/target "$ROOT"/mutation-test/target; do rm_path "$d" "remove"; done

if [ "$KEEP_RESULTS" = 0 ]; then
  echo ""
  echo "-- experiment output (NOT the shipped reference data) --"
  for d in "$ROOT"/lion-benchmark/*/results "$ROOT"/lion-benchmark/real-world/*/results; do
    rm_path "$d" "remove"
  done
  rm_path "$ROOT/lion-benchmark/correctness-stress/events.tsv" "remove"
  rm_path "$ROOT/lion-benchmark/correctness-stress/stress_heatmap.pdf" "remove"
  echo "  (ref-result/ and ref-2/ are shipped data and are never removed)"
fi

# ------------------------------------------------------------------- final ---
if [ "$APPLY" = 1 ] && [ -f "$MANIFEST" ]; then rm -f "$MANIFEST"; say "removed  $MANIFEST"; fi

echo ""
echo "=========================================="
if [ "$APPLY" = 1 ]; then
  echo "Done. The repository itself is untouched — delete the clone to finish."
else
  echo "Dry run only. Re-run with --yes to apply."
fi
echo "=========================================="
