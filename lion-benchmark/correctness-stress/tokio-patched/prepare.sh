#!/bin/bash
# Materialize the patched Tokio used as the causation control for the "localset"
# configuration: the exact release tokio-latest/ pins (1.52.3), with one repair
# applied and nothing else changed.
#
# Source is the local cargo registry cache, so the bytes are the published crate
# rather than anything we assembled; if the crate is not cached yet, it is
# fetched first. vendor/ is derived output and gitignored, exactly like
# libevent-tests/deps (build_deps.sh).
#
#   ./prepare.sh          # materialize + patch (idempotent: re-materializes)
set -euo pipefail

VER=1.52.3
DIR="$(cd "$(dirname "$0")" && pwd)"
DEST="$DIR/vendor/tokio-$VER"
PATCH="$DIR/localset-rununtil-wake.patch"

find_src() { ls -d "$HOME"/.cargo/registry/src/*/tokio-"$VER" 2>/dev/null | head -1; }

SRC="$(find_src)"
if [ -z "$SRC" ]; then
  echo "tokio $VER not in the registry cache; fetching..."
  TMP="$(mktemp -d)"
  ( cd "$TMP" && cargo init --name fetch_tokio --bin >/dev/null 2>&1 \
    && cargo add tokio@="$VER" --features full >/dev/null 2>&1 )
  rm -rf "$TMP"
  SRC="$(find_src)"
  [ -n "$SRC" ] || { echo "ERROR: could not obtain tokio $VER" >&2; exit 1; }
fi
echo "source: $SRC"

rm -rf "$DEST"
mkdir -p "$(dirname "$DEST")"
cp -r "$SRC" "$DEST"
chmod -R u+w "$DEST"

# The registry copy ships a .cargo-ok marker and a checksum file that make cargo
# treat it as an immutable registry checkout; drop them so it builds as a path
# dependency we are allowed to modify.
rm -f "$DEST/.cargo-ok" "$DEST/.cargo_vcs_info.json"

( cd "$DEST" && git apply --check "$PATCH" 2>/dev/null || patch -p1 --dry-run -s < "$PATCH" ) \
  || { echo "ERROR: patch does not apply to tokio $VER" >&2; exit 1; }
( cd "$DEST" && ( git apply "$PATCH" 2>/dev/null || patch -p1 -s < "$PATCH" ) )

grep -q "discharge that assumption here" "$DEST/src/task/local.rs" \
  || { echo "ERROR: patch reported success but the repair is absent" >&2; exit 1; }

echo "patched tokio $VER ready at $DEST"
