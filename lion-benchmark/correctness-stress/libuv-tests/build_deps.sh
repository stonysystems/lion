#!/bin/bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
DEPS_DIR="$SCRIPT_DIR/deps"

TAGS=("v1.43.0" "v1.44.2")

# See the matching note in ../libevent-tests/build_deps.sh: CMake 4 rejects the
# pre-3.5 minimum these releases declare, GCC 14 turned several legacy patterns
# into errors, and the install layout is pinned to lib/ because the Makefile
# looks there while some distributions default to lib64/. The caller's CFLAGS
# come first so setting CFLAGS in the environment is not discarded.
DEP_CFLAGS="${CFLAGS:-} -Wno-deprecated-declarations -Wno-implicit-function-declaration"

mkdir -p "$DEPS_DIR"

for tag in "${TAGS[@]}"; do
  version="${tag#v}"
  INSTALL_DIR="$DEPS_DIR/$version"

  if [ -f "$INSTALL_DIR/lib/libuv_a.a" ] || [ -f "$INSTALL_DIR/lib/libuv.a" ]; then
    echo "[$version] already built, skipping"
    continue
  fi

  echo "========== Building libuv $version =========="
  SRC_DIR="$DEPS_DIR/src-$version"

  if [ ! -d "$SRC_DIR" ]; then
    git clone --depth 1 --branch "$tag" \
      https://github.com/libuv/libuv.git "$SRC_DIR"
  fi

  mkdir -p "$INSTALL_DIR"

  pushd "$SRC_DIR" >/dev/null
  rm -rf _build && mkdir _build && cd _build

  cmake .. \
    -DCMAKE_INSTALL_PREFIX="$INSTALL_DIR" \
    -DCMAKE_INSTALL_LIBDIR=lib \
    -DCMAKE_POLICY_VERSION_MINIMUM=3.5 \
    -DCMAKE_C_FLAGS="$DEP_CFLAGS" \
    -DCMAKE_BUILD_TYPE=Release \
    -DLIBUV_BUILD_TESTS=OFF \
    -DLIBUV_BUILD_BENCH=OFF 2>&1 | tail -5
  make -j"$(nproc)" 2>&1 | tail -3
  make install 2>&1 | tail -3

  popd >/dev/null
  echo "[$version] installed to $INSTALL_DIR"
done

echo "Done."
