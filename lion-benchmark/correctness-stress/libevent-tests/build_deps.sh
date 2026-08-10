#!/bin/bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
DEPS_DIR="$SCRIPT_DIR/deps"

TAGS=("release-2.1.5-beta" "release-2.1.11-stable" "release-2.1.12-stable")

# These libevent releases predate the current C toolchain by a decade, so the
# build needs three concessions. They are collected here rather than scattered
# through the invocations below, and the caller's CFLAGS come first so setting
# CFLAGS in the environment still works — hardcoding -DCMAKE_C_FLAGS silently
# discarded it.
#   * CMake 4 refuses a cmake_minimum_required below 3.5; the version-minimum
#     override is the upstream escape hatch. Older CMake ignores the variable.
#   * GCC 14 promoted implicit function declarations from a warning to an error.
#     2.1.5-beta calls arc4random_addrandom(), which a current glibc declares
#     nowhere, so on GCC 14+ it fails to compile at all; suppressing the
#     diagnostic gets it to the link error that src/compat_arc4random.c answers.
#   * The install layout is pinned to lib/ so the Makefiles find the archives on
#     distributions whose default is lib64/.
DEP_CFLAGS="${CFLAGS:-} -Wno-deprecated-declarations -Wno-implicit-function-declaration"

# 2.1.11 and 2.1.12 are configured with OpenSSL enabled, so without the headers
# CMake fails to configure the whole library rather than just the SSL test — a
# 40-line find_package trace that does not name the missing package. Say it here
# instead. (2.1.5-beta is built with SSL off regardless; see below.)
if ! printf '#include <openssl/ssl.h>\n' | "${CC:-cc}" -E -x c - >/dev/null 2>&1; then
  echo "ERROR: the OpenSSL development headers are missing." >&2
  echo "  Debian/Ubuntu: sudo apt-get install libssl-dev" >&2
  echo "  Fedora/RHEL:   sudo dnf install openssl-devel" >&2
  echo "  (../setup.sh installs this for you.)" >&2
  exit 1
fi

mkdir -p "$DEPS_DIR"

for tag in "${TAGS[@]}"; do
  version="${tag#release-}"
  INSTALL_DIR="$DEPS_DIR/$version"

  if [ -f "$INSTALL_DIR/lib/libevent.a" ]; then
    echo "[$version] already built, skipping"
    continue
  fi

  echo "========== Building libevent $version =========="
  SRC_DIR="$DEPS_DIR/src-$version"

  if [ ! -d "$SRC_DIR" ]; then
    git clone --depth 1 --branch "$tag" \
      https://github.com/libevent/libevent.git "$SRC_DIR"
  fi

  mkdir -p "$INSTALL_DIR"

  # 2.1.5-beta's OpenSSL code is incompatible with OpenSSL 3.0
  # (BIO struct became opaque in 1.1.0).  Disable SSL for it.
  case "$version" in
    2.1.5-beta) DISABLE_SSL=ON ;;
    *)          DISABLE_SSL=OFF ;;
  esac

  pushd "$SRC_DIR" >/dev/null
  rm -rf _build

  if [ -f CMakeLists.txt ]; then
    mkdir -p _build && cd _build
    cmake .. \
      -DCMAKE_INSTALL_PREFIX="$INSTALL_DIR" \
      -DCMAKE_INSTALL_LIBDIR=lib \
      -DCMAKE_POLICY_VERSION_MINIMUM=3.5 \
      -DCMAKE_C_FLAGS="$DEP_CFLAGS" \
      -DEVENT__DISABLE_OPENSSL="$DISABLE_SSL" \
      -DEVENT__DISABLE_SAMPLES=ON \
      -DEVENT__DISABLE_TESTS=ON \
      -DEVENT__DISABLE_REGRESS=ON \
      -DEVENT__DISABLE_BENCHMARK=ON \
      -DCMAKE_BUILD_TYPE=Release \
      -DEVENT__LIBRARY_TYPE=STATIC 2>&1 | tail -5
    make -j"$(nproc)" 2>&1 | tail -3
    make install 2>&1 | tail -3
  else
    if [ ! -f configure ]; then
      ./autogen.sh 2>&1 | tail -3
    fi
    SSL_FLAG=""
    [ "$DISABLE_SSL" = "ON" ] && SSL_FLAG="--disable-openssl"
    CFLAGS="$DEP_CFLAGS -O2" \
    ./configure \
      --libdir="$INSTALL_DIR/lib" \
      --prefix="$INSTALL_DIR" \
      --enable-static --disable-shared \
      --disable-samples --disable-libevent-regress \
      $SSL_FLAG 2>&1 | tail -5
    make -j"$(nproc)" 2>&1 | tail -3
    make install 2>&1 | tail -3
  fi

  popd >/dev/null
  echo "[$version] installed to $INSTALL_DIR"
done

# Generate SSL test cert if missing
CERT_DIR="$SCRIPT_DIR"
if [ ! -f "$CERT_DIR/test.crt" ]; then
  echo "Generating self-signed SSL certificate..."
  openssl req -x509 -newkey rsa:2048 \
    -keyout "$CERT_DIR/test.key" -out "$CERT_DIR/test.crt" \
    -days 365 -nodes -subj '/CN=localhost' 2>/dev/null
fi

echo "Done."
