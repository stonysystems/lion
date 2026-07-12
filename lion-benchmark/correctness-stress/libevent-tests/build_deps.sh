#!/bin/bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
DEPS_DIR="$SCRIPT_DIR/deps"

TAGS=("release-2.1.5-beta" "release-2.1.11-stable" "release-2.1.12-stable")

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
      -DCMAKE_C_FLAGS="-Wno-deprecated-declarations" \
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
    CFLAGS="-Wno-deprecated-declarations -O2" \
    ./configure \
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
