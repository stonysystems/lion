#!/bin/bash
# Set up everything needed to build/run the benchmarks and plot the figure:
#   - cmake    : build dependency for the real-world apps' native deps (e.g.
#                pingora's zlib-ng / libz-ng-sys),
#   - wrk      : HTTP load generator for the pingora / axum real-world benchmarks,
#   - OpenSSL headers : the C differential tests build upstream libevent with
#                SSL enabled; the openssl binary alone does not suffice,
#   - sshpass  : non-interactive password SSH to the client host for the
#                cross-machine real-world runs (credentials live only in your
#                gitignored real-world/hosts.env),
#   - a local Python virtualenv (.venv) with matplotlib + numpy for plot.py.
#
# Opt-in (SETUP_IRONFLEET=1) additionally installs the IronFleet experiment
# toolchain — the C# IronRSL/Paxos app is Dafny-generated and built with scons:
#   - Dafny 3.4.0 (exactly 3.4) into ~/.dafny,
#   - .NET 6.0 SDK into ~/.dotnet,
#   - scons (pip --user).
# The Lion async I/O layer (ironfleet/lion-io) itself only needs cargo.
#
# Usage (run from anywhere; paths resolve relative to this script):
#   ./setup.sh                     # micro + real-world deps
#   SETUP_IRONFLEET=1 ./setup.sh   # also the IronFleet (Dafny/.NET/scons) toolchain
#   then:  ./micro/.venv/bin/python micro/plot.py
#
# The micro benchmark itself needs only a Rust toolchain (cargo); cmake/wrk are
# for the real-world apps, sshpass is for the zoo cross-machine runs, and the
# .venv is purely for plot.py.
set -euo pipefail

DIR="$(cd "$(dirname "$0")" && pwd)"
MICRO="$DIR/micro"
VENV="$MICRO/.venv"

APT_UPDATED=0

# Installation manifest — records ONLY what this script actually installs, so
# ../uninstall.sh can undo exactly that and leave anything the machine already
# had alone. Shared with the top-level setup.sh.
MANIFEST="$(cd "$DIR/.." && pwd)/.setup-manifest"
record() {  # idempotent: re-running setup.sh must not duplicate entries
  local line; line="$(printf '%s\t%s' "$1" "$2")"
  grep -qxF "$line" "$MANIFEST" 2>/dev/null || printf '%s\n' "$line" >> "$MANIFEST"
}

# install_pkg <label> <apt-pkg> [dnf-pkg] [pacman-pkg] [brew-pkg]
# Install a package with whatever package manager is available. Best-effort:
# warns (does not abort) if none works.
install_pkg() {
  local cmd="$1" apt_pkg="$2" dnf_pkg="${3:-$2}" pac_pkg="${4:-$2}" brew_pkg="${5:-$2}"
  if command -v apt-get >/dev/null 2>&1; then
    if [ "$APT_UPDATED" -eq 0 ]; then sudo apt-get update -qq && APT_UPDATED=1; fi
    echo "Installing $apt_pkg via apt-get ..."
    sudo apt-get install -y "$apt_pkg" && record pkg-apt "$apt_pkg" \
      || echo "Warning: failed to install $apt_pkg." >&2
  elif command -v dnf >/dev/null 2>&1; then
    echo "Installing $dnf_pkg via dnf ..."
    sudo dnf install -y "$dnf_pkg" && record pkg-dnf "$dnf_pkg" \
      || echo "Warning: failed to install $dnf_pkg." >&2
  elif command -v pacman >/dev/null 2>&1; then
    echo "Installing $pac_pkg via pacman ..."
    sudo pacman -S --noconfirm "$pac_pkg" && record pkg-pacman "$pac_pkg" \
      || echo "Warning: failed to install $pac_pkg." >&2
  elif command -v brew >/dev/null 2>&1; then
    echo "Installing $brew_pkg via brew ..."
    brew install "$brew_pkg" && record pkg-brew "$brew_pkg" \
      || echo "Warning: failed to install $brew_pkg." >&2
  else
    echo "Warning: no known package manager; install '$cmd' manually." >&2
  fi
}

# ensure_tool <command> <apt-pkg> [dnf-pkg] [pacman-pkg] [brew-pkg]
ensure_tool() {
  local cmd="$1"
  if command -v "$cmd" >/dev/null 2>&1; then
    echo "$cmd already installed."
    return 0
  fi
  install_pkg "$@"
}

# The libevent differential tests (correctness-stress/libevent-tests) build
# upstream libevent with OpenSSL enabled, so they need the OpenSSL *headers* —
# not the openssl binary, which nearly every machine already has, so a
# command-presence check would pass on a host that cannot build them. Missing
# headers make CMake fail to configure 2.1.11 and 2.1.12 outright, not just the
# one SSL test, which is a confusing way to learn a package is absent.
openssl_headers_present() {
  local cc; cc="$(command -v cc 2>/dev/null || command -v gcc 2>/dev/null || true)"
  [ -n "$cc" ] || return 1
  printf '#include <openssl/ssl.h>\n' | "$cc" -E -x c - >/dev/null 2>&1
}
ensure_openssl_dev() {
  if openssl_headers_present; then
    echo "OpenSSL headers already installed."
    return 0
  fi
  install_pkg "OpenSSL headers" libssl-dev openssl-devel openssl openssl
}

# --- System tools for building and running the benchmarks ---
ensure_tool cmake   cmake
ensure_tool wrk     wrk
ensure_openssl_dev

# wrk has no package on every distro and apt needs root; when it is still
# missing, build from source into ~/.local/bin (bench_setup puts that on PATH).
if ! command -v wrk >/dev/null 2>&1 && [ ! -x "$HOME/.local/bin/wrk" ]; then
  echo "Building wrk from source into ~/.local/bin ..."
  mkdir -p "$HOME/.local/bin"
  tmpd="$(mktemp -d)"
  if git clone -q --depth 1 https://github.com/wg/wrk "$tmpd/wrk"     && make -C "$tmpd/wrk" -j"$(nproc)" >/dev/null 2>&1     && cp "$tmpd/wrk/wrk" "$HOME/.local/bin/"; then
    echo "wrk -> $HOME/.local/bin/wrk"
    record path "$HOME/.local/bin/wrk"
  else
    echo "WARNING: wrk source build failed; pingora/axum benches need wrk on PATH"
  fi
  rm -rf "$tmpd"
fi
ensure_tool sshpass sshpass

if ! command -v python3 >/dev/null 2>&1; then
  echo "Error: python3 is required but not found" >&2
  exit 1
fi

# --- Ensure the venv module is usable (Debian/Ubuntu split it into python3-venv) ---
if ! python3 -c "import ensurepip" >/dev/null 2>&1; then
  echo "python venv module (ensurepip) missing; installing ..."
  if command -v apt-get >/dev/null 2>&1; then
    sudo apt-get install -y python3-venv
  elif command -v dnf >/dev/null 2>&1; then
    sudo dnf install -y python3-pip
  else
    echo "Warning: could not auto-install the venv module; install python3-venv manually." >&2
  fi
fi

echo "Creating virtualenv at $VENV ..."
python3 -m venv --clear "$VENV"
record path "$VENV"

echo "Installing plotting dependencies (matplotlib, numpy) ..."
"$VENV/bin/python" -m pip install --upgrade pip >/dev/null
# Version-bounded (see plotting-requirements.txt) so that a future major release
# cannot break plot.py on a machine setting this up later.
"$VENV/bin/python" -m pip install -r "$DIR/plotting-requirements.txt" \
  || { echo "Warning: bounded install failed; falling back to unpinned." >&2
       "$VENV/bin/python" -m pip install matplotlib numpy; }
"$VENV/bin/python" -m pip freeze 2>/dev/null \
  | grep -iE '^(matplotlib|numpy)==' | sed 's/^/  installed: /'

# --- Opt-in: IronFleet experiment toolchain (Dafny 3.4.0 + .NET 6.0 + scons) ---
# Best-effort, idempotent; only the C# IronRSL app needs these. The Lion async I/O
# cdylib (ironfleet/lion-io) builds with plain cargo.
if [ "${SETUP_IRONFLEET:-0}" = "1" ]; then
  echo ""
  echo "=== IronFleet toolchain (SETUP_IRONFLEET=1) ==="

  # scons (build driver for the Dafny->C# app). Functional check, not just
  # presence: on NFS-shared homes ~/.local/bin/scons may have been installed by
  # a machine with a different python3, whose SCons site-packages this one
  # cannot import.
  if PATH="$HOME/.local/bin:$PATH" scons --version >/dev/null 2>&1; then
    echo "scons already installed."
  else
    echo "Installing scons (pip --user) ..."
    # Debian/Ubuntu ship no pip for the system python and disable ensurepip for
    # it, so `python3 -m pip` fails outright there; a private venv is the
    # root-less way that works on a stock image. (scons runs standalone from
    # its own venv — nothing else imports it.)
    if python3 -m pip install --user scons 2>/dev/null \
       || python3 -m pip install --user --break-system-packages scons 2>/dev/null; then
      record pip-user scons
    else
      SCONS_VENV="$HOME/.local/share/lion-scons-venv"
      echo "  no usable system pip; installing scons into $SCONS_VENV ..."
      if python3 -m venv "$SCONS_VENV" \
         && "$SCONS_VENV/bin/pip" install -q --upgrade pip \
         && "$SCONS_VENV/bin/pip" install -q scons \
         && mkdir -p "$HOME/.local/bin" \
         && ln -sf "$SCONS_VENV/bin/scons" "$HOME/.local/bin/scons"; then
        record path "$SCONS_VENV"
        record path "$HOME/.local/bin/scons"
      else
        echo "Warning: failed to install scons; install manually." >&2
      fi
    fi
    echo "  (ensure ~/.local/bin is on PATH)"
  fi

  # Dafny 3.4.0 — must be exactly 3.4 (not 3.13+); install into ~/.dafny
  DAFNY_DIR="$HOME/.dafny/dafny-3.4.0"
  if [ ! -f "$DAFNY_DIR/dafny/Dafny.dll" ]; then
    echo "Installing Dafny 3.4.0 into $DAFNY_DIR ..."
    mkdir -p "$HOME/.dafny"
    ZIP="$HOME/.dafny/dafny-3.4.0.zip"
    if command -v wget >/dev/null 2>&1; then
      wget -q "https://github.com/dafny-lang/dafny/releases/download/v3.4.0/dafny-3.4.0-x64-ubuntu-16.04.zip" -O "$ZIP" \
        && unzip -q -o "$ZIP" -d "$DAFNY_DIR" && rm -f "$ZIP" \
        && record path "$DAFNY_DIR" \
        && echo "  Dafny -> $DAFNY_DIR/dafny/Dafny.dll" \
        || echo "Warning: Dafny 3.4.0 download/unzip failed; install manually." >&2
    else
      echo "Warning: wget not found; cannot fetch Dafny 3.4.0." >&2
    fi
  else
    echo "Dafny 3.4.0 already installed at $DAFNY_DIR."
  fi

  # .NET 6.0 SDK — install into ~/.dotnet via the official script
  if ! command -v dotnet >/dev/null 2>&1 && [ ! -x "$HOME/.dotnet/dotnet" ]; then
    echo "Installing .NET 6.0 SDK into ~/.dotnet ..."
    SCRIPT="/tmp/dotnet-install.sh"
    if command -v curl >/dev/null 2>&1; then
      curl -fsSL https://dot.net/v1/dotnet-install.sh -o "$SCRIPT"
    elif command -v wget >/dev/null 2>&1; then
      wget -q https://dot.net/v1/dotnet-install.sh -O "$SCRIPT"
    fi
    if [ -f "$SCRIPT" ]; then
      bash "$SCRIPT" --channel 6.0 --install-dir "$HOME/.dotnet" \
        && record path "$HOME/.dotnet" \
        && echo "  .NET -> $HOME/.dotnet/dotnet (add to PATH)" \
        || echo "Warning: .NET 6.0 install failed; install manually." >&2
      rm -f "$SCRIPT"
    else
      echo "Warning: could not fetch dotnet-install.sh." >&2
    fi
  else
    echo ".NET SDK already installed."
  fi
  echo "=== IronFleet toolchain done ==="
fi

echo ""
echo "Done. Generate the figure with:"
echo "  $VENV/bin/python $MICRO/plot.py            # uses ref_result/ -> micro_bench.pdf"
echo "  $VENV/bin/python $MICRO/plot.py --data results/full"
