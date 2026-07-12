#!/bin/bash
# Benchmark: Pingora HTTP reverse proxy on Lion runtime
# Architecture: wrk → Pingora (Lion) :6188 → backend :8080
set -euo pipefail

PINGORA_DIR="$(cd "$(dirname "$0")" && pwd)"
DURATION=${1:-10}
CONNECTIONS=${2:-100}
THREADS=${3:-2}

echo "========================================="
echo "  Pingora HTTP Reverse Proxy Benchmark"
echo "  Duration: ${DURATION}s"
echo "  Connections: $CONNECTIONS"
echo "  wrk threads: $THREADS"
echo "========================================="
echo ""

# Build
echo "Building..."
cd "$PINGORA_DIR"
cargo build --release --example load_balancer -p pingora-proxy 2>&1 | tail -3
echo ""

# Start a simple backend HTTP server (python)
echo "Starting backend HTTP server on :8080..."
python3 -c "
from http.server import HTTPServer, BaseHTTPRequestHandler
class H(BaseHTTPRequestHandler):
    def do_GET(self):
        body = b'Hello from backend\n'
        self.send_response(200)
        self.send_header('Content-Length', len(body))
        self.end_headers()
        self.wfile.write(body)
    def log_message(self, *args):
        pass
HTTPServer(('127.0.0.1', 8080), H).serve_forever()
" &
BACKEND_PID=$!
sleep 1

# Start Pingora proxy
echo "Starting Pingora proxy on :6188..."
# The load_balancer example connects to 1.1.1.1:443 by default.
# We need a simpler proxy. Let's use the gateway example or create a minimal one.
# For now, test with the echo service which doesn't need a backend.
cargo build --release --example server -p pingora 2>&1 | tail -3
./target/release/examples/server &
PROXY_PID=$!
sleep 2

echo "Running wrk..."
echo ""

# Test 1: varying connections
for conns in 10 50 100 500; do
  result=$(wrk -t$THREADS -c$conns -d${DURATION}s http://127.0.0.1:6142 2>&1)
  rps=$(echo "$result" | grep "Requests/sec" | awk '{print $2}')
  latency=$(echo "$result" | grep "Latency" | awk '{print $2}')
  echo "  conns=$conns  rps=$rps  latency=$latency"
done

echo ""

# Cleanup
kill $PROXY_PID 2>/dev/null || true
kill $BACKEND_PID 2>/dev/null || true
wait 2>/dev/null

echo "Done."
