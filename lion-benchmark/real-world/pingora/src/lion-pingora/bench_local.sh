#!/bin/bash
# Local benchmark: Pingora HTTP Echo on Lion runtime
# Varies connections and measures throughput + latency
set -euo pipefail

PINGORA_DIR="$(cd "$(dirname "$0")" && pwd)"
DURATION=10
WRK_THREADS=2

echo "========================================="
echo "  Pingora HTTP Echo — Lion Runtime"
echo "  Duration: ${DURATION}s per test"
echo "  $(date)"
echo "========================================="
echo ""

cd "$PINGORA_DIR"

# Build
echo "Building release..."
cargo build --release --example server -p pingora 2>&1 | tail -3
echo ""

# Start server (NoSteal = Lion, 1 worker thread)
for threads in 1 2 4; do
  cat > /tmp/pingora_bench.yaml << EOF
---
version: 1
threads: $threads
work_stealing: false
EOF

  pkill -f "examples/server" 2>/dev/null || true
  sleep 1

  ./target/release/examples/server -c /tmp/pingora_bench.yaml > /dev/null 2>&1 &
  SERVER_PID=$!
  sleep 3
  # Verify server is up
  curl -s http://127.0.0.1:6145 -d 'ping' > /dev/null 2>&1 || { echo "Server failed to start"; kill $SERVER_PID 2>/dev/null; continue; }

  echo "── Lion, $threads worker thread(s) ──"
  for conns in 10 50 100 500 1000; do
    result=$(wrk -t$WRK_THREADS -c$conns -d${DURATION}s http://127.0.0.1:6145 2>&1)
    rps=$(echo "$result" | grep "Requests/sec" | awk '{print $2}')
    latency=$(echo "$result" | grep "Latency" | awk '{print $2}')
    p99=$(echo "$result" | grep "99%" | awk '{print $2}')
    printf "  conns=%-5d  rps=%-12s  avg_lat=%-10s  p99=%-10s\n" "$conns" "$rps" "$latency" "${p99:-N/A}"
  done
  echo ""

  kill $SERVER_PID 2>/dev/null || true
  wait $SERVER_PID 2>/dev/null || true
done

echo "Complete: $(date)"
