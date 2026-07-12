#!/bin/bash
# Pingora HTTP Echo Benchmark: Lion vs Tokio (NoSteal/thread-per-core)
# Runs on zoo-001. Both versions built from the same Pingora codebase.
# Lion version: work_stealing=false (Lion NoSteal runtime)
# Tokio version: work_stealing=true (Tokio multi-thread, as baseline)
#   Note: Tokio NoSteal is not available since networking code uses lion::net.
#   We compare Lion thread-per-core against Tokio work-stealing.
set -euo pipefail

DIR=/home/users/tzhou/lion/lion-benchmark-v2/pingora
DURATION=10
RUNS=5
PORT=6145
OUTDIR="/tmp/pingora_bench"
mkdir -p "$OUTDIR"

echo "========================================="
echo "  Pingora HTTP Echo Benchmark"
echo "  Duration: ${DURATION}s x ${RUNS} runs"
echo "  $(date)"
echo "========================================="
echo ""

cd "$DIR"
echo "Building..."
cargo build --release --example server -p pingora 2>&1 | tail -3
echo ""

# Install wrk if not present
which wrk > /dev/null 2>&1 || {
  echo "Installing wrk..."
  sudo apt-get install -y wrk 2>/dev/null || {
    git clone https://github.com/wg/wrk.git /tmp/wrk-build && cd /tmp/wrk-build && make -j$(nproc) && sudo cp wrk /usr/local/bin/ && cd "$DIR"
  }
}

RAW="$OUTDIR/raw.csv"
echo "workload,threads,connections,payload,run,rps,latency_avg,latency_p99" > "$RAW"

run_test() {
  local threads=$1 conns=$2 payload_size=$3 label=$4
  local rps_list=()

  cat > /tmp/pingora_bench.yaml << EOF
---
version: 1
threads: $threads
work_stealing: false
EOF

  pkill -f "examples/server" 2>/dev/null || true
  sleep 2

  ./target/release/examples/server -c /tmp/pingora_bench.yaml > /dev/null 2>&1 &
  local PID=$!
  sleep 3

  # Verify server is up
  if ! curl -s http://127.0.0.1:$PORT -d 'ping' > /dev/null 2>&1; then
    echo "  SKIP $label (server failed to start)"
    kill $PID 2>/dev/null || true
    return
  fi

  local wrk_script=""
  if [ "$payload_size" -gt 0 ]; then
    local body=$(python3 -c "print('x' * $payload_size)")
    wrk_script=$(mktemp)
    cat > "$wrk_script" << LUAEOF
wrk.method = "POST"
wrk.body = "$body"
wrk.headers["Content-Type"] = "application/octet-stream"
LUAEOF
  fi

  for run in $(seq 1 $RUNS); do
    local result
    if [ -n "$wrk_script" ]; then
      result=$(wrk -t4 -c$conns -d${DURATION}s -s "$wrk_script" http://127.0.0.1:$PORT 2>&1)
    else
      result=$(wrk -t4 -c$conns -d${DURATION}s http://127.0.0.1:$PORT 2>&1)
    fi
    local rps=$(echo "$result" | grep "Requests/sec" | awk '{print $2}')
    local lat=$(echo "$result" | grep "Latency" | awk '{print $2}')
    local p99=$(echo "$result" | grep "99%" | awk '{print $2}')
    echo "$label,$threads,$conns,$payload_size,$run,$rps,$lat,$p99" >> "$RAW"
    rps_list+=($rps)
  done

  [ -n "$wrk_script" ] && rm -f "$wrk_script"

  local avg_rps=$(printf '%s\n' "${rps_list[@]}" | awk '{s+=$1}END{printf "%.0f",s/NR}')
  printf "  %-30s  threads=%-2d conns=%-5d payload=%-5d  rps=%s\n" "$label" "$threads" "$conns" "$payload_size" "$avg_rps"

  kill $PID 2>/dev/null || true
  wait $PID 2>/dev/null || true
  sleep 2
}

# ══════════════════════════════════════════
# Workload 1: Varying connections (1 thread)
# ══════════════════════════════════════════
echo "### Workload 1: Varying connections (1 thread) ###"
for conns in 10 50 100 500 1000; do
  run_test 1 $conns 0 "lion-1t"
done
echo ""

# ══════════════════════════════════════════
# Workload 2: Varying threads (500 connections)
# ══════════════════════════════════════════
echo "### Workload 2: Varying threads (500 connections) ###"
for threads in 1 2 4; do
  run_test $threads 500 0 "lion-${threads}t"
done
echo ""

# ══════════════════════════════════════════
# Workload 3: Varying payload (1 thread, 100 connections)
# ══════════════════════════════════════════
echo "### Workload 3: Varying payload (1 thread, 100 conns) ###"
for size in 0 64 1024 10240; do
  run_test 1 100 $size "lion-payload-${size}B"
done
echo ""

echo "========================================="
echo "  Complete: $(date)"
echo "  Raw data: $RAW"
echo "========================================="
