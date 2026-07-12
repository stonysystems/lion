#!/bin/bash
set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
RUMQTT_DIR="$SCRIPT_DIR/.."
DURATION=${DURATION:-30}
PORT_TOKIO=1883
PORT_LION=1884

echo "=== MQTT (rumqttd) Benchmark ==="
echo "Building benchmark tool..."
cd "$SCRIPT_DIR" && cargo build --release 2>&1 | tail -1

echo ""
echo "Building rumqttd (tokio)..."
cd "$RUMQTT_DIR/tokio-rumqtt" && cargo build --release -p rumqttd 2>&1 | tail -1

echo ""
echo "Building rumqttd (lion-v2)..."
cd "$RUMQTT_DIR/lion-v2-rumqtt" && cargo build --release -p rumqttd 2>&1 | tail -1

BENCH="$SCRIPT_DIR/target/release/mqtt-benchmark"
RUMQTTD_TOKIO="$RUMQTT_DIR/tokio-rumqtt/target/release/rumqttd"
RUMQTTD_LION="$RUMQTT_DIR/lion-v2-rumqtt/target/release/rumqttd"

CSV_FILE="$SCRIPT_DIR/results.csv"
echo "system,runtime,workload,pub_throughput_mps,sub_throughput_mps,p50_ms,p95_ms,p99_ms,p999_ms,max_ms" > "$CSV_FILE"

run_with_broker() {
  local runtime=$1
  local broker_bin=$2
  local port=$3
  local config=$4

  echo ""
  echo "--- Running with $runtime runtime (port $port) ---"
  $broker_bin -c "$config" &
  BROKER_PID=$!
  sleep 2

  $BENCH --port "$port" --duration "$DURATION" --runtime "$runtime" --csv 2>/dev/null | grep -v "^system," >> "$CSV_FILE"
  $BENCH --port "$port" --duration "$DURATION" --runtime "$runtime" 2>/dev/null

  kill $BROKER_PID 2>/dev/null || true
  wait $BROKER_PID 2>/dev/null || true
  sleep 1
}

echo ""
echo "NOTE: You need to provide rumqttd config files."
echo "  Example: run_with_broker tokio \$RUMQTTD_TOKIO $PORT_TOKIO path/to/config.toml"
echo "  Example: run_with_broker lion  \$RUMQTTD_LION  $PORT_LION  path/to/config.toml"
echo ""
echo "Or run the benchmark tool directly against a running broker:"
echo "  $BENCH --host 127.0.0.1 --port 1883 --duration $DURATION"
echo ""
echo "Results will be saved to: $CSV_FILE"
