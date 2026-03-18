#!/bin/bash
# Benchmark runner: time the solver on all instances.
# Usage: scripts/benchmark.sh [timeout_seconds]
set -euo pipefail

TIMEOUT="${1:-30}"
SOLVER="./target/release/asp-solver"
INSTANCES_DIR="./benchmarks/instances"

cargo build --release --quiet 2>/dev/null

echo "ASP Solver Benchmark"
echo "===================="
echo "Timeout: ${TIMEOUT}s per instance"
echo ""
printf "%-35s %8s %10s\n" "Instance" "Result" "Time"
printf "%-35s %8s %10s\n" "--------" "------" "----"

TOTAL=0
PASS=0
TIMEOUT_COUNT=0

for f in "$INSTANCES_DIR"/*.lp; do
    name=$(basename "$f" .lp)
    TOTAL=$((TOTAL + 1))

    start=$(date +%s%N 2>/dev/null || python3 -c "import time; print(int(time.time()*1e9))")

    result=$(timeout "$TIMEOUT" "$SOLVER" "$f" 2>/dev/null | tail -1) || result="TIMEOUT"

    end=$(date +%s%N 2>/dev/null || python3 -c "import time; print(int(time.time()*1e9))")

    elapsed_ms=$(( (end - start) / 1000000 ))

    if [ "$result" = "TIMEOUT" ]; then
        TIMEOUT_COUNT=$((TIMEOUT_COUNT + 1))
        printf "%-35s %8s %9sms\n" "$name" "TIMEOUT" ">${TIMEOUT}000"
    else
        PASS=$((PASS + 1))
        printf "%-35s %8s %9sms\n" "$name" "$result" "$elapsed_ms"
    fi
done

echo ""
echo "Total: $TOTAL | Completed: $PASS | Timeout: $TIMEOUT_COUNT"
