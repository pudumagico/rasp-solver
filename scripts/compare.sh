#!/bin/bash
# Compare rasp-solver vs clingo on benchmark instances.
# Usage: scripts/compare.sh [timeout_seconds]
set -euo pipefail

TIMEOUT="${1:-30}"
RASP="./target/release/asp-solver"
CLINGO="${CLINGO:-clingo}"

cargo build --release --quiet 2>/dev/null

HAS_CLINGO=false
if command -v "$CLINGO" &>/dev/null; then
    HAS_CLINGO=true
    CLINGO_VERSION=$("$CLINGO" --version 2>/dev/null | head -1)
    echo "clingo: $CLINGO_VERSION"
fi

echo "rasp-solver benchmark comparison"
echo "================================"
echo "Timeout: ${TIMEOUT}s"
echo ""

if $HAS_CLINGO; then
    printf "%-25s  %-12s %8s  %-12s %8s  %s\n" "Instance" "rasp" "time" "clingo" "time" "match"
    printf "%-25s  %-12s %8s  %-12s %8s  %s\n" "--------" "----" "----" "------" "----" "-----"
else
    printf "%-25s  %-12s %8s\n" "Instance" "rasp" "time"
    printf "%-25s  %-12s %8s\n" "--------" "----" "----"
fi

TOTAL=0
MATCH=0
RASP_SOLVED=0
CLINGO_SOLVED=0

time_cmd() {
    local solver="$1"
    local file="$2"
    local start end elapsed result

    start=$(perl -e 'use Time::HiRes qw(time); print time' 2>/dev/null || python3 -c "import time; print(time.time())")

    if [ "$solver" = "rasp" ]; then
        result=$(perl -e "alarm $TIMEOUT; exec @ARGV" -- "$RASP" "$file" 2>/dev/null | grep -E 'SAT' || echo "TIMEOUT")
    else
        result=$(perl -e "alarm $TIMEOUT; exec @ARGV" -- "$CLINGO" "$file" -n 1 --outf=0 2>/dev/null | grep -E 'SAT' || echo "TIMEOUT")
    fi

    end=$(perl -e 'use Time::HiRes qw(time); print time' 2>/dev/null || python3 -c "import time; print(time.time())")
    elapsed=$(perl -e "printf '%.3f', $end - $start")

    echo "${result}|${elapsed}"
}

for f in benchmarks/instances/*.lp; do
    name=$(basename "$f" .lp)
    TOTAL=$((TOTAL + 1))

    rasp_out=$(time_cmd "rasp" "$f")
    rasp_result=$(echo "$rasp_out" | cut -d'|' -f1)
    rasp_time=$(echo "$rasp_out" | cut -d'|' -f2)

    if [ "$rasp_result" != "TIMEOUT" ]; then
        RASP_SOLVED=$((RASP_SOLVED + 1))
    fi

    if $HAS_CLINGO; then
        clingo_out=$(time_cmd "clingo" "$f")
        clingo_result=$(echo "$clingo_out" | cut -d'|' -f1)
        clingo_time=$(echo "$clingo_out" | cut -d'|' -f2)

        if [ "$clingo_result" != "TIMEOUT" ]; then
            CLINGO_SOLVED=$((CLINGO_SOLVED + 1))
        fi

        match_str=""
        if [ "$rasp_result" = "$clingo_result" ]; then
            match_str="OK"
            MATCH=$((MATCH + 1))
        elif [ "$rasp_result" = "TIMEOUT" ] || [ "$clingo_result" = "TIMEOUT" ]; then
            match_str="-"
        else
            match_str="MISMATCH"
        fi

        printf "%-25s  %-12s %7ss  %-12s %7ss  %s\n" "$name" "$rasp_result" "$rasp_time" "$clingo_result" "$clingo_time" "$match_str"
    else
        printf "%-25s  %-12s %7ss\n" "$name" "$rasp_result" "$rasp_time"
    fi
done

echo ""
echo "Total instances: $TOTAL"
echo "rasp-solver solved: $RASP_SOLVED"
if $HAS_CLINGO; then
    echo "clingo solved: $CLINGO_SOLVED"
    echo "Results match: $MATCH"
fi
