#!/bin/bash
# Agent work loop: autonomous development cycle.
# Run inside a Docker container with the repo mounted.
set -e

AGENT_ID="${AGENT_ID:-agent-1}"

while true; do
    COMMIT=$(git rev-parse --short=6 HEAD)
    LOGFILE="agent_logs/${AGENT_ID}_${COMMIT}.log"
    mkdir -p agent_logs

    echo "[${AGENT_ID}] Starting session at commit ${COMMIT}"

    claude --dangerously-skip-permissions \
        -p "$(cat AGENT_PROMPT.md)" \
        --model claude-opus-4-6 &> "${LOGFILE}" || true

    echo "[${AGENT_ID}] Session complete. Log: ${LOGFILE}"

    # Pull any changes from other agents
    git pull --rebase origin main 2>/dev/null || true
done
