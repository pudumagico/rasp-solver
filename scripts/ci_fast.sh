#!/bin/bash
# Fast CI script: build + clippy + test (<30s target).
set -euo pipefail

echo "=== cargo clippy ==="
cargo clippy -- -D warnings

echo ""
echo "=== cargo test ==="
cargo test

echo ""
echo "=== cargo build (release) ==="
cargo build --release

echo ""
echo "All checks passed."
