#!/usr/bin/env bash
# Regression check for Phase 3 Dijkstra fixtures (Lean + Rust).
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
LEAN="$ROOT/formal/lean"

echo "==> Lean: build + fixture guards"
cd "$LEAN"
lake exe cache get 2>/dev/null || true
lake build Sssp.Fixtures.Dijkstra

echo "==> Rust: shared JSON fixtures"
cd "$ROOT"
cargo test shared_json_fixtures --quiet

echo "All fixture checks passed."
