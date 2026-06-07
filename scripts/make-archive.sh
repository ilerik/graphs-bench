#!/usr/bin/env bash
# Build a reproducible source archive from tracked Git files.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
REF="${1:-HEAD}"
SHORT_SHA="$(git -C "$ROOT" rev-parse --short "$REF")"
OUT_DIR="$ROOT/dist"
NAME="graphs-bench-$SHORT_SHA"
ARCHIVE="$OUT_DIR/$NAME.tar.gz"

mkdir -p "$OUT_DIR"
git -C "$ROOT" archive --format=tar.gz --prefix="$NAME/" -o "$ARCHIVE" "$REF"
sha256sum "$ARCHIVE" > "$ARCHIVE.sha256"

echo "$ARCHIVE"
echo "$ARCHIVE.sha256"
