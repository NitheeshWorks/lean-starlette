#!/usr/bin/env bash
# Hostile form uploads end to end over TCP, each against a time and a
# peak-memory bound (tests/Bench.lean, `formCases`). Exits 1 on the first
# bound exceeded. Needs curl.
#
#   scripts/bench.sh
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
lake build bench
for c in url200k urlValue20m mpValue20m mpFields50k mpFile50m chunked20m chunkedMpFile50m; do
  ./.lake/build/bin/bench formmem "$c"
done
echo "bench bounds held"
