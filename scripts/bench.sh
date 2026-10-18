#!/usr/bin/env bash
# Hostile form uploads end to end over TCP, each against a time and a
# peak-memory bound (tests/Bench.lean, `formCases`), then m5's hostile
# inputs (a huge Cookie header, 10 000 CORS origins, large and bomb-shaped
# bodies through GZip) against twice Starlette 1.8.0's warm times
# (tests/golden/m5-bench-starlette-1.8.0.json). Exits 1 on the first bound
# exceeded. Needs curl.
#
#   scripts/bench.sh
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
lake build bench
for c in url200k urlValue20m mpValue20m mpFields50k mpFile50m chunked20m chunkedMpFile50m expectMpFile10m; do
  ./.lake/build/bin/bench formmem "$c"
done
for c in post10m-404 post10m-read post20m-404 post20m-read; do
  ./.lake/build/bin/bench bodybench "$c"
done
./.lake/build/bin/bench m5bench
echo "bench bounds held"
