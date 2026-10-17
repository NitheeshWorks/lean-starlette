#!/usr/bin/env bash
# The whole local gate, in the order CI runs it. Exits on the first failure.
#
#   scripts/check.sh            # everything
#   scripts/check.sh --quick    # build, sorry gate, axioms (no tests)
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
LIB=LeanStarlette

echo "== build =="
lake build

echo "== sorry gate =="
if grep -rn --include='*.lean' -w "sorry" "$LIB/"; then
  echo "found 'sorry' under $LIB/: a proof is admitted" >&2; exit 1
fi
echo "none"

echo "== axiom hygiene =="
lake env lean --run scripts/Axioms.lean "$LIB"

[[ "${1:-}" == "--quick" ]] && exit 0

echo "== property tests =="
lake exe props

echo "== conformance =="
lake exe conformance

echo "== traceability =="
python3 scripts/traceability-check.py

if [[ "${1:-}" == "--pbt" ]]; then
  echo "== plausible =="
  (cd tests/pbt && lake build && ./.lake/build/bin/pbt)
fi
echo "all clean"
