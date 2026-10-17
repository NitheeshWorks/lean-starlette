import LeanStarlette

/-!
# Conformance cases

Each case re-expresses one upstream test (https://github.com/Kludex/starlette, `tests/`) in Lean and
names it, so `docs/traceability.toml` can point at both. The upstream suite is
the behavioural specification; no upstream code is copied.

Run with `lake exe conformance`.
-/

structure Case where
  /-- Upstream test this mirrors, e.g. `tests/test_path.py::test_int`. -/
  upstream : String
  name : String
  run : IO Bool

def cases : List Case := []

def main : IO UInt32 := do
  let mut failures := 0
  for c in cases do
    let ok ← try c.run catch e => do IO.println s!"      {e}"; pure false
    IO.println s!"{if ok then "ok  " else "FAIL"}  {c.name}  [{c.upstream}]"
    unless ok do failures := failures + 1
  IO.println s!"{cases.length} cases, {failures} failing"
  return if failures == 0 then 0 else 1
