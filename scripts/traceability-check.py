#!/usr/bin/env python3
"""Validate docs/traceability.toml against the code.

spec -> code : every `realises` and `theorem` symbol resolves in Lean
spec -> test : every `test` path exists
status       : one of implemented | partial | tested | excluded | deviation

  scripts/traceability-check.py [--no-lean]
"""
import subprocess, sys, tomllib
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
LIB = "LeanStarlette"
STATUSES = {"implemented", "partial", "tested", "excluded", "deviation"}

def main():
    doc = tomllib.loads((REPO / "docs" / "traceability.toml").read_text())
    rows = doc.get("requirement", [])
    bad = []
    symbols = []
    for row in rows:
        for k in ("id", "upstream", "title", "status"):
            if k not in row: bad.append(f"{row.get('id','?')}: missing {k}")
        if row.get("status") not in STATUSES: bad.append(f"{row.get('id')}: bad status {row.get('status')}")
        symbols += row.get("realises", []) + row.get("theorem", [])
        for t in row.get("test", []):
            p = t.split("::")[0]
            if not (REPO / p).exists(): bad.append(f"{row['id']}: test path {p} missing")
    if symbols and "--no-lean" not in sys.argv:
        body = f"import {LIB}\n" + "\n".join(f"#check @{s}" for s in sorted(set(symbols)))
        tmp = REPO / ".lake" / "trace-check.lean"; tmp.parent.mkdir(exist_ok=True)
        tmp.write_text(body)
        proc = subprocess.run(["lake", "env", "lean", str(tmp)], cwd=REPO, capture_output=True, text=True)
        for line in (proc.stdout + proc.stderr).splitlines():
            if ": error" in line: bad.append(line.strip())
    print(f"{len(rows)} requirements, {len(set(symbols))} symbols, {len(bad)} problems")
    for b in bad: print("  " + b)
    sys.exit(1 if bad else 0)

if __name__ == "__main__":
    main()
