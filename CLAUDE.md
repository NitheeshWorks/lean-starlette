# CLAUDE.md

Guidance for Claude Code in this repository. `README.md` covers usage;
`CONTRIBUTING.md` covers architecture, verification rules and conventions,
and is the document to keep current when the code changes.

A clean-room Lean 4 port of Starlette. Part of the verified FastAPI stack
under github.com/NitheeshWorks (lean-fastapi and its dependencies, one repo each).

## Commands

```
lake build                              # library + proofs + test executables
lake exe props [seed]                   # property tests, < 1 s
lake exe conformance                    # upstream-mirroring cases
lake env lean --run scripts/Axioms.lean LeanStarlette   # axiom hygiene
scripts/check.sh [--quick|--pbt]        # the whole gate
lake env lean LeanStarlette/Proofs/Foo.lean     # check one file (never bare `lean`)
```

## Rules that CI enforces

* No `sorry`, no `partial def`, no `unsafe` under `LeanStarlette/`.
* Every theorem reaches only `propext`, `Quot.sound`, `Classical.choice`.
* Every symbol in `docs/traceability.toml` resolves; every test path exists.

## Commit messages

No `Co-Authored-By:` line and no AI or Claude attribution trailer, in
commits or PR descriptions.

## How to add something

1. Type in `DataTypes/` (invariants as fields), definition in `RepoImpl/`
   (total), property in `Specifications/`, theorem in `Proofs/`, slot in
   `Proofs/Verified.lean`, public function in `APIs/` returning a refinement.
2. A property test in `tests/Props.lean` for anything tested-not-proved, and a
   conformance case in `tests/Conformance.lean` naming the upstream test.
3. A row in `docs/traceability.toml`.
4. Update `CONTRIBUTING.md` if the architecture or the tested-not-proved list
   changed.

Upstream sources are the spec, never copied. Read them from
`/home/nitheesh/Official/NitheeshWorks/upstream-spec/`;
cite the test by path in the conformance case and the traceability row.
