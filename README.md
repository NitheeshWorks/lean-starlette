# lean-starlette

[![Lean 4](https://img.shields.io/badge/built%20with-Lean%204-blue.svg)](https://lean-lang.org)
[![Proofs](https://img.shields.io/badge/proofs-machine%20checked-brightgreen.svg)](CONTRIBUTING.md#verification)

A clean-room port of [Starlette](https://github.com/Kludex/starlette) to Lean 4: routing, requests, responses and middleware as pure functions with proved matching, header and body invariants; one transport module over Lean core's Std.Http.

Part of the verified FastAPI stack: [lean-fastapi](https://github.com/NitheeshWorks/lean-fastapi)
and its dependencies, each ported as its own repo with its proofs. This one
depends on: [lean-json](https://github.com/NitheeshWorks/lean-json), [lean-multipart](https://github.com/NitheeshWorks/lean-multipart), [lean-itsdangerous](https://github.com/NitheeshWorks/lean-itsdangerous), [lean-httpx](https://github.com/NitheeshWorks/lean-httpx), [lean-jinja2](https://github.com/NitheeshWorks/lean-jinja2).

## What "verified" means here

* Public functions take the weakest precondition they need and return the
  strongest postcondition, as a refinement type `{r // Post r}` or an
  `Except` of one. Invariants live in types, not comments.
* Every theorem is machine-checked. CI fails on `sorry` and on any axiom
  beyond Lean's own `propext`, `Quot.sound` and `Classical.choice`.
* What is tested rather than proved is listed, with the reason, in
  [CONTRIBUTING.md](CONTRIBUTING.md#verification) and in
  `docs/traceability.toml`.

## Getting started

```
lake build            # library, proofs, and both test executables
lake exe props        # property tests (seeded; `lake exe props 42`)
lake exe conformance  # cases re-expressed from the upstream test suite
scripts/check.sh      # the whole CI gate, locally
```

Toolchain: `leanprover/lean4:v4.35.0` (pinned in `lean-toolchain`; `elan` installs it).

## Status

Milestone 0: skeleton, CI gate, cross-repo pins. See the stack plan in
lean-fastapi for the milestones that fill this in.

## License

MIT, see [LICENSE](LICENSE). Upstream attribution is in [NOTICE](NOTICE).
