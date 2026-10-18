# Contributing to lean-starlette

`README.md` covers usage. This file covers the architecture, the verification
rules, the repository layout and the conventions, and is the document to keep
current when the code changes.

## Architecture

`LeanStarlette/` is layered bottom-up; each layer imports only the ones below it, so a
proof at one layer rewrites with lemmas from beneath it instead of unfolding
to bytes:

| Directory | Holds | Proved? |
|---|---|---|
| `DataTypes/` | structures and inductives; invariants are fields | n/a |
| `RepoImpl/` | executable definitions; total, structural recursion | subject of proofs |
| `Specifications/` | the properties, in `Prop` | the contract |
| `Proofs/` | theorems; `Proofs/Verified.lean` bundles one `Verified<Layer>` per layer | yes |
| `APIs/` | the public surface, returning refinements | by construction |
| `Transport.lean` | the only effectful module: `Std.Http` conversion and serving | no; tested |

Everything except the transport module is a pure function. This is
load-bearing: a round-trip property of a function is an equation that
`omega` and `simp` attack directly; the same property of a procedure would
be a Hoare triple over a heap.

## Verification <a name="verification"></a>

* **Weak preconditions, strong postconditions.** A public function takes the
  minimal hypothesis its body needs (usually none; the refinement lives in the
  input type) and returns the strongest useful statement, typically a round
  trip or a membership, as `{r // Post r}` or `Except Err {r // Post r}`.
* **Refinement types are subtypes with `Decidable` predicates**, so the same
  predicate is checked at runtime (`if h : P x`) and used in proofs.
* **Totality.** No `partial def` or `unsafe` under `LeanStarlette/`, and
  `scripts/gate-allow.txt` is empty. The transport calls
  `Std.Http.Server.serve`, whose accept loop lives in Lean core, so this
  library has no loop of its own. Everything that reads request input
  (percent-decoding, UTF-8, query strings, the `Host` header, header lookup)
  is structural recursion over the input, linear in its length; `Std.Http`
  bounds the URI (8 KiB), header count and size, and the body (64 MiB, or
  `max_body_size`). JSON bodies go through lean-json, whose parser has a
  depth limit; a body over it is a `400`. No request parser uses
  `Keel.Parse.fix`.
* **`_ext` lemmas.** A decoder lemma holds on any continuation of the buffer and
  reports the final position, so field lemmas compose. Do not add a lemma that
  only holds at the end of a buffer; it is unusable one field later.
* **Numbers.** `Nat`/`Int`/decimal-as-rational in proofs. `Float` only at the
  boundary via `Float.toBits`. Never `bv_decide` or `native_decide`.
* **The gate.** `scripts/check.sh` runs what CI runs: build, `sorry` grep,
  `scripts/Axioms.lean` (every theorem under `LeanStarlette` reaches only `propext`,
  `Quot.sound`, `Classical.choice`), `lake exe props`, `lake exe conformance`,
  the traceability check.

### Routing on Keel

Path templates, convertors, greedy matching and first-match dispatch are
`Keel.Route` (lean-keel). This repo instantiates them: `BaseRoute.matches`
is a `Keel.Match`, `Router.resolve` is `Keel.dispatch` plus Starlette's 405
and `redirect_slashes` decisions, and the headline theorems are proved from
`dispatch_found_iff`, `dispatch_partial_iff`, `dispatch_none_iff`,
`match_urlFor` and `urlFor_match`. `Allow` is computed here as the union of
all partial matches (`allowOf`), not Keel's first-partial policy, because
of UP-027.

### Tested, not proved

Listed here with the reason, and in `docs/traceability.toml` with
`status = "tested"`.

* **Percent-encoding and UTF-8** (`unquote`, `quote`, `quote_plus`,
  `decodeUtf8`): round trips are seeded properties and plausible checks.
  Proving them needs a UTF-8 codec theory (lean-keel `Codec` over bytes with
  `String.toUTF8`), which is not yet there; the functions are compared with
  Python's `urllib.parse` in the conformance suite.
* **`QueryParams`** parse/print round trip: depends on the above.
* **`URL`** split and rebuild, and the `Host` header parser: string
  plumbing compared against upstream cases. IP literals in `Host` are checked
  for their character set, not as IPv6 addresses.
* **The transport** (`Transport.lean`): `Std.Http` is trusted, not
  re-verified (stack plan). Tested through `Std.Http`'s in-memory
  connection (`[std.http]` conformance cases) and over TCP (`[socket]`
  cases, each compared with uvicorn + Starlette 1.8.0). Its one `partial`
  is the accept loop, justified in `scripts/gate-allow.txt`.
* **Files** (`RepoImpl/FileIO.lean`) is the second effectful module: file
  reads and `stat` for `FileResponse` and `StaticFiles`. The decisions it
  acts on (ranges, ETags, 304, the path under the static root) are pure, in
  `Range.lean`, `Files.lean` and `HttpDate.lean`.

### Deviations from upstream

Each has a `status = "deviation"` row in `docs/traceability.toml`.

* **`Allow` on 405** is the union of every partially matching route's
  methods, deduplicated in route order. Upstream uses the first partial
  route's method set, in hash-seed order (UP-027).
* **No body for 1xx, 204, 304**: the body is dropped and `Response.h_body`
  records it. Upstream sends the body (UP-028).
* **Routes match the whole path**: `/about%0A` is not `/about`. Upstream's
  `$` matches before a final newline (UP-030).
* **`float` path parameters are exact decimals** (Keel `Fixed`), and render
  without rounding. Upstream's `to_string` rounds to 20 places (UP-029).
* **`request.json()` on a body that is not JSON**, or nests deeper than
  lean-json's limit, raises `HTTPException(400)`. Upstream lets
  `json.loads` raise, which is a 500 (or a `RecursionError`).
* **`JSONResponse` of NaN or an infinity** is the 500 that upstream's
  `ValueError` becomes; a pure constructor cannot raise.
* **Status codes** are `100..599` by type (`StatusCode.Valid`, discharged
  `by decide` for literals). Upstream accepts any integer.
* **Route names** default to `""`: a Lean function has no runtime
  `__name__`. Pass `name := "..."` for `url_path_for`.
* **`ServerErrorMiddleware`** returns its 500 response instead of
  re-raising, and its debug page shows the exception and message (Lean has
  no traceback). An `IO` error is reported as `RuntimeError`.
* **Methods** keep their given order with `HEAD` appended after `GET`;
  upstream stores a set.
* **Transport limits.** `Application.run` and `Application.exchange`
  default to uvicorn's effective limits (measured against uvicorn 0.54 with
  Starlette 1.8.0 on the same raw requests): any number of query parameters,
  invalid percent escapes passed through to `QueryParams` (decoded as
  Starlette does), any number of headers, targets up to 65535 bytes. Std.Http
  hard-codes stricter URI limits (100 query parameters, strict `%XX`), so the
  transport moves the request target into a private header
  (`x-lean-starlette-target`, never shown to the app) before Std.Http parses
  the head. What remains, each answered with a status and a body (row
  `transport.limits`):
  * a target over 65535 bytes is `414 URI Too Long` (uvicorn: `400`);
  * a head over 1 MiB is `431`, exactly (uvicorn with httptools, its default
    when installed, as in `uvicorn[standard]`, has no limit; uvicorn with
    h11 0.16 answers `431` over 16 KiB, `h11._connection.DEFAULT_MAX_INCOMPLETE_EVENT_SIZE`;
    neither limits the header count);
  * a body over `config.maxBodySize` (64 MiB by default) or the app's
    `max_body_size` is `413` (uvicorn has no limit);
  * a request without `Host` is `400`, as RFC 9112 3.2 requires (uvicorn: `200`);
  * one request per connection: keep-alive is off, because only the first
    request line is rewritten;
  * a head not complete within `config.headerTimeout` is `408`.
  Pass a `Std.Http.Config` to tighten the rest.
* **Numbers from request input** follow CPython's `int()` digit limit
  (`sys.int_max_str_digits`, 4300; leading zeros count): a longer `Range`
  bound is upstream's `ValueError` (the part is ignored), a longer date field
  makes `parsedate` return `None`. The limit is checked in linear time before
  conversion, and conversion goes 18 digits per big-number step
  (`boundedDigits?`, `digitsValueChunked_eq`). The `Host` port is at most five
  significant digits. JSON numbers are bounded by lean-json.

### Open: cost of matching paths (lean-keel)

Path matching runs on Keel.Route. Measured at Keel 6f70d3f, compiled
(`lake build bench`): a path that does not match a template with a capture
before a literal costs O(n²) in its length (`/s/{a}/x` against `/s/` + 65000
characters: 75 s), and `int`/`float` captures render with a quadratic
`Codec.decimal` (65536 digits: 11 s). Both are requested from lean-keel (card
notes on xpnwkxj1gfz9); this repository takes the fix with `lake update Keel`.

### Large JSON bodies

`lake build bench && /usr/bin/time -v .lake/build/bin/bench array 20`: one
`POST` of a 20 MB JSON array (2.6 million integers) through
`Application.exchange` and `request.json()` peaks at 237 MB resident, 0.7 s
(lean-json 5c4d6ad; it was 650 MB before lean-json's compact representation).
A wide object is quadratic in its key count in lean-json 5c4d6ad (1 MB, 68k
keys: 6 s), reported to lean-json with the cause.

## Tests

* `tests/Props.lean`: seeded property tests, no dependencies, under a second.
* `tests/Conformance.lean`: cases re-expressed from the upstream suite; each
  names the upstream test (`tests/test_x.py::test_y`). It also replays
  `tests/golden/starlette-1.8.0.jsonl`: status, headers and body recorded
  from Starlette 1.8.0's TestClient by `tests/golden/record.py` (run with
  the upstream-spec venv; never needed to build), checked against the same
  app written in Lean. Recorded deviations are listed in `goldenDeviations`.
* `tests/pbt/`: a separate Lake package, the one place an external dependency
  (`plausible`) is taken.

## Traceability

`docs/traceability.toml` links upstream behaviour to the Lean symbol, theorem
and test that realise it. Add a row when behaviour is newly implemented,
tested-only, excluded, or deviates. CI fails if a registered symbol does not
resolve.

## Conventions

* Lean 4 `leanprover/lean4:v4.35.0`; no Mathlib; the core library depends only on Lean
  core and the sibling `lean-*` repos listed in `lakefile.toml`, pinned by
  commit in `lake-manifest.json`.
* Choose the definition that suits the automation over a prettier one with a
  harder proof.
* No upstream code is copied; the upstream test suite and docs are the spec.
