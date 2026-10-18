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
| `TestClient.lean` | `TestClient app`: lean-httpx's `Client` over an in-process transport | the transport's scope and response are (`RepoImpl/TestClient.lean`); the rest tested |

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

* **`TestClient`** (`TestClient.lean`) is lean-httpx's `Client` over
  `testClientTransport`, as Starlette's is an `httpx.Client`; the conformance
  suite's `TestClient.request` goes through it. Proved: what the transport
  computes (`scope_headers_complete`, `scope_has_host`, `scope_passthrough`,
  `test_response_body`). Tested, not proved: the effectful transport
  (re-raising a server error after the 500, background tasks) and the client
  (lean-httpx's), by golden replay from Starlette 1.8.0's `TestClient`
  (`tests/golden/testclient-starlette-1.8.0.jsonl`, 47 calls over
  `tests/test_testclient.py`'s cases and the scope field by field) and a
  property (query parameters lean-httpx encodes reach `query_params`). The
  path is `unquote(url.path)` as upstream, which decodes twice (UP-058,
  already reported upstream as Kludex/starlette#2587); matching it keeps the
  golden tests honest. Raw ASGI apps, response trailers and debug extensions
  are out of scope (applications here are Lean `App`s); the WebSocket test
  session and lifespan context come with the m7 card.

* **Forms.** The parse is proved (`Proofs/Forms.lean`): `request.form()`
  decodes the raw form lean-multipart's Starlette parser returns, refined by
  its `UrlencodedWithinLimits` / `MultipartWithinLimits`; the decoded items
  meet `max_files` and `max_fields`; a rejection is `HTTPException(400)`.
  Tested, not proved: the decoding itself (charsets, `unquote_plus`) and
  `FormData` / `UploadFile` (`RepoImpl/Upload.lean`, effectful: an upload's
  position and closed flag are an `IO.Ref`), by golden replay from Starlette
  1.8.0 (`tests/golden/forms-starlette-1.8.0.jsonl`, 53 requests, hostile ones
  included), the upstream datastructure tests (`formDataCases`) and
  properties (`FormData` get/getlist/keys, urlencoded round trip, the field
  limit).

* **File I/O** (`RepoImpl/FileIO.lean`): reading in 64 KiB chunks, ranges
  and multipart bodies, `stat`, and the symbolic-link check (`realPath` of
  the file under the directory's, unless `follow_symlink`) are tested, not
  proved: golden replay from Starlette 1.8.0
  (`tests/golden/files-starlette-1.8.0.jsonl`, 32 requests) and constant
  memory measured with `bench file` (20 MB and 400 MB files both peak near
  86 MB resident).

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
* **`StaticFiles(check_dir=True)`** checks the directory on every request
  (upstream at construction): a missing directory is a 500 either way.
* **Background tasks** are `IO` actions (`BackgroundTask(func, *args)` is the
  closure); their order is proved for `run` in `IO` (`background_run_order_io`,
  with the `LawfulMonad IO` instance proved in `Proofs/Background.lean`) and for
  `runAll` in every lawful monad.
* **An `int` path segment of more than 4300 digits** does not match (404),
  as Keel's `int` convertor caps its digits before converting. Upstream's
  regex matches and then `int()` raises, a 500 (UP-052).
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
* **`TestClient` sends `accept-encoding: gzip, deflate`** (lean-httpx's
  decoders); upstream's `test_request_headers` expects `zstd` too, which
  httpx sends only with a zstd decoder installed.
* **Uploads stay in memory**: lean-multipart parses a part into a
  `ByteArray`, so an `UploadFile` never spools to disk (upstream's
  `SpooledTemporaryFile` rolls over at 1 MiB). The body is bounded by
  `max_body_size` (64 MiB by default).
* **Form charsets**: UTF-8 (any spelling Python accepts) and latin-1/ASCII
  are decoded; any other charset Python knows is decoded as latin-1, as an
  unknown one is upstream (row `forms.charset`).
* **A stalled request body** (no byte for `config.lingeringTimeout`, 10 s by
  default) is `408`; uvicorn waits.
* **Numbers from request input** follow CPython's `int()` digit limit
  (`sys.int_max_str_digits`, 4300; leading zeros count): a longer `Range`
  bound is upstream's `ValueError` (the part is ignored), a longer date field
  makes `parsedate` return `None`. The limit is checked in linear time before
  conversion, and conversion goes 18 digits per big-number step
  (`boundedDigits?`, `digitsValueChunked_eq`). The `Host` port is at most five
  significant digits. JSON numbers are bounded by lean-json.

### Cost of matching paths

Path matching runs on Keel.Route, linear in the path since Keel d7ff26d:
65000-character paths that do not match take 5 to 13 ms (conformance
`benchCases`, bound 50 ms; upstream 20 ms). Before, a capture followed by a
literal cost O(n²) (75 s at 65000 characters).

### Large uploads

`Std.Http`'s reader copies the unconsumed input on every receive, so a body
it reads itself costs O(n²) (20 MB 5.5 s, 40 MB 18 s). The transport reads
the body itself and hands it to the application directly; `Std.Http` gets
the head alone, with `Content-Length` and `Transfer-Encoding` renamed to
private names (`hideFraming`), which `requestOfHead` names back in place, so
the application sees the headers the client sent.

* A `Content-Length` body: `readBody`, reads of up to 64 KiB, each compacted
  to its size (a read's buffer has the capacity asked for) and joined once.
* A chunked body: `readChunked` keeps the pieces apart while
  `ChunkScan.feed` finds the end (h11's limits: at most 20 hex digits; a
  size line or trailer block still incomplete past 16 KiB after a receive is
  a 400; `max_body_size` on the decoded size is a 413). The bytes are then
  decoded once by `decodeChunkedBody` (lean-httpx's `chunkSizeLine` and
  `lastChunk` with slices for the data, into one buffer of the decoded
  size); `decodeChunkedBody_encode` proves it returns exactly the chunks of
  any chunk-encoded body, and a property test compares it with lean-httpx's
  codec on bodies with extensions and trailers.

`scripts/bench.sh` (CI) bounds each hostile upload in time and peak memory
(the bench process at rest is about 70 MB): the chunked cases at three times
uvicorn 0.54 + Starlette 1.8.0 on the same request (20 MB: 0.17-0.2 s and
150-180 MB against 0.09 s and 76 MB; a 50 MB multipart file: 0.45-0.5 s and
355 MB against 0.26-0.31 s and 127 MB); a 50 MB Content-Length upload
0.4-0.5 s; 200k urlencoded fields rejected in 26 ms; 50k multipart fields in
47 ms; a 20 MiB value over `max_part_size` in 0.2 s.

### Large JSON bodies

`lake build bench && /usr/bin/time -v .lake/build/bin/bench array 20`: one
`POST` of a 20 MB JSON array (2.6 million integers) through
`Application.exchange` and `request.json()` peaks at 237 MB resident, 0.7 s
(lean-json 5c4d6ad; it was 650 MB before lean-json's compact representation). A 100k-key, 1.4 MB object through `request.json()` takes 67 ms at lean-json bca7cc0 (conformance `benchCases`, bound 250 ms; upstream 0.11 s).
(A wide object was quadratic in its key count in lean-json 5c4d6ad, 1 MB with
68k keys taking 6 s; fixed in lean-json bca7cc0.)

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
