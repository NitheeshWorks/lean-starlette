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
  `lake exe axioms LeanStarlette` (`scripts/Axioms.lean`, a byte-for-byte
  copy of `stack-tools/Axioms.lean` pinned by `scripts/Axioms.sha256`, which
  CI checks; changes go to stack-tools first: every theorem under `LeanStarlette` reaches only `propext`,
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

### Middleware (m5)

A middleware is `App → App` (`Middleware`), and the application applies its
list first-outermost (`middlewareStack`, `middleware_stack_order`). Each
upstream middleware is a function with upstream's keyword arguments and
defaults, so `Middleware CORSMiddleware (allow_origins := ["*"])` is
`Middleware(CORSMiddleware, allow_origins=["*"])` (the `Middleware` macro in
`APIs/Middleware.lean` is application). What each decides is a pure
function, and the theorems are about those functions:

* `TrustedHostMiddleware`: `trustedHostDecision` (`trusted_host_reject`,
  `trusted_host_reject_400`); its patterns are checked when the app is
  built (`ValidHostPattern`, by `decide +kernel`).
* `HTTPSRedirectMiddleware`: `httpsRedirectURL` (`https_redirect`).
* `CORSMiddleware`: `CORSConfig.preflight` and `responseHeaders`
  (`cors_preflight`, `cors_allowed_origin`). `allow_origin_regex` is a
  `PyRe.Pattern`: `RepoImpl/PyRe.lean` is only Python's `re` dialect (atoms
  with CPython 3.13's `\d`, `\w`, `\s` tables, and a parser after
  `re._parser`), compiled onto `Keel.Regex` in `Mode.full`, which is
  `re.fullmatch`; matching and its laws are Keel's. `re!"..."` parses a
  literal at elaboration and embeds the result (`ToExpr`), so nothing is
  reduced by the kernel; `PyRe.Pattern.compile` does it at run time.
* Cookies (`RepoImpl/Cookies.lean`): `cookieParser` is `cookie_parser`,
  linear (an array and a hash index), proved equal to the list-`dict`
  specification `cookieParserSpec` (`cookieParser_eq_spec`);
  `cookie_parse_print` (legal distinct names read back from the header a
  browser sends) and `set_cookie_receive` / `delete_cookie_receive` (what a
  browser jar holds after the line) are stated on the specification side.
* `SessionMiddleware` signs with lean-itsdangerous's `TimestampSigner`
  (`session_sign_verify` from `TimestampSigner.unsign_sign` and lean-httpx's
  `decodeList_encodeList`); the cookie is byte-identical to upstream's.
* `GZipMiddleware`: `gzip_minimum_size`; the compressor is
  `RepoImpl/Deflate.lean` (LZ77 with hash chains, zlib's lazy evaluation
  and `TOO_FAR`, per-block choice of dynamic Huffman, fixed or stored,
  slicing-by-8 CRC-32), tested, not proved.
* `AuthenticationMiddleware`, `requires`, `BaseHTTPMiddleware`: tested.

**Elaboration cost.** A plain `by decide` on `PyRe.parse` of a CORS regex
is killed at 4 GB; every compile-time check here is `decide +kernel` or
needs no reduction (`re!`). `tests/MiddlewareUsage.lean` (every middleware,
a realistic regex and a six-host list) elaborates under
`stack-tools/capped` 4G in 2.0 s at 1.74 GB peak, of which the import is
1.70 GB.

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
  plumbing compared against upstream cases. The parser is `_HOST_RE`
  exactly; a bracketed literal is validated as `ipaddress.IPv6Address`
  (`isIPv6Address`, `isIPv4Address` for the embedded form), checked by a
  property and the IPv6 golden scenarios.
* **Middleware** beyond the eight theorems: CORS response headers for
  every option, GZip's pass-through rules, exclusions and streams,
  sessions' cookie flags and `Vary`, authentication and `requires`,
  `BaseHTTPMiddleware`: golden replay of 66 scenarios from
  `tests/middleware/` and `tests/test_authentication.py`
  (`tests/golden/middleware-starlette-1.8.0.jsonl`) and 134 unit goldens
  (`tests/golden/m5-units-starlette-1.8.0.jsonl`: the regex dialect against
  Python's `re.fullmatch`, `cookie_parser`, `_quote`, `set_cookie` lines,
  signed session cookies).
* **The DEFLATE compressor**: properties (lean-httpx's `gunzip` reads back
  `gzip` of any bytes, and sync-flushed pieces concatenate), and
  `bench gziptest`, whose outputs Python's `zlib` decompresses. Its sizes
  against zlib level 9: 10 MB of text 1.02 MB (zlib 0.82 MB), 20 MB of
  zeros 23.6 KB (19.5 KB), random bytes stored.
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
  path is the encoded path decoded once, as a server gives it (a deviation,
  below). Raw ASGI apps, response trailers and debug extensions
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

* **`allow_origin_regex`**: backreferences, lookaround, conditionals,
  atomic groups, possessive quantifiers, inline flags and `\N{...}` are an
  `Unsupported` error at construction; `$` is `\Z` (differs from Python only
  for a pattern that matches past a final newline, `a$\n`); repeat counts
  at most 1000, expanded patterns at most 100 000 nodes.
* **`set_cookie`**: `samesite` is an enumeration; `expires` is a date or
  text (upstream's integer, seconds from now, needs the clock);
  `delete_cookie` expires at the Unix epoch where upstream prints the
  current time; `partitioned` prints `Partitioned` (Python 3.14's output;
  3.13 raises); a value character above U+00FF is sent as is, where upstream
  raises `UnicodeEncodeError`, a 500 (UP-064).
* **Session cookies** are read as Latin-1 bytes where upstream encodes
  UTF-8; a signed value is ASCII, so any other character fails the
  signature either way.
* **GZip**: the compressed bytes are Lean's, not zlib's, and
  `compresslevel` is accepted and unused; a status that forbids content
  (1xx, 204, 304) is passed through, where upstream with `minimum_size=0`
  gzips the empty body and declares `Content-Length: 20` (UP-063).
* **`requires(scopes, endpoint, ...)`** wraps an endpoint function, so there
  is no signature to inspect for `request`; WebSocket endpoints are not in
  this port.
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
  * a first head not complete within `config.headerTimeout` is `408`; a
    kept-alive connection idle for `keepAliveTimeout` (5 s, uvicorn's) is
    closed quietly.
  Pass a `Std.Http.Config` to tighten the rest.
* **On the wire** the bytes are uvicorn 0.54's with h11 0.16 (row
  `transport.wire`; `tests/FramingCases.lean` compares 22 scenarios byte for
  byte), but for the `server` field, `Std.Http`'s `serverName`
  (`LeanHTTP/1.1` by default; set it to `uvicorn` for uvicorn's bytes), and
  `100 Continue` for a chunked body, sent before the body is read rather
  than when the application reads it.
* **`TestClient` decodes the path once**, as a server does: `/x%2541`
  reaches the application as `/x%41`, as over a socket (conformance
  `tcSocketCases`). Starlette's test transport applies `unquote` to httpx's
  already-decoded `url.path`, so its application sees `/xA` (UP-058,
  Kludex/starlette#2587); the golden case `scope: double-encoded path`
  expects the server's value (`tcDeviation`).
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

* A `Content-Length` body is read when the application asks for it
  (`Request.receive?`): the router does when a route matches
  (`Request.loadBody`), so a `404` or `405` leaves it on the connection, and
  the transport reads and drops it after the response to keep the
  connection (unless the client waits for `100 Continue`, which is then
  never sent and the connection closed). The application runs on a thread
  of its own, which blocks on each read (`readBodyIO`, 128 KiB at a time,
  one `Async.block` each) into one buffer of the body's size. The buffer
  belongs to that thread alone: Lean's runtime never updates an object
  shared between threads in place, so a buffer in an `IO.Ref` or carried
  through `Async` continuations was copied on every read (10 MiB: 156 ms
  against 38 ms). One deadline serves many reads; it is renewed when bytes
  came since it was set, so a stalled body is cut off after one to two
  `lingeringTimeout`s (`408`).
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

### Hostile inputs to middleware

`bench m5bench` (in `scripts/bench.sh`) runs each case as the best of 5
after a first run and fails above twice Starlette 1.8.0's warm best of 5 on
the same input (`tests/golden/record_m5_bench.py` →
`tests/golden/m5-bench-starlette-1.8.0.json`). Measured at db28314:

| Case | Lean | Starlette 1.8.0 |
|---|---|---|
| `cookie_parser`, 1 MB, 70 000 names | 58 ms | 41 ms |
| `cookie_parser`, 100 000 repeats of one name | 31 ms | 30 ms |
| `cookie_parser`, 50 000 quoted values with escapes | 63 ms | 77 ms |
| 1000 preflights, origin not among 10 000 | 108 ms | 143 ms |
| 1000 GETs from the last of 10 000 origins | 94 ms | 598 ms |
| GZip over TCP, 10 MB of text | 1.05 s | 1.97 s |
| GZip over TCP, 20 MB of zeros (a 1000:1 body) | 163 ms | 93 ms |
| GZip over TCP, 2 MB of random bytes | 81 ms | 70 ms |

Upstream's GZip is uvicorn 0.54 with h11; a `Cookie` header over 16 KiB is
a `431` there, so the cookie cases are timed at the function. The
compressor searches less often inside long runs of literals (after 256 in a
row, one position in up to eight), so incompressible bodies cost little.

`bench bodybench` (in `scripts/bench.sh`) POSTs 10 and 20 MiB to a server
in a child process, against uvicorn 0.54 + Starlette 1.8.0 on the same
requests (`tests/golden/body-bench-starlette-1.8.0.json`, warm best of 5,
peak resident memory less the memory before, after a warm-up): to a route
that reads the body, 44 / 87 ms and +24 / +50 MB against 52 / 93 ms and
+19 / +39 MB; to a 404, 35 / 62 ms and +16 / +18 MB against 33 / 48 ms and
+0 / +0.5 MB. Unread, uvicorn drops the body as it arrives; here the cost
is fixed per request (the threads' heaps: 6 MB with no body, the same for
1 and 40 MiB), so that row is bounded at twice the body size instead.

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
