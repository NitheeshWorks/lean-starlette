# lean-starlette

[![Lean 4](https://img.shields.io/badge/built%20with-Lean%204-blue.svg)](https://lean-lang.org)
[![Proofs](https://img.shields.io/badge/proofs-machine%20checked-brightgreen.svg)](CONTRIBUTING.md#verification)

A clean-room port of [Starlette](https://github.com/Kludex/starlette) to Lean 4: routing, requests, responses and middleware as pure functions with proved matching, header and body invariants; one transport module over Lean core's Std.Http.

Part of the verified FastAPI stack: [lean-fastapi](https://github.com/NitheeshWorks/lean-fastapi)
and its dependencies, each ported as its own repo with its proofs. This one
depends on: [lean-json](https://github.com/NitheeshWorks/lean-json), [lean-multipart](https://github.com/NitheeshWorks/lean-multipart), [lean-itsdangerous](https://github.com/NitheeshWorks/lean-itsdangerous), [lean-httpx](https://github.com/NitheeshWorks/lean-httpx), [lean-jinja2](https://github.com/NitheeshWorks/lean-jinja2).

## Quickstart

Starlette's own README example, in Lean:

```python
from starlette.applications import Starlette
from starlette.responses import JSONResponse
from starlette.routing import Route

async def homepage(request):
    return JSONResponse({'hello': 'world'})

routes = [Route("/", endpoint=homepage)]

app = Starlette(debug=True, routes=routes)
```

```lean
import LeanStarlette
open LeanStarlette

def homepage (request : Request) : IO Response :=
  return JSONResponse (json% {"hello": "world"})

def routes := [Route "/" homepage]

def app := Starlette (debug := true) (routes := routes)

def main : IO Unit := app.run (port := 8000)   -- `uvicorn example:app`
```

Path parameters, query parameters, headers, bodies and exceptions read as
they do in Starlette:

```lean
def user (request : Request) : AppM Response := do
  let username := request.pathParams["username"]!
  let q := request.queryParams["q"]?             -- last value, like the dict
  let agent := request.headers["User-Agent"]?    -- any case
  if toString username == "admin" then throw (HTTPException 404 "Item not found")
  return PlainTextResponse s!"Hello, {username}!"

def create (request : Request) : AppM Response := do
  let data ← request.json                        -- 400 on invalid JSON
  return JSONResponse data (status_code := 201)

def app := Starlette (routes := [
  Route "/users/{username}" user,
  Route "/items" create (methods := ["POST"]),
  Mount "/api" (routes := [Route "/items/{item_id:int}" user (name := "item")]),
  Route "/old" (fun (_ : Request) => RedirectResponse "/new")])
```

Endpoints may be `Request → IO Response`, `Request → AppM Response`
(`AppM` adds `throw (HTTPException ...)`), or a pure `Request → Response`.
Status codes are checked at compile time (`by decide` on the literal).

## What is proved

The routing laws are `Keel.Route`'s general theorems (lean-keel),
instantiated for Starlette's `Route`, `Mount` and `Router`:

| Property | Lean statement |
|---|---|
| The first fully matching route handles the request | `route_first_match : Router.resolve rs b req = .found c ↔ ∃ pre r post, rs = pre ++ r :: post ∧ r.matches req = .full c ∧ ∀ r' ∈ pre, ¬ (r'.matches req).IsFull` |
| 405 exactly when nothing matches fully and something matches the path; `Allow` is the union of those routes' methods | `partial_iff_405 : Router.resolve rs b req .unionOfPartials = .methodNotAllowed allow ↔ (∀ r ∈ rs, ¬ full) ∧ (∃ r ∈ rs, partial) ∧ allow = allowOf rs req`, `mem_allowOf` |
| 404 exactly when nothing matches and `redirect_slashes` does not apply; the redirect is a 307 to the toggled path | `no_match_404`, `redirect_slashes_307`, `redirect_307` |
| A `Route` that allows `GET` treats `HEAD` as `GET` (`RouteExact`, for FastAPI's `APIRoute`, does not add `HEAD`) | `route_head_implies_get : (Route p e ms n).allows "GET" → (Route p e ms n).matches {req with method := "HEAD"} = (Route p e ms n).matches {req with method := "GET"}`, `routeExact_methods` |
| `url_path_for` and routing are inverse | `compile_match_url_path_for` (the URL of valid captures routes back to them), `urlPathFor_match` (a canonical path is the URL of its match) |
| Header lookup is case-insensitive | `headers_get_ci : (Headers.ofList l).get? k = (l.find? (lowerAscii ·.1 == lowerAscii k)).map (·.2)` |
| `content-length` is the size of the body sent | `content_length_eq_body` |
| 1xx, 204 and 304 responses have no body | `no_body_204_304` (and the field `Response.h_body`) |
| `JSONResponse`'s body parses back to the value; NaN is refused | `json_response_body`, `json_response_nonfinite` |
| Background tasks run in the order they were added | `background_run_order : runAll (ts ++ [t]) = (do runAll ts; t)` in every lawful monad, `run_order_trace` |
| A printed `Range` header parses back to its ranges; every parsed range lies inside the file | `range_parse_print`, `range_within` |
| A static file is 304 exactly when `If-None-Match` lists its ETag (or `*`), else when `If-Modified-Since` is no earlier than `Last-Modified` | `etag_304_iff`, `date_304_iff`, `static_304_iff` |
| A served static path is the directory followed by plain entry names (no `..`, `.`, `/`, `\`, NUL) | `served_path_inside` |

Every one has a slot in `LeanStarlette/Proofs/Verified.lean`. What is
tested rather than proved, and every deviation from upstream, is listed in
[CONTRIBUTING.md](CONTRIBUTING.md#verification) and `docs/traceability.toml`.

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

Milestone 1: routing (`Route`, `RouteExact`, `Mount`, `Router`,
convertors), `Request`, `Response` and its four subclasses, `HTTPException`,
the exception and server-error middleware, and the `Std.Http` transport.
Milestone 6: `StreamingResponse`, `BackgroundTasks`, `FileResponse` with
`Range`/`If-Range`/ETag, `StaticFiles` with `html` mode and 304 (files are
sent in 64 KiB chunks: a 400 MB file peaks at 86 MB resident, as a 20 MB one
does). Middleware, cookies, forms, WebSockets, `Host`, lifespan and the
httpx-based `TestClient` follow in later milestones.

## License

MIT, see [LICENSE](LICENSE). Upstream attribution is in [NOTICE](NOTICE).
