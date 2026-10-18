import Keel.Route
import LeanJson
import LeanStarlette.DataTypes.Chars

/-!
# DataTypes: headers, requests, responses, exceptions and routes

The shapes of `starlette.datastructures.Headers`, `QueryParams`,
`starlette.requests.Request`, `starlette.responses.Response`,
`starlette.exceptions.HTTPException` and the routing table. Invariants are
fields:

* `Headers.h_lower`: stored names are lower-case, as Starlette stores raw
  header names, so lookup is case-insensitive by construction.
* `Response.h_status`: the status code is a three-digit HTTP status.
* `Response.h_body`: a response whose status forbids content (1xx, 204, 304)
  has an empty body (RFC 9110 section 6.4.1; upstream does not enforce it,
  UP-028).
* `BaseRoute.route`'s `h_head`: a route that allows `GET` allows `HEAD`.
-/

namespace LeanStarlette

/-! ## Headers -/

/-- An immutable, case-insensitive multidict of header fields, in order.
Names are stored lower-cased (`Headers.raw` upstream is a list of
`(bytes, bytes)` with lower-case names). -/
structure Headers where
  raw : List (String × String)
  h_lower : ∀ p ∈ raw, IsLower p.1

/-- The query string's `key=value` pairs, in order (`QueryParams`). -/
structure QueryParams where
  items : List (String × String)
  deriving Inhabited, BEq, Repr

/-! ## Status codes -/

/-- A three-digit HTTP status code. `by decide` proves it for a literal. -/
abbrev StatusCode.Valid (n : Nat) : Prop := 100 ≤ n ∧ n < 600

/-- Whether a response with this status may carry content: not 1xx, 204 or
304 (upstream's `init_headers` condition for `content-length`). -/
def bodyAllowed (status : Nat) : Bool := !(status < 200 || status == 204 || status == 304)

/-! ## Path parameters -/

/-- One converted path parameter: the convertor that matched it and the
value's canonical text (`int` gives `7` for `007`, `uuid` the lower-case
hyphenated form). The typed value is `PathParam.as?`. -/
structure PathParam where
  convertor : String
  text : String
  deriving Inhabited, BEq, Repr

/-- `request.path_params`: the converted parameters, by name, in template
order (a mount's parameters first). -/
structure PathParams where
  items : List (String × PathParam) := []

/-! ## Requests -/

/-- An HTTP request, as Starlette's `Request` sees its ASGI scope and body.
`path` is percent-decoded, as the ASGI `path` is. -/
structure Request where
  method : String := "GET"
  scheme : String := "http"
  /-- `(host, port)` of the server, when known. -/
  server : Option (String × Nat) := none
  /-- `(host, port)` of the client, when known. -/
  client : Option (String × Nat) := none
  path : String := "/"
  root_path : String := ""
  /-- The raw query string, without the `?`. -/
  query_string : String := ""
  headers : Headers := ⟨[], by simp⟩
  path_params : PathParams := {}
  /-- The whole request body. -/
  bodyBytes : ByteArray := .empty
  /-- The application's `url_path_for`, for `request.url_for`: the path and
  the route's protocol. Filled in by the application. -/
  urlPathFor : String → List (String × String) → Option (String × String) := fun _ _ => none

/-! ## Responses -/

/-- An HTTP response: status, headers in order, and body. -/
structure Response where
  status_code : Nat
  headers : Headers
  body : ByteArray
  h_status : StatusCode.Valid status_code
  h_body : bodyAllowed status_code = true ∨ body.size = 0

/-! ## Exceptions and the handler monad -/

/-- What an endpoint can raise. `http` is `HTTPException`; `custom` carries
any other exception a downstream library defines (lean-fastapi's
`RequestValidationError`), matched by `kind`. Build an `http` one with the
`HTTPException` function. -/
inductive Exception where
  | http (status_code : Nat) (detail : String) (headers : List (String × String))
      (h : StatusCode.Valid status_code)
  | custom (kind : String) (detail : String) (data : LeanJson.Json)

/-- The monad endpoints run in: `IO` with `Exception`s. A plain `IO`
endpoint lifts into it. -/
abbrev AppM := ExceptT Exception IO

/-- An ASGI application, in Lean: a request in, a response out. -/
abbrev App := Request → AppM Response

/-! ## Routes -/

/-- A routing table entry (`BaseRoute`): a `Route` to an endpoint, or a
`Mount` of a sub-application or of nested routes. Build them with the
`Route` and `Mount` functions, which compile the path. -/
inductive BaseRoute where
  /-- `Route(path, endpoint, methods=..., name=...)`. `error` is the
  `compile_path` error, if the path did not compile. -/
  | route (path : String) (r : Keel.Route App) (name : String) (error : Option String)
      (h_head : ∀ ms, r.methods = some ms → "GET" ∈ ms → "HEAD" ∈ ms)
  /-- `Mount(path, routes=... | app=..., name=...)`: `template` is
  `path + "/{path:path}"`; `handler` runs the mounted routes or app. -/
  | mount (path : String) (template : Keel.PathTemplate) (routes : List BaseRoute)
      (handler : App) (name : Option String) (error : Option String)

end LeanStarlette
