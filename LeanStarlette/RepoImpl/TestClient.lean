import LeanStarlette.RepoImpl.Applications
import LeanHttpx.RepoImpl.Transports

/-!
# RepoImpl: the `TestClient` transport, the pure part

Starlette's `TestClient` is an `httpx.Client` whose transport
(`_TestClientTransport`) calls the application in process. This module is
what that transport computes from an httpx request: the request the
application sees (Starlette's ASGI `scope`), and the httpx response built
from what the application sent. `LeanStarlette/TestClient.lean` runs it.

* `server` is the URL's host and port, the scheme's default port when the
  URL has none (80 for `http`/`ws`, 443 for `https`/`wss`).
* `headers`: a `host` header (the URL's netloc) when the request has none,
  then every request header in order, its name lower-cased.
* `path` is the request target's path decoded once, as a server gives it
  (`/x%2541` reaches the app as `/x%41`). Upstream applies `unquote` to
  httpx's already-decoded `url.path`, decoding twice (`/xA`): UP-058,
  Kludex/starlette#2587, a documented deviation.
* A `HEAD` response has no body.
-/

namespace LeanStarlette

/-- The port a scheme defaults to in the test transport's `server`. -/
def schemeDefaultPort (scheme : String) : Nat :=
  if scheme == "https" || scheme == "wss" then 443 else 80

/-- The scope's headers: `host` (the URL's netloc) when the request has none,
then the request's headers, names lower-cased. -/
def scopeHeaders (r : LeanHttpx.Request) : List (String × String) :=
  (if r.headers.raw.any (fun p => lowerAscii p.1 == "host") then [] else [("host", r.url.netloc)]) ++
    r.headers.raw.map fun p => (lowerAscii p.1, p.2)

/-- The encoded path of a URL, without its query (`raw_path` in the scope). -/
def rawPathOf (u : LeanHttpx.URL) : String := (u.rawPath.splitOn "?").headD "/"

/-- The request the application sees for an httpx request (the `scope`
`_TestClientTransport.handle_request` builds), with the whole body. -/
def scopeRequest (rootPath : String) (client : String × Nat) (r : LeanHttpx.Request) : Request where
  method := r.method
  scheme := r.url.scheme
  server := some (r.url.host, r.url.port.getD (schemeDefaultPort r.url.scheme))
  client := some client
  path := unquote (rawPathOf r.url)
  root_path := rootPath
  query_string := r.url.query
  headers := Headers.ofList (scopeHeaders r)
  bodyBytes := r.content

/-- The httpx response for what the application sent: its status, headers
and body (none for `HEAD`), the body raw for the client to decode. -/
def testResponse (method : String) (status : Nat) (headers : Headers) (body : ByteArray) : LeanHttpx.Response where
  statusCode := status
  headers := ⟨headers.raw⟩
  stream := some (if method == "HEAD" then .empty else body)

end LeanStarlette
