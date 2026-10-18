import Std.Http
import LeanStarlette.APIs

/-!
# Transport: serving an application with `Std.Http`

The one effectful module. It converts between Lean core's `Std.Http`
messages and this library's pure `Request` and `Response`, and serves an
`Application` with `Std.Http.Server.serve`, whose accept loop lives in core.
Nothing here loops: no `partial`, no `scripts/gate-allow.txt` entry.

`Std.Http` parses HTTP/1.1, enforces its header, URI and body limits
(`Std.Http.Config`, 64 MiB of body by default) and frames the response; it
is trusted, not re-verified, and tested through its mock transport
(`tests/Conformance.lean`).
-/

namespace LeanStarlette

open Std.Http Std.Async

/-- The request target as Starlette's scope sees it: the percent-decoded
path and the raw query string. -/
def splitTarget (target : String) : String × String :=
  match splitFirst '?' target.toList with
  | (p, some q) => (unquote (String.ofList p), String.ofList q)
  | (p, none) => (unquote (String.ofList p), "")

/-- The pure request for a `Std.Http` request head and its whole body. -/
def requestOfHead (head : Std.Http.Request.Head) (body : ByteArray)
    (client : Option (String × Nat) := none) (server : Option (String × Nat) := none) : Request :=
  let (path, query_string) := splitTarget (toString head.uri)
  { method := toString head.method
    path, query_string, client, server
    headers := Headers.ofList (head.headers.toList.map fun (n, v) => (toString n, toString v))
    bodyBytes := body }

/-- The `Std.Http` status for a code. -/
def statusOf (code : Nat) : Status :=
  match Status.ofCode none code.toUInt16 with
  | some s => s
  | none =>
    match CustomStatus.ofCodeAndPhrase? code.toUInt16 "Unknown" with
    | some c => .other c
    | none => .internalServerError

/-- The `Std.Http` response for a pure one. Header fields that are not valid
HTTP (a name that is not a token, a value with a control character) are
dropped rather than sent. -/
def toHttpResponse (r : Response) : Async (Std.Http.Response Body.Full) := do
  let headers := r.headers.raw.foldl (init := Std.Http.Headers.empty) fun acc (n, v) =>
    match Header.Name.ofString? n, Header.Value.ofString? v with
    | some n, some v => acc.insert n v
    | _, _ => acc
  (Std.Http.Response.withStatus (statusOf r.status_code)).headers headers |>.fromBytes r.body

/-- The `Std.Http` handler for an application: read the body (up to the
application's `max_body_size`, when it has one), call the app, send the
response. -/
def Application.toHandler (a : Application) : Std.Http.Server.StatelessHandler :=
  Std.Http.Server.Handler.ofFn fun req => do
    let limit := a.max_body_size.map fun n => (n + 1).toUInt64
    let body : ByteArray ← req.body.readAll (maximumSize := limit)
    let client := (req.extensions.get Std.Http.Server.RemoteAddr).map fun ra =>
      (toString ra.addr.ipAddr, ra.addr.port.toNat)
    let response ← a.call (requestOfHead req.line body client)
    let r ← toHttpResponse response
    return (r : Std.Http.Response Body.Any)

/-- `uvicorn.run(app, host=..., port=...)`: serve until the process is
stopped. -/
def Application.run (a : Application) (host : String := "127.0.0.1") (port : Nat := 8000)
    (config : Std.Http.Config := {}) : IO Unit := do
  let some ip := Std.Net.IPv4Addr.ofString host
    | throw (IO.userError s!"not an IPv4 address: {host}")
  let addr : Std.Net.SocketAddress := .v4 ⟨ip, port.toUInt16⟩
  Async.block do
    let server ← Std.Http.Server.serve addr a.toHandler config
    IO.println s!"Serving on http://{host}:{port} (Press CTRL+C to quit)"
    server.waitShutdown

/-- Serve one raw HTTP/1.1 exchange over `Std.Http`'s in-memory transport:
the bytes of the request in, the bytes of the response out. The test
client for raw-byte cases. -/
def Application.exchange (a : Application) (raw : ByteArray)
    (config : Std.Http.Config := { generateDate := false, lingeringTimeout := 1000 }) : IO ByteArray := do
  let (client, server) ← Std.Http.Internal.Mock.new
  Async.block do
    client.send raw
    client.getSendChan.close
    Std.Http.Server.serveConnection server a.toHandler config |>.run
    let res ← client.recv?
    pure (res.getD .empty)

end LeanStarlette
