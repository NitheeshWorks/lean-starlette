import Std.Http
import LeanStarlette.APIs
import LeanStarlette.RepoImpl.Head

/-!
# Transport: serving an application with `Std.Http`

The effectful module for the network. It converts between Lean core's
`Std.Http` messages and this library's pure `Request` and `Response`, and
serves an `Application`.

Each connection goes through `serveConnection`:

1. Read the request head (up to `maxHeadBytes`, within `headerTimeout`).
2. `rewriteHead` (pure, `RepoImpl/Head.lean`) moves the raw request target
   into `targetHeader`, so that `Std.Http`'s request-target parser, whose
   limits `Std.Http.Config` does not expose, never sees it; or it answers
   414/400 as uvicorn does.
3. `Std.Http.Server.serveConnection` runs one exchange over a transport that
   replays the head (`Replay`). Keep-alive is off, because only the first
   request line of a connection is rewritten (see `CONTRIBUTING.md`).
4. Error responses `Std.Http` writes itself (413, 431, 400) get the body
   uvicorn sends with them.

`acceptLoop` is the one unbounded loop: a server accepts until it is
stopped. It is the single entry of `scripts/gate-allow.txt`; everything it
calls is total.

`Std.Http` is trusted, not re-verified, and tested through its mock
transport and over real sockets (`tests/Conformance.lean`).
-/

namespace LeanStarlette

open Std.Http Std.Async Std.Async.TCP

/-- The request target as Starlette's scope sees it: the percent-decoded
path and the raw query string. An absolute-form target
(`http://host/path`) gives its path, as uvicorn does. -/
def splitTarget (target : String) : String × String :=
  let cs := target.toList
  let cs := match splitFirst ':' cs with
    | (scheme, some ('/' :: '/' :: rest)) =>
      if !scheme.isEmpty && scheme.all Char.isAlpha then
        let p := rest.dropWhile (fun c => c ≠ '/' && c ≠ '?')
        if p.isEmpty then ['/'] else if p.head? == some '?' then '/' :: p else p
      else cs
    | _ => cs
  match splitFirst '?' cs with
  | (p, some q) => (unquote (String.ofList p), String.ofList q)
  | (p, none) => (unquote (String.ofList p), "")

/-- The pure request for a `Std.Http` request head and its whole body. The
target is the one the transport saved in `targetHeader` (every copy of that
header is removed). -/
def requestOfHead (head : Std.Http.Request.Head) (body : ByteArray)
    (client : Option (String × Nat) := none) (server : Option (String × Nat) := none) : Request :=
  let fields := head.headers.toList.map fun (n, v) => (lowerAscii (toString n), toString v)
  let target := ((fields.find? (·.1 == targetHeader)).map (·.2)).getD (toString head.uri)
  let (path, query_string) := splitTarget target
  { method := toString head.method
    path, query_string, client, server
    headers := Headers.ofList (fields.filter (·.1 != targetHeader))
    bodyBytes := body }

/-- The `Std.Http` status for a code. -/
def statusOf (code : Nat) : Status :=
  match Status.ofCode none code.toUInt16 with
  | some s => s
  | none =>
    match CustomStatus.ofCodeAndPhrase? code.toUInt16 "Unknown" with
    | some c => .other c
    | none => .internalServerError

/-- The `Std.Http` header fields of a response. Fields that are not valid
HTTP (a name that is not a token, a value with a control character) are
dropped rather than sent. -/
def httpHeaders (r : Response) : Std.Http.Headers :=
  r.headers.raw.foldl (init := Std.Http.Headers.empty) fun acc (n, v) =>
    match Header.Name.ofString? n, Header.Value.ofString? v with
    | some n, some v => acc.insert n v
    | _, _ => acc

/-- The body of a response as a `Std.Http` stream. The stream is a
rendezvous channel: `send` waits for the connection to take each chunk, so
a streamed body is held one chunk at a time. With a `content-length` the
body is sent with that length, otherwise chunked. Background tasks run
after the last chunk is taken and the stream is closed. -/
def toHttpBody (r : Response) : Async Body.Stream := do
  let s ← Body.mkStream
  let known := (r.headers.get? "content-length").bind String.toNat?
  s.setKnownSize (some (match known with | some n => .fixed n | none => .chunked))
  let gen : ContentStream := r.stream.getD fun send => if r.body.size > 0 then send r.body else pure ()
  background do
    try
      gen fun chunk => if chunk.size > 0 then s.send (Chunk.ofByteArray chunk) else pure ()
      s.close
      r.background.run
    catch err =>
      s.closeWithError err
  return s

/-- The `Std.Http` response for a pure one. -/
def toHttpResponse (r : Response) : Async (Std.Http.Response Body.Any) := do
  let body ← toHttpBody r
  let resp := (Std.Http.Response.withStatus (statusOf r.status_code)).headers (httpHeaders r) |>.body body
  return (resp : Std.Http.Response Body.Any)

/-- The `Std.Http` handler for an application: read the body (up to the
application's `max_body_size`, when it has one), call the app, send the
response. `handled` records that the application ran, so the transport can
tell its own error responses from the application's. -/
def Application.toHandler (a : Application) (handled : IO.Ref Bool)
    (client : Option (String × Nat) := none) : Std.Http.Server.StatelessHandler :=
  Std.Http.Server.Handler.ofFn fun req => do
    handled.set true
    let limit := a.max_body_size.map fun n => (n + 1).toUInt64
    let body : ByteArray ← req.body.readAll (maximumSize := limit)
    let response ← a.call (requestOfHead req.line body client)
    toHttpResponse response

/-! ## One connection -/

/-- A transport that first yields a fixed prefix (the rewritten head), then
the underlying connection's bytes; and that gives `Std.Http`'s own empty
error responses uvicorn's bodies. -/
structure Replay (t : Type) where
  inner : t
  pending : IO.Ref (Option ByteArray)
  innerRegistered : IO.Ref Bool
  handled : IO.Ref Bool

/-- Give an error response `Std.Http` wrote before the application ran the
body uvicorn sends. -/
def decorateError (handled : Bool) (data : Array ByteArray) : Array ByteArray :=
  if handled then data else
  let all := data.foldl (· ++ ·) ByteArray.empty
  match emptyErrorResponse? all with
  | some (code, reason) => #[rawResponse code reason (errorBody code reason)]
  | none => data

instance [Transport t] : Transport (Replay t) where
  recv r n := do
    match ← r.pending.swap none with
    | some b => pure (some b)
    | none => Transport.recv r.inner n
  sendAll r data := do Transport.sendAll r.inner (decorateError (← r.handled.get) data)
  recvSelector r n := {
    tryFn := do
      match ← r.pending.get with
      | some b => r.pending.set none; pure (some (some b))
      | none => (Transport.recvSelector r.inner n).tryFn
    registerFn := fun w => do
      match ← r.pending.get with
      | some b => w.race (pure ()) fun p => do r.pending.set none; p.resolve (.ok (some b))
      | none => r.innerRegistered.set true; (Transport.recvSelector r.inner n).registerFn w
    unregisterFn := do
      if ← r.innerRegistered.swap false then (Transport.recvSelector r.inner n).unregisterFn }
  close r := Transport.close r.inner

/-- How reading a head ended. -/
inductive HeadRead where
  | complete (bytes : ByteArray)
  | eof
  | tooLarge
  | timeout

/-- Read until the head is complete, racing a deadline. A head (request line,
headers and the blank line) longer than `buf.size + budget` bytes is
`tooLarge`, exactly. Each step reads at least one byte, so this is total; only the new
bytes are scanned for the end of the head. -/
def readHead [Transport t] (c : t) (deadline : Std.Async.Selector Unit) (buf : ByteArray) (budget : Nat) :
    Async HeadRead := do
  if hb : budget = 0 then return .tooLarge else
  let r ← Selectable.one #[
    .case (Transport.recvSelector c 65536) (fun x => pure (some x)),
    .case deadline (fun _ => pure none)]
  match r with
  | none => return .timeout
  | some none => return .eof
  | some (some chunk) =>
    if hc : chunk.size = 0 then return .eof else
    have : budget - min budget chunk.size < budget := by omega
    let buf' := buf ++ chunk
    match findHeadEnd buf' (buf.size - min buf.size 3) with
    | some e => return (if e ≤ buf.size + budget then .complete buf' else .tooLarge)
    | none => readHead c deadline buf' (budget - min budget chunk.size)
termination_by budget

/-- How reading a body ended: the chunks read, in order. -/
inductive BodyRead where
  | complete (chunks : Array ByteArray)
  | eof (chunks : Array ByteArray)
  | timeout

/-- Read until `got + (bytes read)` reaches `need`, each read within `timeout`
(as `Std.Http`'s `lingeringTimeout`). Reads ask for at most what is still
missing, so nothing past the body is taken. The chunks are kept apart and
joined once by the caller: appending to one buffer inside `Async` copies it
on every read. Each step reads at least one byte. -/
def readBody [Transport t] (c : t) (timeout : Std.Time.Millisecond.Offset) (acc : Array ByteArray)
    (got need : Nat) : Async BodyRead := do
  if hn : need ≤ got then return .complete acc else
  let deadline ← Std.Async.Selector.sleep timeout
  let r ← Selectable.one #[
    .case (Transport.recvSelector c (min 65536 (need - got)).toUInt64) (fun x => pure (some x)),
    .case deadline (fun _ => pure none)]
  match r with
  | none => return .timeout
  | some none => return .eof acc
  | some (some chunk) =>
    if hc : chunk.size = 0 then return .eof acc else
    have : need - (got + chunk.size) < need - got := by omega
    readBody c timeout (acc.push chunk) (got + chunk.size) need
termination_by need - got

/-- Join chunks into one buffer of the right capacity, copying each once. -/
def joinChunks (first : ByteArray) (chunks : Array ByteArray) : ByteArray :=
  chunks.foldl (· ++ ·) (ByteArray.emptyWithCapacity (first.size + chunks.foldl (· + ·.size) 0) ++ first)

/-- The configuration the transport hands `Std.Http`: uvicorn-like limits
(no header count limit beyond the head size; long header values), and no
keep-alive. -/
def transportConfig (base : Std.Http.Config) : Std.Http.Config :=
  { base with
    enableKeepAlive := false
    maxHeaders := maxHeadBytes
    maxHeaderBytes := maxHeadBytes + 1024
    maxHeaderValueLength := maxHeadBytes
    maxHeaderNameLength := maxHeadBytes
    maxStartLineLength := maxHeadBytes
    maxUriLength := maxHeadBytes }

/-- Serve one connection: read and rewrite the head, then let `Std.Http`
run the exchange. -/
def serveOne [Transport t] (a : Application) (conn : t) (config : Std.Http.Config)
    (client : Option (String × Nat) := none) (extensions : Extensions := .empty)
    (shutdown : Async Unit := pure ()) : Async Unit := do
  let deadline ← Std.Async.Selector.sleep config.headerTimeout
  match ← readHead conn deadline .empty maxHeadBytes with
  | .eof => Transport.close conn; shutdown
  | .timeout =>
    Transport.sendAll conn #[rawResponse 408 "Request Timeout" "Request Timeout"]
    Transport.close conn; shutdown
  | .tooLarge =>
    Transport.sendAll conn #[rawResponse 431 "Request Header Fields Too Large" "Request Header Fields Too Large"]
    Transport.close conn; shutdown
  | .complete head =>
    match rewriteHead head with
    | .reject code reason body =>
      Transport.sendAll conn #[rawResponse code reason body]
      Transport.close conn; shutdown
    | .forward bytes =>
      -- A body framed by a plain Content-Length is read here, whole, and handed
      -- to Std.Http with the head in one piece: Std.Http's reader copies its
      -- unconsumed input on every receive, which is quadratic in a body that
      -- arrives in many reads (20 MB: 5.5 s; in one piece: linear).
      let bytes ← match plainBodyLength bytes with
        | some (e, len) =>
          if len ≤ config.maxBodySize then
            match ← readBody conn config.lingeringTimeout #[] bytes.size (e + len) with
            | .complete cs => pure (some (joinChunks bytes cs))
            | .eof cs => pure (some (joinChunks bytes cs))
            | .timeout => pure none
          else pure (some bytes)
        | none => pure (some bytes)
      match bytes with
      | none =>
        Transport.sendAll conn #[rawResponse 408 "Request Timeout" "Request Timeout"]
        Transport.close conn; shutdown
      | some bytes =>
        let handled ← IO.mkRef false
        let replay : Replay t := ⟨conn, ← IO.mkRef (some bytes), ← IO.mkRef false, handled⟩
        Std.Http.Server.serveConnection replay (a.toHandler handled client) (transportConfig config) extensions |>.run
        shutdown

/-! ## The server -/

/-- Accept connections until the process stops, each served in the
background, at most `config.maxConnections` at once. The one unbounded loop
of the library (`scripts/gate-allow.txt`). -/
partial def acceptLoop (a : Application) (server : Socket.Server) (config : Std.Http.Config)
    (permits : Std.Semaphore) : Async Unit := do
  let client ← server.accept
  await (← permits.acquire)
  let peer ← (EIO.toBaseIO client.getPeerName : BaseIO (Except IO.Error Std.Net.SocketAddress))
  let (clientAddr, ext) := match peer with
    | .ok (addr : Std.Net.SocketAddress) => (some (toString addr.ipAddr, addr.port.toNat), Extensions.empty.insert (Std.Http.Server.RemoteAddr.mk addr))
    | .error _ => (none, Extensions.empty)
  background do
    try serveOne a client config clientAddr ext (try client.shutdown catch _ => pure ())
    finally permits.release
  acceptLoop a server config permits

/-- `uvicorn.run(app, host=..., port=...)`: serve until the process is
stopped. -/
def Application.run (a : Application) (host : String := "127.0.0.1") (port : Nat := 8000)
    (config : Std.Http.Config := {}) : IO Unit := do
  let some ip := Std.Net.IPv4Addr.ofString host
    | throw (IO.userError s!"not an IPv4 address: {host}")
  let addr : Std.Net.SocketAddress := .v4 ⟨ip, port.toUInt16⟩
  Async.block do
    let server ← Socket.Server.mk
    server.bind addr
    server.listen 1024
    server.noDelay
    let permits ← Std.Semaphore.new (max config.maxConnections 1)
    IO.println s!"Serving on http://{host}:{port} (Press CTRL+C to quit)"
    acceptLoop a server config permits

/-- Serve one raw HTTP/1.1 exchange over `Std.Http`'s in-memory transport,
through the same path as a socket connection: the bytes of the request in,
the bytes of the response out. The test client for raw-byte cases. -/
def Application.exchange (a : Application) (raw : ByteArray)
    (config : Std.Http.Config := { generateDate := false, lingeringTimeout := 1000 }) : IO ByteArray := do
  let (client, server) ← Std.Http.Internal.Mock.new
  Async.block do
    client.send raw
    client.getSendChan.close
    serveOne a server config
    let res ← client.recv?
    pure (res.getD .empty)

end LeanStarlette
