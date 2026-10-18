import Std.Http
import LeanStarlette.APIs
import LeanStarlette.RepoImpl.Head
import LeanStarlette.RepoImpl.Chunked

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
header is removed). With `preread`, the body was read by the transport and
the head's framing headers carry their private names (`hideFraming`). -/
def requestOfHead (head : Std.Http.Request.Head) (body : ByteArray)
    (client : Option (String × Nat) := none) (server : Option (String × Nat) := none)
    (preread : Bool := false) : Request :=
  let fields := head.headers.toList.map fun (n, v) => (lowerAscii (toString n), toString v)
  -- a body the transport read: its framing headers come back under their names
  let fields := if preread then fields.map fun (n, v) =>
      ((framingHeaders.find? (·.2 == n)).map (·.1) |>.getD n, v) else fields
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

/-- Read a request body into one buffer of `cap` bytes' capacity (the
transport always knows the length: it hands `Std.Http` a `Content-Length`).
`Body.Stream.readAll` grows its buffer from empty, holding up to twice the
body while it copies. At most `limit` bytes, as `readAll`'s `maximumSize`;
`fuel` bounds the number of chunks. -/
def readBodyInto {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m] [Body.Stream.NextChunk m]
    (stream : Body.Stream) (cap : Nat) (limit : Option UInt64) (fuel : Nat) : m ByteArray := do
  let mut out := ByteArray.emptyWithCapacity cap
  for _ in [0:fuel] do
    match ← Body.Stream.NextChunk.nextChunk stream with
    | none => return out
    | some chunk =>
      out := out ++ chunk.data
      if let some max := limit then
        if out.size.toUInt64 > max then
          throw (IO.userError s!"body exceeded maximum size of {max} bytes")
  return out

/-- The `Content-Length` of a head, if it has a plain one. -/
def headContentLength (head : Std.Http.Request.Head) : Option Nat :=
  (head.headers.toList.find? fun (n, _) => lowerAscii (toString n) == "content-length").bind
    fun (_, v) => (toString v).trimAscii.toString.toNat?

/-- The `Std.Http` handler for an application: read the body (up to the
application's `max_body_size`, when it has one), call the app, send the
response. `handled` records that the application ran, so the transport can
tell its own error responses from the application's. -/
def Application.toHandler (a : Application) (handled : IO.Ref Bool)
    (client : Option (String × Nat) := none) (preread : Option (IO.Ref (Option ByteArray)) := none) :
    Std.Http.Server.StatelessHandler :=
  Std.Http.Server.Handler.ofFn fun req => do
    handled.set true
    let limit := a.max_body_size.map fun n => (n + 1).toUInt64
    let taken ← match preread with
      | some r => r.swap none
      | none => pure none
    let (body, pre) ← match taken with
      | some b => pure (b, true)
      | none =>
        let cap := min ((headContentLength req.line).getD 0) (a.max_body_size.getD (64 * 1024 * 1024) + 1)
        pure (← readBodyInto req.body cap limit (cap + 1024 * 1024 * 1024), false)
    let response ← a.call (requestOfHead req.line body client (preread := pre))
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
    -- a read's buffer has the capacity asked for; keep only its bytes
    readBody c timeout (acc.push (chunk.extract 0 chunk.size)) (got + chunk.size) need
termination_by need - got

/-- Join chunks into one buffer of the right capacity, copying each once. -/
def joinChunks (first : ByteArray) (chunks : Array ByteArray) : ByteArray :=
  chunks.foldl (· ++ ·) (ByteArray.emptyWithCapacity (first.size + chunks.foldl (· + ·.size) 0) ++ first)

/-- How reading a chunked body ended. -/
inductive ChunkedRead where
  /-- The raw pieces received (the last cut where the body ends) and the
  decoded size. -/
  | complete (pieces : Array ByteArray) (size : Nat)
  | timeout
  | eof
  | bad (message : String)
  | tooLarge

/-- Read a chunked body piece by piece, `ChunkScan.feed` deciding where it
ends; each read within `timeout`. The pieces are kept apart, as in
`readBody`. `raw` bytes have been read of at most `cap`, which bounds the
framing a sender can add (and the recursion); each step reads at least one
byte. -/
def readChunked [Transport t] (c : t) (timeout : Std.Time.Millisecond.Offset) (st : ChunkScan)
    (acc : Array ByteArray) (got limit raw cap : Nat) : Async ChunkedRead := do
  if hn : cap ≤ raw then return .tooLarge else
  let deadline ← Std.Async.Selector.sleep timeout
  let r ← Selectable.one #[
    .case (Transport.recvSelector c 65536) (fun x => pure (some x)),
    .case deadline (fun _ => pure none)]
  match r with
  | none => return .timeout
  | some none => return .eof
  | some (some piece) =>
    if hc : piece.size = 0 then return .eof else
    match st.feed piece got limit with
    | (.done used, got') => return .complete (acc.push (piece.extract 0 used)) got'
    | (.bad m, _) => return .bad m
    | (.tooLarge, _) => return .tooLarge
    | (st', got') =>
      have : cap - (raw + piece.size) < cap - raw := by omega
      readChunked c timeout st' (acc.push (piece.extract 0 piece.size)) got' limit (raw + piece.size) cap
termination_by cap - raw

/-- What the transport does with a request: hand `Std.Http` these bytes
(with the body it read itself, if any, for the application), or answer with
a status. -/
inductive ChunkedOutcome where
  | forward (bytes : ByteArray) (body : Option ByteArray := none)
  | reject (status : Nat) (reason body : String)
  /-- Close without a response (uvicorn, when a chunked body ends early). -/
  | drop

/-- The body after the head of a pre-read request: the bytes received after
`e`, then the pieces, at most `len` of them. -/
def prereadBody (bytes : ByteArray) (e : Nat) (pieces : Array ByteArray) (len : Nat) : ByteArray :=
  let b := joinChunks (bytes.extract e bytes.size) pieces
  if b.size ≤ len then b else b.extract 0 len

/-- Decode the received bytes (`bytes` up to the body's start `e`, then the
pieces) with the verified decoder into a buffer of `size`, the scanner's
decoded size; the two must agree, or the request is refused. `Std.Http` gets
the head alone. -/
def chunkedRequest (bytes : ByteArray) (e : Nat) (pieces : Array ByteArray) (size : Nat) : ChunkedOutcome :=
  match decodeChunkedBody (joinChunks bytes pieces) e (ByteArray.emptyWithCapacity size) with
  | some (out, _) =>
    if out.size == size then .forward (hideFraming bytes e) (some out)
    else .reject 400 "Bad Request" "Invalid HTTP request received."
  | none => .reject 400 "Bad Request" "Invalid HTTP request received."

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
      -- A body framed by a plain Content-Length is read here, whole: Std.Http's
      -- reader copies its unconsumed input on every receive, which is quadratic
      -- in a body that arrives in many reads (20 MB: 5.5 s; here: linear). A
      -- chunked body is read the same way and its framing decoded once by the
      -- verified decoder (`decodeChunkedBody_encode`). Std.Http then gets the
      -- head alone, its framing headers renamed (`hideFraming`), and the
      -- application the body, so Std.Http never copies it.
      let limit := config.maxBodySize
      let outcome ← match plainBodyLength bytes with
        | some (e, len) =>
          if len ≤ limit then
            match ← readBody conn config.lingeringTimeout #[] bytes.size (e + len) with
            | .complete cs => pure (ChunkedOutcome.forward (hideFraming bytes e) (some (prereadBody bytes e cs len)))
            | .eof cs => pure (.forward (hideFraming bytes e) (some (prereadBody bytes e cs len)))
            | .timeout => pure (.reject 408 "Request Timeout" "Request Timeout")
          else pure (.forward bytes)
        | none =>
          match chunkedBodyStart bytes with
          | none => pure (.forward bytes)
          | some e =>
            let early := bytes.extract e bytes.size
            match ChunkScan.feed (.sizeLine .empty) early 0 limit with
            | (.done _, got) => pure (chunkedRequest bytes e #[] got)
            | (.bad _, _) => pure (.reject 400 "Bad Request" "Invalid HTTP request received.")
            | (.tooLarge, _) => pure (.reject 413 "Content Too Large" "Content Too Large")
            | (st, got) =>
              match ← readChunked conn config.lingeringTimeout st #[] got limit early.size (2 * limit + 1024 * 1024) with
              | .complete pieces size => pure (chunkedRequest bytes e pieces size)
              | .timeout => pure (.reject 408 "Request Timeout" "Request Timeout")
              | .eof => pure .drop
              | .bad _ => pure (.reject 400 "Bad Request" "Invalid HTTP request received.")
              | .tooLarge => pure (.reject 413 "Content Too Large" "Content Too Large")
      match outcome with
      | .drop => Transport.close conn; shutdown
      | .reject code reason body =>
        Transport.sendAll conn #[rawResponse code reason body]
        Transport.close conn; shutdown
      | .forward bytes body =>
        let handled ← IO.mkRef false
        let preread ← IO.mkRef body
        let replay : Replay t := ⟨conn, ← IO.mkRef (some bytes), ← IO.mkRef false, handled⟩
        Std.Http.Server.serveConnection replay (a.toHandler handled client (some preread)) (transportConfig config) extensions |>.run
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
