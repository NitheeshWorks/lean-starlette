import Std.Http
import LeanStarlette.APIs
import LeanStarlette.RepoImpl.Head
import LeanStarlette.RepoImpl.Chunked
import LeanStarlette.RepoImpl.Wire

/-!
# Transport: serving an application with `Std.Http`

The effectful module for the network. It converts between Lean core's
`Std.Http` messages and this library's pure `Request` and `Response`, and
serves an `Application`.

Each connection goes through `serveRequests`, once per request while the
connection is kept alive (as uvicorn: HTTP/1.1 without `Connection: close`,
no exception in the application, a body of known length or chunked):

1. Read the request head (up to `maxHeadBytes`; the first within
   `headerTimeout`, a later one within `keepAliveTimeout`), starting from
   any bytes of it already received (pipelining).
2. `rewriteHead` (pure, `RepoImpl/Head.lean`) moves the raw request target
   into `targetHeader`, so that `Std.Http`'s request-target parser, whose
   limits `Std.Http.Config` does not expose, never sees it; or it answers
   414/400 as uvicorn does.
3. The transport reads the body itself (`requestOutcome`), after sending
   `100 Continue` to a client that expects it, and keeps what follows the
   body for the next request.
4. `Std.Http.Server.serveConnection` parses and checks the head alone
   (`Replay` gives it nothing more), and calls the application. Error
   responses it writes before the application runs (400, 413) get the body
   uvicorn sends with them. The application's response is written by the
   transport, as uvicorn and h11 write it (`writeResponse`, `wireHead` in
   `RepoImpl/Wire.lean`): reason phrases, header order and spelling,
   framing and `Connection` handling.

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
application's `max_body_size`, when it has one), call the app, and write the
response with `write` (the transport's own writer, as uvicorn frames it).
`Std.Http` gets an empty response, which the transport drops. `handled`
records that the application ran, so the transport can tell its own error
responses from the application's. -/
def Application.toHandler (a : Application) (handled : IO.Ref Bool)
    (client : Option (String × Nat) := none) (preread : Option (IO.Ref (Option ByteArray)) := none)
    (write : Option (Response → Async Unit) := none) (report : Exception → IO Unit := fun _ => pure ())
    (receive? : Option (IO (Except Nat ByteArray)) := none) :
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
    let request := { requestOfHead req.line body client (preread := pre) with receive? }
    -- An application that may read its body from the connection runs on a
    -- thread of its own: reading blocks it (`Async.block`), never a thread
    -- of the task pool.
    let response ← match receive? with
      | none => a.call request report
      | some _ =>
        match ← (await (← IO.asTask (a.call request report) .dedicated) : Async _) with
        | .ok r => pure r
        | .error _ => pure internalServerError
    match write with
    | some w =>
      w response
      toHttpResponse (PlainTextResponse "")
    | none => toHttpResponse response

/-! ## One connection -/

/-- What `Std.Http` sees of a connection: the rewritten head of one request
and then the end of input (the transport reads bodies and later requests
itself). Before the application runs, what `Std.Http` writes (its error
responses) goes through, with uvicorn's bodies; after, nothing does (the
transport writes the response). Closing is the transport's. -/
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
  recv r _ := r.pending.swap none
  sendAll r data := do
    -- once the application ran, the transport has written its response
    unless ← r.handled.get do Transport.sendAll r.inner (decorateError false data)
  recvSelector r _ := {
    tryFn := do
      match ← r.pending.get with
      | some b => r.pending.set none; pure (some (some b))
      | none => pure (some none)
    registerFn := fun w => do
      let b ← r.pending.swap none
      w.race (pure ()) fun p => p.resolve (.ok b)
    unregisterFn := pure () }
  close _ := pure ()

/-- How reading a head ended. -/
inductive HeadRead where
  | complete (bytes : ByteArray)
  | eof
  | tooLarge
  /-- No complete head in time; `got` bytes of one had arrived. -/
  | timeout (got : Nat)

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
  | none => return .timeout buf.size
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

/-- The most a body read asks for at once. -/
def bodyReadSize : Nat := 128 * 1024

/-- Read `remaining` more bytes of a body, appending them to `buf` (with
`keep`; otherwise they are discarded), within `timeout` of inactivity: one
deadline serves many reads, and when it passes it is renewed if bytes came
since it was set (`progressed`), so a body is cut off after between one and two
`timeout`s without a byte. Reads ask for at most what is missing, so nothing
past the body is taken. -/
def readInto [Transport t] (c : t) (timeout : Std.Time.Millisecond.Offset) (buf : IO.Ref ByteArray) (keep : Bool)
    (deadline : Std.Async.Selector Unit) (progressed : Bool) (remaining : Nat) : Async BodyRead := do
  if hr : remaining = 0 then return .complete #[] else
  let r ← Selectable.one #[
    .case (Transport.recvSelector c (min bodyReadSize remaining).toUInt64) (fun x => pure (some x)),
    .case deadline (fun _ => pure none)]
  match r with
  | none =>
    if hs : progressed = false then return .timeout else
    have : 2 * remaining + 0 < 2 * remaining + (if progressed then 1 else 0) := by simp_all
    readInto c timeout buf keep (← Std.Async.Selector.sleep timeout) false remaining
  | some none => return .eof #[]
  | some (some chunk) =>
    if hc : chunk.size = 0 then return .eof #[] else
    let n := min chunk.size remaining
    if keep then buf.modify (· ++ chunk)
    have hn : 0 < n := by omega
    have : 2 * (remaining - n) + 1 < 2 * remaining + (if progressed then 1 else 0) := by split <;> omega
    readInto c timeout buf keep deadline true (remaining - n)
termination_by 2 * remaining + (if progressed then 1 else 0)

/-- `readInto` for the thread that waits for the body (the application's):
each read is one `Async.block`, and the bytes go into `buf`, a value of
this thread alone, so it is extended in place. (An object shared between
threads is never updated in place by Lean's runtime, so a buffer kept in a
reference or carried through `Async` continuations would be copied on every
read.) -/
def readBodyIO [Transport t] (c : t) (timeout : Std.Time.Millisecond.Offset) (buf : ByteArray)
    (deadline : Std.Async.Selector Unit) (progressed : Bool) (remaining : Nat) : IO (ByteArray × BodyRead) := do
  if hr : remaining = 0 then return (buf, .complete #[]) else
  let r ← Async.block (Selectable.one #[
    .case (Transport.recvSelector c (min bodyReadSize remaining).toUInt64) (fun x => pure (some x)),
    .case deadline (fun _ => pure none)])
  match r with
  | none =>
    if hs : progressed = false then return (buf, .timeout) else
    have : 2 * remaining + 0 < 2 * remaining + (if progressed then 1 else 0) := by simp_all
    readBodyIO c timeout buf (← Async.block (Std.Async.Selector.sleep timeout)) false remaining
  | some none => return (buf, .eof #[])
  | some (some chunk) =>
    if hc : chunk.size = 0 then return (buf, .eof #[]) else
    let n := min chunk.size remaining
    have hn : 0 < n := by omega
    have : 2 * (remaining - n) + 1 < 2 * remaining + (if progressed then 1 else 0) := by split <;> omega
    readBodyIO c timeout (buf ++ chunk) deadline true (remaining - n)
termination_by 2 * remaining + (if progressed then 1 else 0)

/-- Join chunks into one buffer of the right capacity, copying each once. -/
def joinChunks (first : ByteArray) (chunks : Array ByteArray) : ByteArray :=
  chunks.foldl (· ++ ·) (ByteArray.emptyWithCapacity (first.size + chunks.foldl (· + ·.size) 0) ++ first)

/-- How reading a chunked body ended. -/
inductive ChunkedRead where
  /-- The raw pieces received (the last cut where the body ends) and the
  decoded size. -/
  | complete (pieces : Array ByteArray) (size : Nat) (rest : ByteArray)
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
    | (.done used, got') => return .complete (acc.push (piece.extract 0 used)) got' (piece.extract used piece.size)
    | (.bad m, _) => return .bad m
    | (.tooLarge, _) => return .tooLarge
    | (st', got') =>
      have : cap - (raw + piece.size) < cap - raw := by omega
      readChunked c timeout st' (acc.push (piece.extract 0 piece.size)) got' limit (raw + piece.size) cap
termination_by cap - raw

/-- What the transport does with a request: hand `Std.Http` these bytes
(with the body it read itself, if any, for the application, and the bytes
received past it, the start of the next request), or answer with a status.
`keep`: the connection may serve another request afterwards (the transport
read the body and knows where the next request starts). -/
inductive ChunkedOutcome where
  | forward (bytes : ByteArray) (body : Option ByteArray := none) (rest : ByteArray := .empty) (keep : Bool := false)
  /-- A `Content-Length` body still on the connection: `initial` bytes of
  its `len` have come with the head; `rest` follows the body. -/
  | lazy (bytes : ByteArray) (initial : ByteArray) (len : Nat) (rest : ByteArray)
  | reject (status : Nat) (reason body : String)
  /-- Close without a response (uvicorn, when a chunked body ends early). -/
  | drop

/-- Decode the received bytes (`bytes` up to the body's start `e`, then the
pieces) with the verified decoder into a buffer of `size`, the scanner's
decoded size; the two must agree, or the request is refused. `Std.Http` gets
the head alone; `rest` follows the body. -/
def chunkedRequest (bytes : ByteArray) (e : Nat) (pieces : Array ByteArray) (size : Nat) (rest : ByteArray) :
    ChunkedOutcome :=
  match decodeChunkedBody (joinChunks bytes pieces) e (ByteArray.emptyWithCapacity size) with
  | some (out, _) =>
    if out.size == size then .forward (hideFraming bytes e) (some out) rest true
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

/-- uvicorn's default fields: `date` (with `generateDate`) and `server`
(`serverName`; uvicorn's is `uvicorn`, `Std.Http`'s default `LeanHTTP/1.1`). -/
def defaultFields (config : Std.Http.Config) : IO (List (String × String)) := do
  let date ← if config.generateDate then
      pure [("date", wireDate (← Std.Time.Timestamp.now).toSecondsSinceUnixEpoch.val)]
    else pure []
  return date ++ (config.serverName.map fun v => ("server", toString v)).toList

/-- Write a response as uvicorn does (`wireHead`), its body in the framing
the head chose, then run its background tasks. Returns whether the
connection can serve another request. -/
def writeResponse [Transport t] (conn : t) (config : Std.Http.Config) (rq : WireRequest) (r : Response) :
    Async Bool := do
  let h := wireHead rq (← defaultFields config) r.status_code r.headers.raw
  let gen : ContentStream := r.stream.getD fun send => if r.body.size > 0 then send r.body else pure ()
  try
    match h.body with
    | .none => Transport.sendAll conn #[h.bytes]
    | .raw | .untilClose =>
      if r.stream.isNone then Transport.sendAll conn #[h.bytes, r.body]
      else
        Transport.sendAll conn #[h.bytes]
        gen fun c => if c.size > 0 then Transport.sendAll conn #[c] else pure ()
    | .chunked =>
      Transport.sendAll conn #[h.bytes]
      gen fun c => if c.size > 0 then Transport.sendAll conn #[chunkFrame c] else pure ()
      Transport.sendAll conn #[lastChunkFrame]
  catch _ => return false
  try r.background.run catch _ => pure ()
  return h.keepAlive && h.body != .untilClose

/-- The outcome for a request the transport has the head of: read its body
(sending `100 Continue` first when the client waits for it and none of the
body has come), or leave it to `Std.Http`. -/
def requestOutcome [Transport t] (conn : t) (config : Std.Http.Config) (bytes : ByteArray) (expect : Bool) :
    Async ChunkedOutcome := do
  let limit := config.maxBodySize
  -- uvicorn sends it when the application first reads the body, whether or
  -- not body bytes have already arrived; here the body is read before the
  -- application runs
  let continue_ : Async Unit := if expect then Transport.sendAll conn #[continueBytes] else pure ()
  match plainBodyLength bytes with
  | some (e, len) =>
    if len ≤ limit then
      let avail := bytes.extract e bytes.size
      pure (.lazy (hideFraming bytes e) (avail.extract 0 len) len (avail.extract len avail.size))
    else pure (.forward bytes)
  | none =>
    match chunkedBodyStart bytes with
    | some e =>
      let early := bytes.extract e bytes.size
      match ChunkScan.feed (.sizeLine .empty) early 0 limit with
      | (.done used, got) =>
        continue_
        pure (chunkedRequest (bytes.extract 0 (e + used)) e #[] got (early.extract used early.size))
      | (.bad _, _) => pure (.reject 400 "Bad Request" "Invalid HTTP request received.")
      | (.tooLarge, _) => pure (.reject 413 "Content Too Large" "Content Too Large")
      | (st, got) =>
        continue_
        match ← readChunked conn config.lingeringTimeout st #[] got limit early.size (2 * limit + 1024 * 1024) with
        | .complete pieces size rest => pure (chunkedRequest bytes e pieces size rest)
        | .timeout => pure (.reject 408 "Request Timeout" "Request Timeout")
        | .eof => pure .drop
        | .bad _ => pure (.reject 400 "Bad Request" "Invalid HTTP request received.")
        | .tooLarge => pure (.reject 413 "Content Too Large" "Content Too Large")
    | none =>
      match findHeadEnd bytes 0 with
      | some e =>
        let hs := (headerLines bytes e).map splitHeaderLine
        let framed := hs.any fun (n, _) => n == "content-length".toUTF8.toList || n == "transfer-encoding".toUTF8.toList
        -- no body: Std.Http gets the head, the rest is the next request
        if framed then pure (.forward bytes)
        else pure (.forward (hideFraming bytes e) (some .empty) (bytes.extract e bytes.size) true)
      | none => pure (.forward bytes)

/-- One exchange: `Std.Http` parses the head (`bytes`) and calls the
application, whose response the transport writes. `some ()` when the
connection can serve another request (the application ran, did not fail,
and the response leaves the connection open). -/
def exchange [Transport t] (a : Application) (conn : t) (config : Std.Http.Config)
    (client : Option (String × Nat)) (extensions : Extensions) (rq : WireRequest) (bytes : ByteArray)
    (body : Option ByteArray) (receive? : Option (IO (Except Nat ByteArray))) : Async (Option Unit) := do
  let handled ← IO.mkRef false
  let preread ← IO.mkRef body
  let kept ← IO.mkRef false
  -- uvicorn closes the connection after an exception in the application
  let failed ← IO.mkRef false
  let write (r : Response) : Async Unit := do kept.set (← writeResponse conn config rq r)
  let replay : Replay t := ⟨conn, ← IO.mkRef (some bytes), ← IO.mkRef false, handled⟩
  Std.Http.Server.serveConnection replay
    (a.toHandler handled client (some preread) (some write) (fun _ => failed.set true) receive?)
    (transportConfig config) extensions |>.run
  return if (← handled.get) && (← kept.get) && !(← failed.get) then some () else none

/-- Serve requests on one connection until it is not kept alive, at most
`fuel` of them (`config.maxRequests`). `pending` are bytes already received
of the next request. The first request's head must arrive within
`headerTimeout` (else `408`); a later one within `keepAliveTimeout`, else the
connection is closed quietly, as uvicorn does. -/
def serveRequests [Transport t] (a : Application) (conn : t) (config : Std.Http.Config)
    (client : Option (String × Nat)) (extensions : Extensions) :
    Nat → ByteArray → Bool → Async Unit
  | 0, _, _ => pure ()
  | fuel + 1, pending, first => do
    let wait := if first then config.headerTimeout else config.keepAliveTimeout.val
    let deadline ← Std.Async.Selector.sleep wait
    let read ← match findHeadEnd pending 0 with
      | some e => pure (if e ≤ maxHeadBytes then HeadRead.complete pending else .tooLarge)
      | none => readHead conn deadline pending (maxHeadBytes - min maxHeadBytes pending.size)
    match read with
    | .eof => pure ()
    | .timeout got =>
      if first || got > 0 then Transport.sendAll conn #[rawResponse 408 "Request Timeout" "Request Timeout"]
    | .tooLarge =>
      Transport.sendAll conn #[rawResponse 431 "Request Header Fields Too Large" "Request Header Fields Too Large"]
    | .complete head =>
      let e0 := (findHeadEnd head 0).getD head.size
      let rq := wireRequestOf head e0
      match rewriteHead head with
      | .reject code reason body => Transport.sendAll conn #[rawResponse code reason body]
      | .forward bytes =>
        -- A body framed by a plain Content-Length is read here, whole: Std.Http's
        -- reader copies its unconsumed input on every receive, which is quadratic
        -- in a body that arrives in many reads (20 MB: 5.5 s; here: linear). A
        -- chunked body is read the same way and its framing decoded once by the
        -- verified decoder (`decodeChunkedBody_encode`). Std.Http then gets the
        -- head alone, its framing headers renamed (`hideFraming`), and the
        -- application the body, so Std.Http never copies it.
        let expect := expectsContinue head e0
        match ← requestOutcome conn config bytes expect with
        | .drop => pure ()
        | .reject code reason body => Transport.sendAll conn #[rawResponse code reason body]
        | .forward bytes body rest keep =>
          if let some _ ← exchange a conn config client extensions rq bytes body none then
            if keep then serveRequests a conn config client extensions fuel rest false
            else pure ()
          else pure ()
        | .lazy bytes initial len rest =>
          -- The body is read when the application asks for it (the router does
          -- when a route matches), with `100 Continue` first if the client
          -- waits for it, as uvicorn does; else it is read and dropped after
          -- the response, so the connection can serve the next request.
          let memo ← IO.mkRef (none : Option (Except Nat ByteArray))
          let complete ← IO.mkRef false
          let started ← IO.mkRef false
          let receive : IO (Except Nat ByteArray) := do
            if let some r ← memo.get then return r
            started.set true
            if expect then Async.block (Transport.sendAll conn #[continueBytes])
            let deadline ← Async.block (Std.Async.Selector.sleep config.lingeringTimeout)
            let (body, how) ← readBodyIO conn config.lingeringTimeout (ByteArray.emptyWithCapacity len ++ initial)
              deadline false (len - initial.size)
            let res : Except Nat ByteArray := match how with
              | .complete _ => .ok body
              | .eof _ => .ok body
              | .timeout => .error 408
            if how matches .complete _ then complete.set true
            memo.set (some res)
            return res
          if let some _ ← exchange a conn config client extensions rq bytes (some .empty) (some receive) then
            let mut done ← complete.get
            unless ← started.get do
              -- unread: the client still sends it, unless it waits for 100 Continue
              unless expect do
                let sink ← IO.mkRef ByteArray.empty
                done := (← readInto conn config.lingeringTimeout sink false
                  (← Std.Async.Selector.sleep config.lingeringTimeout) false (len - initial.size)) matches .complete _
            if done then serveRequests a conn config client extensions fuel rest false

/-- Serve one connection (`serveRequests`), then close it. -/
def serveOne [Transport t] (a : Application) (conn : t) (config : Std.Http.Config)
    (client : Option (String × Nat) := none) (extensions : Extensions := .empty)
    (shutdown : Async Unit := pure ()) : Async Unit := do
  serveRequests a conn config client extensions config.maxRequests .empty true
  Transport.close conn
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

/-- The server's defaults: uvicorn's 5 s keep-alive timeout and no
practical limit on requests per connection; `Std.Http`'s for the rest
(`server: LeanHTTP/1.1`; pass `serverName := some (.ofString! "uvicorn")`
for uvicorn's bytes exactly). -/
def serverDefaults : Std.Http.Config :=
  { keepAliveTimeout := ⟨5000, by decide⟩, maxRequests := 1000000 }

/-- `uvicorn.run(app, host=..., port=...)`: serve until the process is
stopped. -/
def Application.run (a : Application) (host : String := "127.0.0.1") (port : Nat := 8000)
    (config : Std.Http.Config := serverDefaults) : IO Unit := do
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
