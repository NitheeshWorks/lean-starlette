import LeanStarlette.RepoImpl.Head
import LeanStarlette.RepoImpl.HttpDate
import LeanHttpx.RepoImpl.H1Body

/-!
# RepoImpl: a response on the wire, as uvicorn (h11) writes it

The transport writes responses itself, byte for byte as uvicorn 0.54 with
h11 0.16 does for the same request and ASGI messages; `Std.Http` only
parses the request head. Everything here is pure:

* `statusPhrase` is uvicorn's `STATUS_PHRASES`: Python's
  `http.HTTPStatus(code).phrase` (RFC 9110 names, `422 Unprocessable
  Content`), empty for a code Python does not name.
* `wireHead` is the status line and header block: uvicorn's default
  headers (`date`, `server`) first, then the application's in its order
  and spelling, then `connection: close` when the request carried exactly
  that field (uvicorn's `CLOSE_HEADER`); then h11's
  `_clean_up_response_headers_for_sending`: a body of unknown length is
  chunked (`Transfer-Encoding: chunked`, appended) for an HTTP/1.1 peer and
  sent until close for HTTP/1.0, and a connection that will not be kept gets
  `Connection: close` (title-cased, appended, replacing the field).
* `chunkFrame` is h11's `ChunkedWriter`: lean-httpx's `encodeChunk`,
  nothing for an empty piece; the frames and `lastChunkBytes` decode back
  to the pieces (`wire_chunks_decode`).
-/

namespace LeanStarlette

/-- uvicorn's reason phrase for a status: `http.HTTPStatus(code).phrase`
(Python 3.13), or empty. -/
def statusPhrase : Nat → String
  | 100 => "Continue"
  | 101 => "Switching Protocols"
  | 102 => "Processing"
  | 103 => "Early Hints"
  | 200 => "OK"
  | 201 => "Created"
  | 202 => "Accepted"
  | 203 => "Non-Authoritative Information"
  | 204 => "No Content"
  | 205 => "Reset Content"
  | 206 => "Partial Content"
  | 207 => "Multi-Status"
  | 208 => "Already Reported"
  | 226 => "IM Used"
  | 300 => "Multiple Choices"
  | 301 => "Moved Permanently"
  | 302 => "Found"
  | 303 => "See Other"
  | 304 => "Not Modified"
  | 305 => "Use Proxy"
  | 307 => "Temporary Redirect"
  | 308 => "Permanent Redirect"
  | 400 => "Bad Request"
  | 401 => "Unauthorized"
  | 402 => "Payment Required"
  | 403 => "Forbidden"
  | 404 => "Not Found"
  | 405 => "Method Not Allowed"
  | 406 => "Not Acceptable"
  | 407 => "Proxy Authentication Required"
  | 408 => "Request Timeout"
  | 409 => "Conflict"
  | 410 => "Gone"
  | 411 => "Length Required"
  | 412 => "Precondition Failed"
  | 413 => "Content Too Large"
  | 414 => "URI Too Long"
  | 415 => "Unsupported Media Type"
  | 416 => "Range Not Satisfiable"
  | 417 => "Expectation Failed"
  | 418 => "I'm a Teapot"
  | 421 => "Misdirected Request"
  | 422 => "Unprocessable Content"
  | 423 => "Locked"
  | 424 => "Failed Dependency"
  | 425 => "Too Early"
  | 426 => "Upgrade Required"
  | 428 => "Precondition Required"
  | 429 => "Too Many Requests"
  | 431 => "Request Header Fields Too Large"
  | 451 => "Unavailable For Legal Reasons"
  | 500 => "Internal Server Error"
  | 501 => "Not Implemented"
  | 502 => "Bad Gateway"
  | 503 => "Service Unavailable"
  | 504 => "Gateway Timeout"
  | 505 => "HTTP Version Not Supported"
  | 506 => "Variant Also Negotiates"
  | 507 => "Insufficient Storage"
  | 508 => "Loop Detected"
  | 510 => "Not Extended"
  | 511 => "Network Authentication Required"
  | _ => ""

/-- What a response's framing depends on in its request. -/
structure WireRequest where
  method : String := "GET"
  /-- The request was HTTP/1.1 (not 1.0). -/
  http11 : Bool := true
  /-- h11's keep-alive: HTTP/1.1 and no `close` token in `Connection`. -/
  keepAlive : Bool := true
  /-- A header field `connection: close`, exactly (uvicorn's `CLOSE_HEADER`). -/
  closeHeader : Bool := false

/-- How the body follows the head. -/
inductive WireBody where
  /-- No body bytes (HEAD, 204, 304). -/
  | none
  /-- The bytes as they are (`Content-Length`). -/
  | raw
  /-- Chunked frames, then the last chunk. -/
  | chunked
  /-- The bytes as they are, then the connection is closed (HTTP/1.0). -/
  | untilClose
  deriving DecidableEq, Repr

/-- h11's `get_comma_header`: every value of the field, split on commas,
stripped and lower-cased, empty items dropped. -/
def commaHeader (hs : List (String × String)) (name : String) : List String :=
  (hs.filter (lowerAscii ·.1 == name)).flatMap fun (_, v) =>
    ((lowerAscii v).splitOn ",").filterMap fun t =>
      let t := t.trimAscii.toString
      if t.isEmpty then none else some t

/-- Remove a field (any spelling). -/
def dropField (hs : List (String × String)) (name : String) : List (String × String) :=
  hs.filter (lowerAscii ·.1 != name)

/-- Insert into a sorted list of distinct strings. -/
def insertSorted (x : String) : List String → List String
  | [] => [x]
  | y :: ys => if x == y then y :: ys else if x < y then x :: y :: ys else y :: insertSorted x ys

/-- The response head h11 writes, how its body follows, and whether the
connection is kept for another request. -/
structure WireHead where
  /-- The status line. -/
  status : String
  /-- The fields, in the order written. -/
  fields : List (String × String)
  body : WireBody
  keepAlive : Bool

/-- The bytes of a head: the status line, each field, a blank line. -/
def WireHead.bytes (h : WireHead) : ByteArray :=
  (h.status ++ String.join (h.fields.map fun (n, v) => s!"{n}: {v}\r\n") ++ "\r\n").toUTF8

/-- The status line and fields of a response, as uvicorn and h11 write them
(module docstring). `defaults` are uvicorn's `date` and `server`. -/
def wireHead (rq : WireRequest) (defaults : List (String × String)) (status : Nat)
    (headers : List (String × String)) : WireHead :=
  let hs := defaults ++ headers
  let hs := if rq.closeHeader && !hs.contains ("connection", "close") then hs ++ [("connection", "close")] else hs
  let headMethod := if rq.method == "HEAD" then "GET" else rq.method
  let noBody := status == 204 || status == 304 || (headMethod == "CONNECT" && 200 ≤ status && status < 300)
  let unknown := !noBody && (commaHeader hs "transfer-encoding").isEmpty && (commaHeader hs "content-length").isEmpty
  let (hs, needClose) :=
    if unknown then
      let hs := dropField hs "content-length"
      if rq.http11 then (dropField hs "transfer-encoding" ++ [("Transfer-Encoding", "chunked")], false)
      else (dropField hs "transfer-encoding", rq.method != "HEAD")
    else (hs, false)
  let hs :=
    if !rq.keepAlive || needClose then
      let toks := ((commaHeader hs "connection").filter (· != "keep-alive")).foldr insertSorted []
      dropField hs "connection" ++ (insertSorted "close" toks).map ("Connection", ·)
    else hs
  let keep := rq.keepAlive && !needClose && !(commaHeader hs "connection").contains "close"
  let body : WireBody :=
    if rq.method == "HEAD" || noBody then .none
    else if !(commaHeader hs "transfer-encoding").isEmpty then .chunked
    else if !(commaHeader hs "content-length").isEmpty then .raw
    else .untilClose
  { status := s!"HTTP/1.1 {status} {statusPhrase status}\r\n", fields := hs, body, keepAlive := keep }

/-- One piece of a chunked body: h11 writes nothing for an empty piece. -/
def chunkFrame (c : ByteArray) : ByteArray :=
  if c.size = 0 then .empty else ⟨(LeanHttpx.H1.encodeChunk c).toArray⟩

/-- The last chunk, without trailers. -/
def lastChunkFrame : ByteArray := ⟨LeanHttpx.H1.lastChunkBytes.toArray⟩

/-- The bytes of a chunked body sent as `pieces`: each piece's frame, then
the last chunk (what `writeResponse` sends). -/
def wireChunked (pieces : List ByteArray) : ByteArray :=
  pieces.foldl (fun acc c => acc ++ chunkFrame c) .empty ++ lastChunkFrame

/-- `100 Continue`, as uvicorn sends it to a client that expects it. -/
def continueBytes : ByteArray := "HTTP/1.1 100 Continue\r\n\r\n".toUTF8

/-- The fields of a head (up to `e`), as `(lower-cased name, value)` text. -/
def headFields (head : ByteArray) (e : Nat) : List (String × String) :=
  (headerLines head e).map fun l =>
    let (n, v) := splitHeaderLine l
    (String.ofList (n.map fun b => Char.ofNat b.toNat), String.ofList (v.map fun b => Char.ofNat b.toNat))

/-- The method and version of a head's request line. -/
def requestLineParts (head : ByteArray) : String × String :=
  let start := skipEmptyLines head 0 8
  match findCRLF head start with
  | none => ("", "")
  | some eol =>
    match splitSpaces (head.extract start eol).toList with
    | [m, _, v] => (String.ofList (m.map fun b => Char.ofNat b.toNat), String.ofList (v.map fun b => Char.ofNat b.toNat))
    | _ => ("", "")

/-- What framing a response needs from the request with this head (`e`: its end). -/
def wireRequestOf (head : ByteArray) (e : Nat) : WireRequest :=
  let (method, version) := requestLineParts head
  let fs := headFields head e
  let http11 := version != "HTTP/1.0"
  { method, http11
    keepAlive := http11 && !(commaHeader fs "connection").contains "close"
    closeHeader := fs.contains ("connection", "close") }

/-- h11's `has_expect_100_continue`: an HTTP/1.1 request whose `Expect`
lists `100-continue`. -/
def expectsContinue (head : ByteArray) (e : Nat) : Bool :=
  (requestLineParts head).2 != "HTTP/1.0" && (commaHeader (headFields head e) "expect").contains "100-continue"

/-- uvicorn's `date` field value for a Unix time (`email.utils.formatdate(usegmt=True)`). -/
def wireDate (unix : Int) : String := formatHttpDate unix

end LeanStarlette
