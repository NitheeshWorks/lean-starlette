import LeanStarlette.RepoImpl.Head
import LeanHttpx.RepoImpl.H1Body

/-!
# RepoImpl: chunked request bodies, read by the transport

`Std.Http` reads a body by copying its unconsumed input on every receive,
which is quadratic in a body that arrives in many reads. The transport reads
a `Content-Length` body itself (`readBody`); this module does the same for
`Transfer-Encoding: chunked`, in two parts:

* `ChunkScan.feed` decides, piece by piece as bytes arrive, where the body
  ends. It enforces h11's limits as uvicorn runs it: a chunk-size line or
  trailer block still incomplete after a receive and over 16 KiB
  (`h11_max_incomplete_event_size`), or a size of more than 20 hex digits,
  is a 400 and `max_body_size` on the decoded size
  (413). It only skips data, so each byte is touched a bounded number of
  times.
* `decodeChunkedBody` then decodes the received bytes, once, with
  lean-httpx's chunked codec parsers (`H1.chunkSizeLine`, `H1.lastChunk`)
  and slices for the data, appended to one buffer of the decoded size;
  `decodeChunkedBody_encode` proves it returns exactly the
  concatenated chunks of any chunk-encoded body.

`Std.Http` is then handed the head alone (`hideFraming`) and the
application the decoded body; request trailers are dropped, as uvicorn
drops them.
-/

namespace LeanStarlette

open LeanHttpx LeanHttpx.H1 Keel

/-! ## Decoding -/

/-- Decode chunks from `pos`, appending each chunk's data to `acc`: each
chunk-size line with the codec's `chunkSizeLine`, its data as one slice, then
the last chunk and trailers with the codec's `lastChunk`. The output and the
position after the body. -/
def decodeChunksInto (b : ByteArray) : Nat → Nat → ByteArray → Option (ByteArray × Nat)
  | 0, _, _ => none
  | fuel + 1, pos, acc =>
    match (chunkSizeLine (ε := Unit)).run b pos with
    | .error _ _ => none
    | .ok n j =>
      if n = 0 then
        match (lastChunk (ε := Unit)).run b pos with
        | .ok _ k => some (acc, k)
        | .error _ _ => none
      else if b[j + n]? = some CR ∧ b[j + n + 1]? = some LF then
        decodeChunksInto b fuel (j + n + 2) (acc ++ b.extract j (j + n))
      else none

/-- Decode the chunked body that starts at `start`, appending its data to
`into`: the output and the position after the body. Every chunk takes at
least four bytes, so `b.size + 1` steps suffice. -/
def decodeChunkedBody (b : ByteArray) (start : Nat) (into : ByteArray := .empty) : Option (ByteArray × Nat) :=
  decodeChunksInto b (b.size + 1) start into

/-! ## Where the body ends -/

/-- h11's `max_incomplete_event_size` as uvicorn sets it (16 KiB): the
longest chunk-size line, or trailer block, it buffers. -/
def maxChunkEvent : Nat := 16 * 1024

/-- Where a chunked body's reader is. -/
inductive ChunkScan where
  /-- Reading a chunk-size line; the bytes of it so far. -/
  | sizeLine (line : ByteArray)
  /-- Skipping this many bytes of chunk data and its CRLF. -/
  | data (left : Nat)
  /-- After the last chunk: the trailer bytes so far. -/
  | trailers (acc : ByteArray)
  /-- The body ended; this many bytes of the last piece were part of it. -/
  | done (used : Nat)
  /-- Not a valid chunked body (h11's message). -/
  | bad (message : String)
  /-- The decoded body is over the limit. -/
  | tooLarge

/-- The value of a chunk-size line (without its CRLF), if it starts with 1 to
20 hex digits. -/
def chunkLineSize (line : ByteArray) : Option Nat := Id.run do
  let mut v := 0
  let mut k := 0
  for c in line.data do
    if isHexByte c then
      if k == 20 then return none
      v := v * 16 + hexVal c; k := k + 1
    else break
  return if k == 0 then none else some v

/-- Whether trailer bytes are complete: a lone CRLF, or ending in a blank line. -/
def trailersDone (t : ByteArray) : Bool :=
  (t.size == 2 && t[0]! == CR && t[1]! == LF) ||
  (t.size ≥ 4 && t[t.size - 4]! == CR && t[t.size - 3]! == LF && t[t.size - 2]! == CR && t[t.size - 1]! == LF)

/-- Feed one received piece. `got` is the decoded size so far and `limit`
the largest allowed; the new state and decoded size. -/
def ChunkScan.feed (st : ChunkScan) (piece : ByteArray) (got limit : Nat) : ChunkScan × Nat := Id.run do
  let mut st := st
  let mut got := got
  let mut i := 0
  -- each pass consumes at least one byte of the piece
  for _ in [0:piece.size + 1] do
    if i ≥ piece.size then break
    match st with
    | .data left =>
      let k := min left (piece.size - i)
      i := i + k
      st := if left - k == 0 then .sizeLine .empty else .data (left - k)
    | .sizeLine line =>
      let c := piece[i]!
      i := i + 1
      if c != LF then
        st := .sizeLine (line.push c)
      else
        match chunkLineSize line with
        | none => return (.bad "illegal chunk header", got)
        | some n =>
          if got + n > limit then return (.tooLarge, got)
          got := got + n
          st := if n == 0 then .trailers .empty else .data (n + 2)
    | .trailers acc =>
      let acc := acc.push piece[i]!
      i := i + 1
      if trailersDone acc then return (.done i, got)
      st := .trailers acc
    | s => return (s, got)
  -- h11 bounds what it holds of an event still incomplete after a receive
  match st with
  | .sizeLine line => if line.size > maxChunkEvent then return (.bad "Receive buffer too long", got)
  | .trailers acc => if acc.size > maxChunkEvent then return (.bad "Receive buffer too long", got)
  | _ => pure ()
  return (st, got)

/-! ## The request handed to `Std.Http` -/

/-- For a head whose body is chunked (exactly one `Transfer-Encoding`, whose
value is `chunked`, and no `Content-Length`): the index just past the head.
Anything else is left to `Std.Http`. -/
def chunkedBodyStart (head : ByteArray) : Option Nat := do
  let e ← findHeadEnd head 0
  let hs := (headerLines head e).map splitHeaderLine
  if hs.any (·.1 == "content-length".toUTF8.toList) then none
  match hs.filter (·.1 == "transfer-encoding".toUTF8.toList) with
  | [(_, v)] => if v.map (fun b => if 65 ≤ b && b ≤ 90 then b + 32 else b) == "chunked".toUTF8.toList then some e else none
  | _ => none

end LeanStarlette
