import LeanStarlette.RepoImpl.Text

/-!
# RepoImpl: the request line, before `Std.Http` sees it

`Std.Http`'s request-target parser enforces URI limits that its
`Std.Http.Config` does not expose (at most 100 query parameters, 128 path
segments of 256 bytes, well-formed `%XX` escapes). uvicorn applies none of
them: it hands the raw target to Starlette, which decodes leniently. So the
transport moves the raw target into a header of its own and gives
`Std.Http` the target `/`, which always parses; the application reads the
target back from that header (`targetHeader`).

All of this is a pure function of the bytes read, total and linear in their
length:

* `findHeadEnd` finds the blank line that ends the head, scanning only bytes
  it has not scanned before (so a head sent a byte at a time costs linear,
  not quadratic, time);
* `rewriteHead` checks the request line and rewrites it, or says which error
  uvicorn would answer.
-/

namespace LeanStarlette

/-- The header carrying the raw request target to the application. A client
cannot forge it: the transport adds its own first, and the request reader
drops every copy after taking the first. -/
def targetHeader : String := "x-lean-starlette-target"

/-- The longest request target uvicorn (httptools) accepts. -/
def maxTargetLength : Nat := 65535

/-- The most head bytes read before answering 431 (uvicorn has no limit;
see `CONTRIBUTING.md`). -/
def maxHeadBytes : Nat := 1024 * 1024

/-- Whether `buf` has `\r\n\r\n` ending at or after `from`: the index just past
it. -/
def findHeadEnd (buf : ByteArray) (start : Nat) : Option Nat :=
  go start (buf.size - start)
where
  go (i : Nat) : Nat → Option Nat
    | 0 => none
    | fuel + 1 =>
      if i + 3 < buf.size && buf[i]! == 13 && buf[i+1]! == 10 && buf[i+2]! == 13 && buf[i+3]! == 10 then
        some (i + 4)
      else go (i + 1) fuel

/-- The index of the first `\r\n` at or after `i`. -/
def findCRLF (buf : ByteArray) (i : Nat) : Option Nat :=
  go i (buf.size - i)
where
  go (i : Nat) : Nat → Option Nat
    | 0 => none
    | fuel + 1 => if i + 1 < buf.size && buf[i]! == 13 && buf[i+1]! == 10 then some i else go (i + 1) fuel

/-- What the transport does with a head. -/
inductive HeadAction where
  /-- Hand these bytes to `Std.Http`. -/
  | forward (bytes : ByteArray)
  /-- Answer with this status and body and close (uvicorn's answers). -/
  | reject (status : Nat) (reason body : String)

/-- uvicorn's answer to a request it cannot parse. -/
def invalidRequest : HeadAction := .reject 400 "Bad Request" "Invalid HTTP request received."

/-- Skip the empty lines HTTP/1.1 allows before a request line. -/
def skipEmptyLines (buf : ByteArray) : Nat → Nat → Nat
  | i, 0 => i
  | i, fuel + 1 =>
    if i + 1 < buf.size && buf[i]! == 13 && buf[i+1]! == 10 then skipEmptyLines buf (i + 2) fuel else i

/-- Split bytes on single spaces. -/
def splitSpaces (bs : List UInt8) : List (List UInt8) :=
  let (cur, done) := bs.foldl (init := (([] : List UInt8), ([] : List (List UInt8))))
    fun (cur, done) b => if b == 32 then ([], cur.reverse :: done) else (b :: cur, done)
  (cur.reverse :: done).reverse

/-- Check the request line of a complete head and move its target into
`targetHeader`. A request line that is not `method SP target SP version` is
forwarded unchanged, for `Std.Http` to reject. -/
def rewriteHead (buf : ByteArray) : HeadAction :=
  let start := skipEmptyLines buf 0 8
  match findCRLF buf start with
  | none => .forward buf
  | some eol =>
    let line := (buf.extract start eol).toList
    match splitSpaces line with
    | [method, target, version] =>
      if target.length > maxTargetLength then .reject 414 "URI Too Long" "URI Too Long"
      else if target.isEmpty || target.any (fun b => b < 0x21 || b > 0x7e) then invalidRequest
      else
        let newLine := method ++ " / ".toUTF8.toList ++ version ++ "\r\n".toUTF8.toList ++
          (targetHeader ++ ": ").toUTF8.toList ++ target
        .forward (ByteArray.mk newLine.toArray ++ buf.extract eol buf.size)
    | _ => .forward buf

/-- The bytes of a response the transport writes itself. -/
def rawResponse (status : Nat) (reason body : String) : ByteArray :=
  (s!"HTTP/1.1 {status} {reason}\r\ncontent-type: text/plain; charset=utf-8\r\nconnection: close\r\n" ++
    s!"content-length: {body.utf8ByteSize}\r\n\r\n{body}").toUTF8

/-- The status line of response bytes `Std.Http` wrote: `(code, reason)`, if
the response has an empty body (`Content-Length: 0`). -/
def emptyErrorResponse? (bs : ByteArray) : Option (Nat × String) :=
  let s := (String.fromUTF8? bs).getD ""
  if !s.startsWith "HTTP/1.1 " then none else
  if !((s.splitOn "Content-Length: 0\r\n").length > 1) then none else
  match (s.drop 9).toString.splitOn "\r\n" with
  | line :: _ =>
    match line.splitOn " " with
    | code :: reason => (code.toNat?).map fun c => (c, " ".intercalate reason)
    | [] => none
  | [] => none

/-- The body uvicorn sends with a protocol-level error. -/
def errorBody (code : Nat) (reason : String) : String :=
  if code == 400 then "Invalid HTTP request received." else reason

end LeanStarlette
