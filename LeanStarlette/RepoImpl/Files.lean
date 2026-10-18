import LeanStarlette.RepoImpl.Responses
import LeanStarlette.RepoImpl.Range
import LeanStarlette.RepoImpl.HttpDate

/-!
# RepoImpl: files and static files, the pure part

Everything `FileResponse` and `StaticFiles` decide without touching the
disk; `Transport/Files.lean` does the reading.

* `FileResponse` builds the response's headers and records the file.
* `fileStatHeaders` is `set_stat_headers`: `content-length`,
  `last-modified`, `etag`.
* `filePlan` is the `__call__` decision: the whole file, one range (206), several
  ranges (206 `multipart/byteranges`), or a 400/416 error.
* `isNotModified` is `StaticFiles.is_not_modified` (`etag_304_iff`).
* `staticSegments` turns a route path into path segments that cannot leave
  the directory (`staticSegments_safe`).
-/

namespace LeanStarlette

/-! ## Media types -/

/-- `mimetypes.guess_type` for the common extensions. -/
def guessType (path : String) : Option String :=
  let ext := (lowerAscii ((path.splitOn ".").getLast?.getD ""))
  if !((path.splitOn "/").getLast?.getD path).contains '.' then none else
  match ext with
  | "html" | "htm" => some "text/html" | "css" => some "text/css" | "js" | "mjs" => some "text/javascript"
  | "json" => some "application/json" | "txt" => some "text/plain" | "csv" => some "text/csv"
  | "xml" => some "text/xml" | "png" => some "image/png" | "jpg" | "jpeg" => some "image/jpeg"
  | "gif" => some "image/gif" | "svg" => some "image/svg+xml" | "ico" => some "image/vnd.microsoft.icon"
  | "webp" => some "image/webp" | "pdf" => some "application/pdf" | "zip" => some "application/zip"
  | "gz" => some "application/gzip" | "wasm" => some "application/wasm" | "mp4" => some "video/mp4"
  | "mp3" => some "audio/mpeg" | "woff" => some "font/woff" | "woff2" => some "font/woff2"
  | "md" => some "text/markdown" | "tar" => some "application/x-tar"
  | _ => none

/-! ## FileResponse -/

/-- `FileResponse(path, status_code=200, headers=None, media_type=None,
background=None, filename=None, stat_result=None,
content_disposition_type="attachment")`. The file is read when the response
is sent. -/
def Responses.FileResponse (path : String) (status_code : Nat := 200) (headers : List (String × String) := [])
    (media_type : Option String := none) (background : BackgroundTasks := {})
    (filename : Option String := none) (stat_result : Option (Nat × Int) := none)
    (content_disposition_type : String := "attachment") (h : StatusCode.Valid status_code := by decide) :
    LeanStarlette.Response :=
  let mt := media_type.getD ((guessType (filename.getD path)).getD "application/octet-stream")
  let hs := Headers.ofList headers
  let hs := if hs.contains "content-type" then hs else hs.append "content-type" (contentType mt)
  let hs := hs.setdefault "accept-ranges" "bytes"
  let hs := match filename with
    | none => hs
    | some fn =>
      let q := quote fn
      hs.setdefault "content-disposition"
        (if q != fn then s!"{content_disposition_type}; filename*=utf-8''{q}"
         else s!"{content_disposition_type}; filename=\"{fn}\"")
  { status_code, headers := hs, body := .empty, h_status := h, h_body := .inr rfl,
    file := some { path := path, stat := stat_result }, background }

export Responses (FileResponse)

/-- Lower-case hex of a number. -/
def hexOf (n : Nat) : String :=
  String.ofList ((Nat.toDigits 16 n))

/-- The `ETag` of a file: its modification time (ns) and size. Upstream
hashes `f"{mtime}-{size}"` with MD5; the value is opaque to clients, so
this port uses the pair itself (see `CONTRIBUTING.md`). -/
def fileETag (size : Nat) (mtimeNs : Int) : String :=
  "\"" ++ hexOf mtimeNs.toNat ++ "-" ++ hexOf size ++ "\""

/-- `set_stat_headers`. -/
def fileStatHeaders (h : Headers) (size : Nat) (mtimeNs : Int) : Headers :=
  let h := h.setdefault "content-length" (toString size)
  let h := h.setdefault "last-modified" (formatHttpDate (mtimeNs / 1000000000))
  h.setdefault "etag" (fileETag size mtimeNs)

/-! ## Sending a file: the plan -/

/-- What sending a file comes to. -/
inductive FilePlan (size : Nat) where
  /-- The whole file, with these headers and status. -/
  | whole (status : Nat) (headers : Headers)
  /-- One range: 206 with `content-range`. -/
  | single (r : Nat × Nat) (headers : Headers)
  /-- Several ranges: 206 `multipart/byteranges`. -/
  | multi (rs : ByteRanges size) (headers : Headers) (contentType : String)
  /-- A 400 or 416 response instead of the file. -/
  | error (r : Response)

/-- `_should_use_range(if_range)`. -/
def shouldUseRange (respHeaders : Headers) (ifRange : String) : Bool :=
  !ifRange.startsWith "W/" &&
    (some ifRange == respHeaders.get? "last-modified" || some ifRange == respHeaders.get? "etag")

/-- The part header before each range of a `multipart/byteranges` body. -/
def multipartPartHeader (boundary contentType : String) (r : Nat × Nat) (size : Nat) : String :=
  s!"--{boundary}\r\nContent-Type: {contentType}\r\nContent-Range: bytes {r.1}-{r.2 - 1}/{size}\r\n\r\n"

/-- The length of a `multipart/byteranges` body (upstream's
`generate_multipart`, computed from the parts themselves). -/
def multipartLength (boundary contentType : String) (rs : List (Nat × Nat)) (size : Nat) : Nat :=
  (rs.map fun r => (multipartPartHeader boundary contentType r size).utf8ByteSize + (r.2 - r.1) + 2).sum +
    4 + boundary.utf8ByteSize

/-- `FileResponse.__call__`'s decision, from the request headers, the
response's status and headers (with the stat headers set), and the file
size. -/
def filePlan (reqHeaders : Headers) (status : Nat) (headers : Headers) (size : Nat) (boundary : String) :
    FilePlan size :=
  match reqHeaders.get? "range" with
  | none => .whole status headers
  | some range =>
    if status != 200 then .whole status headers
    else if (reqHeaders.get? "if-range").any (!shouldUseRange headers ·) then .whole status headers
    else
      match parseRangeHeader range size with
      | .full => .whole status headers
      | .malformed msg => .error (PlainTextResponse msg (status_code := 400))
      | .unsatisfiable => .error (PlainTextResponse (status_code := 416) (headers := [("Content-Range", s!"bytes */{size}")]))
      | .ranges rs =>
        match rs.ranges with
        | [r] => .single r ((headers.set "content-range" (contentRange r size)).set "content-length" (toString (r.2 - r.1)))
        | _ =>
          let ct := (headers.get? "content-type").getD "application/octet-stream"
          .multi rs ((headers.set "content-type" s!"multipart/byteranges; boundary={boundary}").set
            "content-length" (toString (multipartLength boundary ct rs.ranges size))) ct

/-! ## Not modified -/

/-- `NotModifiedResponse.NOT_MODIFIED_HEADERS`. -/
def notModifiedHeaders : List String := ["cache-control", "content-location", "date", "etag", "expires", "vary"]

/-- The entity tags of an `If-None-Match` value, weak prefixes removed. -/
def ifNoneMatchTags (v : String) : List String :=
  (v.splitOn ",").map fun t =>
    let t := String.ofList (stripWs t.toList)
    if t.startsWith "W/" then (t.drop 2).toString else t

/-- `StaticFiles.is_not_modified(response_headers, request_headers)`. -/
def isNotModified (etag : String) (lastModified : String) (req : Headers) : Bool :=
  match req.get? "if-none-match" with
  | some inm =>
    if inm.isEmpty then byDate else
    String.ofList (stripWs inm.toList) == "*" || (ifNoneMatchTags inm).contains etag
  | none => byDate
where
  byDate : Bool :=
    match (req.get? "if-modified-since").bind parseHttpDate, parseHttpDate lastModified with
    | some ims, some lm => ims.ge lm
    | _, _ => false

/-- `NotModifiedResponse(headers)`: 304 with the cache headers only. -/
def notModifiedResponse (h : Headers) : Response :=
  Response (status_code := 304) (headers := h.raw.filter fun p => notModifiedHeaders.contains p.1)

/-- `StaticFiles.file_response`: a 304 when the request's validators match,
else the file. `fileHeaders` are the file's headers with the stat headers
set. -/
def staticFileResponse (path : String) (size : Nat) (mtimeNs : Int) (req : Headers) : Response :=
  let r := FileResponse path (stat_result := some (size, mtimeNs))
  let hs := fileStatHeaders r.headers size mtimeNs
  if isNotModified (fileETag size mtimeNs) (formatHttpDate (mtimeNs / 1000000000)) req then
    notModifiedResponse hs
  else { r with headers := hs }

/-! ## Static paths -/

/-- A path segment that names an entry in a directory: not empty, `.` or
`..`, and with no separator or NUL. -/
def isNormalName (s : String) : Bool :=
  !s.isEmpty && s != "." && s != ".." && !s.contains '/' && !s.contains '\\' && !s.contains '\x00'

/-- Resolve `.` and `..` in a route path, refusing a path that climbs above
the directory (upstream normalises and then rejects it with `commonpath`;
both answer 404). A segment with a backslash or NUL is refused too. -/
def staticSegments (routePath : String) : Option (List String) :=
  go [] (routePath.splitOn "/")
where
  go (acc : List String) : List String → Option (List String)
    | [] => some acc.reverse
    | s :: rest =>
      if s.isEmpty || s == "." then go acc rest
      else if s == ".." then
        match acc with
        | [] => none
        | _ :: acc => go acc rest
      else if isNormalName s then go (s :: acc) rest
      else none

/-- The file-system path for segments under a directory. -/
def joinUnder (dir : String) (segs : List String) : String :=
  segs.foldl (fun p s => p ++ "/" ++ s) dir

end LeanStarlette
