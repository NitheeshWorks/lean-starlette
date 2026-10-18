import LeanStarlette.RepoImpl.Files
import LeanStarlette.RepoImpl.Exceptions

/-!
# RepoImpl: reading files (effectful)

The disk side of `FileResponse` and `StaticFiles`. This module and
`Transport.lean` are the only effectful ones; every decision they act on is
a pure function of `RepoImpl/Files.lean` and `RepoImpl/Range.lean`.

* `sendFileRange` streams `[start, end)` of a file in 64 KiB chunks: one
  chunk in memory at a time. It recurses on the bytes left, each step
  sending at least one, so it is total; a file that turns out shorter than
  its `stat` raises, as upstream's multi-range sender does.
* `prepareFile` resolves a `FileResponse` for a request: `stat`, the stat
  headers, `Range`/`If-Range`, and the stream (none for `HEAD`: the file is
  not read).
* `StaticFiles` serves a directory. A route path becomes segments that cannot
  leave the directory (`staticSegments`, proved), and unless
  `follow_symlink` the resolved path must also lie under the directory's
  real path, so a symlink cannot lead outside it.
-/

namespace LeanStarlette

open Std.Async

/-- `FileResponse.chunk_size`. -/
def fileChunkSize : Nat := 64 * 1024

/-- Read and drop `n` bytes (there is no `seek` on a Lean handle). -/
def skipBytes (h : IO.FS.Handle) (path : String) (n : Nat) : IO Unit := do
  if hn : n = 0 then pure () else
  let chunk ← h.read (min fileChunkSize n).toUSize
  if hc : chunk.size = 0 then throw (IO.userError s!"File at path {path} is shorter than expected.")
  else
    have : n - chunk.size < n := by omega
    skipBytes h path (n - chunk.size)
termination_by n

/-- Send the next `n` bytes of the handle, a chunk at a time. -/
def sendBytes (h : IO.FS.Handle) (path : String) (send : ByteArray → Async Unit) (n : Nat) : Async Unit := do
  if hn : n = 0 then pure () else
  let chunk ← (h.read (min fileChunkSize n).toUSize : IO ByteArray)
  if hc : chunk.size = 0 then throw (IO.userError s!"File at path {path} is shorter than expected.")
  else
    send chunk
    have : n - chunk.size < n := by omega
    sendBytes h path send (n - chunk.size)
termination_by n

/-- Send bytes `[start, end)` of a file. -/
def sendFileRange (path : String) (r : Nat × Nat) (send : ByteArray → Async Unit) : Async Unit := do
  let h ← (IO.FS.Handle.mk path .read : IO IO.FS.Handle)
  skipBytes h path r.1
  sendBytes h path send (r.2 - r.1)

/-- Send several ranges as `multipart/byteranges`. -/
def sendMultipart (path boundary contentType : String) (size : Nat) (rs : List (Nat × Nat))
    (send : ByteArray → Async Unit) : Async Unit := do
  for r in rs do
    send (multipartPartHeader boundary contentType r size).toUTF8
    sendFileRange path r send
    send "\r\n".toUTF8
  send s!"--{boundary}--".toUTF8

/-- `stat(path)`: size and modification time in nanoseconds, of a regular
file. -/
def statFile (path : String) : IO (Nat × Int) := do
  let md ← try (System.FilePath.metadata path)
    catch _ => throw (IO.userError s!"File at path {path} does not exist.")
  unless md.type == .file do throw (IO.userError s!"File at path {path} is not a file.")
  return (md.byteSize.toNat, md.modified.sec * 1000000000 + md.modified.nsec.toNat)

/-- A fresh `multipart/byteranges` boundary (`token_hex(13)`). -/
def newBoundary : IO String := do
  let bs ← IO.getRandomBytes 13
  return String.join (bs.toList.map fun b =>
    let s := hexOf b.toNat
    if s.length < 2 then "0" ++ s else s)

/-- An empty stream (the body of a `HEAD` response). -/
def emptyStream : ContentStream := fun _ => pure ()

/-- `FileResponse.__call__`, up to sending: resolve a file response for a
request into a streamed one. Other responses are returned unchanged. -/
def prepareFile (req : Request) (r : Response) : IO Response := do
  let some src := r.file | return r
  let (size, mtime) ← match src.stat with
    | some st => pure st
    | none => statFile src.path.toString
  let headers := fileStatHeaders r.headers size mtime
  let boundary ← newBoundary
  let headOnly := req.method == "HEAD"
  let path := src.path.toString
  let body (s : ContentStream) : Option ContentStream := some (if headOnly then emptyStream else s)
  match filePlan req.headers r.status_code headers size boundary with
  | .whole _ hs => return { r with headers := hs, file := none, stream := body (sendFileRange path (0, size)) }
  | .single rg hs =>
    return { r with status_code := 206, body := .empty, h_status := by decide, h_body := .inr rfl, headers := hs, file := none,
                    stream := body (sendFileRange path rg) }
  | .multi rs hs ct =>
    return { r with status_code := 206, body := .empty, h_status := by decide, h_body := .inr rfl, headers := hs, file := none,
                    stream := body (sendMultipart path boundary ct size rs.ranges) }
  | .error e => return e

/-- The whole body of a response, a stream run to the end (for tests and
for callers that need the bytes; the transport streams instead). -/
def Response.readBody (r : Response) : IO ByteArray := do
  match r.stream with
  | none => pure r.body
  | some gen =>
    let acc ← IO.mkRef ByteArray.empty
    let res ← (gen fun c => (acc.modify (· ++ c) : IO Unit)).toIO
    match ← IO.wait res with
    | .ok () => acc.get
    | .error e => throw e

/-! ## StaticFiles -/

/-- `stat` that answers `none` for a missing entry and raises `401` for a
permission error, as `StaticFiles.lookup_path` and `get_response` do. -/
def statEntry (path : String) : AppM (Option IO.FS.Metadata) := do
  match ← (System.FilePath.metadata path).toBaseIO with
  | .ok md => pure (some md)
  | .error (.permissionDenied ..) => throw (HTTPException 401)
  | .error _ => pure none

/-- Whether `p` is `dir` or below it, as strings of resolved paths. -/
def isUnder (dir p : String) : Bool := p == dir || p.startsWith (dir ++ "/")

/-- `StaticFiles.lookup_path`: the full path and its metadata, for safe
segments. Unless `follow_symlink`, the real path must lie under the
directory's real path. -/
def lookupStatic (directory : String) (follow_symlink : Bool) (segs : List String) :
    AppM (Option (String × IO.FS.Metadata)) := do
  let full := joinUnder directory segs
  let some md ← statEntry full | return none
  if follow_symlink then return some (full, md)
  let real ← (IO.FS.realPath full : IO _)
  let realDir ← (IO.FS.realPath directory : IO _)
  if isUnder realDir.toString real.toString then return some (full, md) else return none

/-- The response for a found regular file. -/
def staticFile (full : String) (md : IO.FS.Metadata) (req : Request) : Response :=
  staticFileResponse full md.byteSize.toNat (md.modified.sec * 1000000000 + md.modified.nsec.toNat) req.headers

/-- `StaticFiles(directory=..., html=False, check_dir=True,
follow_symlink=False)`. The directory check happens on each request
(upstream checks at construction and on the first request): a missing
directory is a `RuntimeError`, so a 500. -/
def StaticFiles (directory : String) (html : Bool := false) (check_dir : Bool := true)
    (follow_symlink : Bool := false) : App := fun req => do
  if check_dir then
    match ← (System.FilePath.metadata directory).toBaseIO with
    | .ok md =>
      unless md.type == .dir || md.type == .symlink do
        throwThe IO.Error (IO.userError s!"StaticFiles path '{directory}' is not a directory.")
    | .error _ => throwThe IO.Error (IO.userError s!"StaticFiles directory '{directory}' does not exist.")
  unless req.method == "GET" || req.method == "HEAD" do
    throw (HTTPException 405 (headers := [("Allow", "GET, HEAD")]))
  let notFound : AppM Response := do
    if html then
      if let some (full, md) ← lookupStatic directory follow_symlink ["404.html"] then
        if md.type == .file then
          return FileResponse full (status_code := 404)
            (stat_result := some (md.byteSize.toNat, md.modified.sec * 1000000000 + md.modified.nsec.toNat))
    throw (HTTPException 404)
  let some segs := staticSegments req.routePath | notFound
  match ← lookupStatic directory follow_symlink segs with
  | some (full, md) =>
    if md.type == .file then return staticFile full md req
    else if md.type == .dir && html then
      match ← lookupStatic directory follow_symlink (segs ++ ["index.html"]) with
      | some (ifull, imd) =>
        if imd.type == .file then
          if !req.path.endsWith "/" then
            let u := req.url
            return RedirectResponse (toString { u with path := u.path ++ "/" })
          return staticFile ifull imd req
        else notFound
      | none => notFound
    else notFound
  | none => notFound

end LeanStarlette
