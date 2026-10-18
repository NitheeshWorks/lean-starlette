import LeanStarlette.RepoImpl.Middleware
import LeanStarlette.RepoImpl.FileIO
import LeanStarlette.RepoImpl.Deflate

/-!
# RepoImpl: `GZipMiddleware` (`starlette/middleware/gzip.py`)

Upstream decides per ASGI message; here a response is a body in memory or
a stream, and the same rules apply to each:

* passed through untouched: a response that already has
  `Content-Encoding`, a `206`, or an excluded media type;
* a body under `minimum_size` is untouched (`gzip_minimum_size`);
* otherwise `Vary: Accept-Encoding` is added, and when the client accepts
  gzip the body is compressed, with `Content-Encoding: gzip` and the new
  `Content-Length`;
* a stream is compressed piece by piece (each piece sync-flushed, as
  upstream's `Z_SYNC_FLUSH`), without `Content-Length`. A file of under
  64 KiB is one message upstream (`FileResponse`'s chunk size) and is
  treated as a body here too; a `HEAD` response is one empty message.

`compresslevel` is accepted and not used: there is one compressor
(`Deflate`), whose bytes differ from zlib's. A status that forbids a body
(`204`, `304`, `1xx`) is passed through (upstream would compress an empty
body when `minimum_size` is `0`).
-/

namespace LeanStarlette

/-- `DEFAULT_EXCLUDED_CONTENT_TYPES`. -/
def gzipDefaultExcluded : List String :=
  ["application/grpc", "application/gzip", "application/x-gzip", "application/zip", "audio/*", "font/woff",
    "font/woff2", "image/avif", "image/gif", "image/jpeg", "image/png", "image/webp", "text/event-stream", "video/*"]

/-- `content_type.partition(";")[0].strip().lower()`. -/
def mediaTypeOf (ct : String) : String :=
  lowerAscii (String.ofList (stripWs ((splitFirst ';' ct.toList).1)))

/-- Whether a response's media type is excluded: the type, its `type/*`,
and `application/grpc` for `application/grpc+…`. -/
def gzipExcluded (exclude : List String) (h : Headers) : Bool :=
  let mt := mediaTypeOf ((h.get? "content-type").getD "")
  let star := String.ofList ((splitFirst '/' mt.toList).1) ++ "/*"
  let types := [mt, star] ++ (if mt.startsWith "application/grpc+" then ["application/grpc"] else [])
  types.any fun t => (exclude.map mediaTypeOf).contains t

/-- Responses `GZipMiddleware` leaves alone. -/
def gzipPassThrough (exclude : List String) (r : Response) : Bool :=
  r.headers.contains "content-encoding" || r.status_code == 206 || gzipExcluded exclude r.headers ||
    !bodyAllowed r.status_code

/-- A body response (`body` in memory) through the responder. -/
def gzipWhole (minimum_size : Nat) (gzip : Bool) (r : Response) (hb : bodyAllowed r.status_code = true) : Response :=
  if r.body.size < minimum_size then r else
  let h := addVary r.headers "Accept-Encoding"
  if gzip then
    let z := Deflate.gzip r.body
    { r with body := z, h_body := .inl hb,
             headers := (h.set "content-encoding" "gzip").set "content-length" (toString z.size) }
  else { r with headers := h }

/-- A stream, compressed piece by piece. -/
def gzipStream (s : ContentStream) : ContentStream := fun send => do
  let st ← (IO.mkRef ((0 : UInt32), (0 : Nat)) : IO _)
  send Deflate.gzipHeader
  s fun piece => do
    (st.modify fun (c, n) => (Deflate.crc32Update c piece, n + piece.size) : IO Unit)
    send (Deflate.deflate piece false)
  let (c, n) ← (st.get : IO _)
  send (Deflate.deflate .empty true ++ Deflate.gzipTrailer c n)

/-- `FileResponse.chunk_size`: a file under it is one body message. -/
def fileChunk : Nat := 64 * 1024

/-- **The responder** on a response. -/
def gzipResponse (minimum_size : Nat) (exclude : List String) (gzip headOnly : Bool) (r : Response) : IO Response := do
  if gzipPassThrough exclude r then return r
  if hb : bodyAllowed r.status_code = true then
    match r.stream with
    | none => return gzipWhole minimum_size gzip r hb
    | some s =>
      if headOnly then return r
      let small := match (r.headers.get? "content-length").bind (·.toNat?) with
        | some n => decide (n < fileChunk)
        | none => false
      if small then
        let b ← r.readBody
        return gzipWhole minimum_size gzip { r with body := b, stream := none, h_body := .inl hb } hb
      let h := addVary r.headers "Accept-Encoding"
      if gzip then
        return { r with headers := (h.set "content-encoding" "gzip").delete "content-length",
                        stream := some (gzipStream s) }
      else return { r with headers := h }
  else return r

/-- Whether the request accepts gzip (`"gzip" in Accept-Encoding`). -/
def acceptsGzip (r : Request) : Bool :=
  let ae := (r.headers.get? "accept-encoding").getD ""
  (ae.splitOn "gzip").length > 1

/-- **`GZipMiddleware(app, minimum_size=500, compresslevel=9,
exclude_content_types=DEFAULT_EXCLUDED_CONTENT_TYPES)`**. -/
def GZipMiddleware (minimum_size : Nat := 500) (compresslevel : Nat := 9)
    (exclude_content_types : List String := gzipDefaultExcluded) : Middleware := fun app req => do
  let _ := compresslevel
  let resp ← app req
  liftM (gzipResponse minimum_size exclude_content_types (acceptsGzip req) (req.method == "HEAD") resp)

end LeanStarlette
