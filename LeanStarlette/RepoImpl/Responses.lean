import LeanStarlette.RepoImpl.Request
import LeanStarlette.RepoImpl.Background

/-!
# RepoImpl: responses

`starlette/responses.py`: `Response`, `PlainTextResponse`, `HTMLResponse`,
`JSONResponse` and `RedirectResponse`. In Python the last four are
subclasses; here there is one `Response` type and five functions that build
it, with Starlette's names and defaults.

`Response.make` is `Response.__init__`: it renders the content and runs
`init_headers`, which adds `content-length` (unless given, and unless the
status forbids a body) and `content-type` (with `; charset=utf-8` for
`text/*`). Unlike upstream it also drops the body when the status forbids one
(UP-028), so `Response.h_body` holds.
-/

namespace LeanStarlette

/-- Response content: text (encoded as UTF-8) or bytes. -/
structure Content where
  bytes : ByteArray

instance : Coe String Content := ⟨fun s => ⟨s.toUTF8⟩⟩
instance : Coe ByteArray Content := ⟨Content.mk⟩
instance : EmptyCollection Content := ⟨⟨.empty⟩⟩

/-- `media_type`, with `; charset=utf-8` appended to a `text/*` type that
has no charset. -/
def contentType (mt : String) : String :=
  if mt.startsWith "text/" && !((lowerAscii mt).splitOn "charset=").length > 1 then
    mt ++ "; charset=utf-8"
  else mt

/-- `Response.init_headers`. -/
def initHeaders (status : Nat) (body : ByteArray) (headers : List (String × String))
    (media_type : Option String) : Headers :=
  let h := Headers.ofList headers
  let h := if !h.contains "content-length" && bodyAllowed status then
      h.append "content-length" (toString body.size) else h
  match media_type with
  | some mt => if h.contains "content-type" then h else h.append "content-type" (contentType mt)
  | none => h

/-- The body a status allows: the content, or nothing for 1xx, 204, 304. -/
def allowedBody (status : Nat) (body : ByteArray) : ByteArray :=
  if bodyAllowed status then body else .empty

theorem allowedBody_ok (status : Nat) (body : ByteArray) :
    bodyAllowed status = true ∨ (allowedBody status body).size = 0 := by
  unfold allowedBody; split
  · exact .inl ‹_›
  · exact .inr rfl

/-- `Response(content, status_code, headers, media_type)`. -/
def Response.make (content : Content) (status_code : Nat) (headers : List (String × String))
    (media_type : Option String) (h : StatusCode.Valid status_code) (background : BackgroundTasks := {}) :
    Response :=
  let body := allowedBody status_code content.bytes
  { status_code, body, h_status := h, h_body := allowedBody_ok _ _, background
    headers := initHeaders status_code body headers media_type }

/-! ## Starlette's response classes, as functions -/
namespace Responses

/-- `Response(content=b"", status_code=200, headers=None, media_type=None)`. -/
def Response (content : Content := {}) (status_code : Nat := 200) (headers : List (String × String) := [])
    (media_type : Option String := none) (background : BackgroundTasks := {})
    (h : StatusCode.Valid status_code := by decide) : LeanStarlette.Response :=
  .make content status_code headers media_type h background

/-- `PlainTextResponse(content, ...)`: `text/plain; charset=utf-8`. -/
def PlainTextResponse (content : Content := {}) (status_code : Nat := 200)
    (headers : List (String × String) := []) (media_type : String := "text/plain")
    (background : BackgroundTasks := {}) (h : StatusCode.Valid status_code := by decide) :
    LeanStarlette.Response :=
  .make content status_code headers (some media_type) h background

/-- `HTMLResponse(content, ...)`: `text/html; charset=utf-8`. -/
def HTMLResponse (content : Content := {}) (status_code : Nat := 200)
    (headers : List (String × String) := []) (media_type : String := "text/html")
    (background : BackgroundTasks := {}) (h : StatusCode.Valid status_code := by decide) :
    LeanStarlette.Response :=
  .make content status_code headers (some media_type) h background

/-- The bytes `JSONResponse` sends for a value: `json.dumps(content,
ensure_ascii=False, allow_nan=False, indent=None, separators=(",", ":"))`.
lean-json's printer is compact and keeps non-ASCII text by default. -/
def jsonBody (j : LeanJson.Json) : ByteArray := (LeanJson.print j).val

/-- `JSONResponse.render`: the body, or the `ValueError` `json.dumps` raises
under `allow_nan=False` for NaN or an infinity. -/
def jsonRender (j : LeanJson.Json) : Except String ByteArray :=
  if j.allFinite then .ok (jsonBody j) else .error "Out of range float values are not JSON compliant"

/-- `JSONResponse(content, ...)`: `application/json`. A value with NaN or an
infinity cannot be rendered (upstream raises `ValueError` in the endpoint,
which `ServerErrorMiddleware` turns into a 500), so the response is that
`500 Internal Server Error`. -/
def JSONResponse {α : Type} [LeanJson.IntoJson α] (content : α) (status_code : Nat := 200)
    (headers : List (String × String) := []) (media_type : String := "application/json")
    (background : BackgroundTasks := {}) (h : StatusCode.Valid status_code := by decide) :
    LeanStarlette.Response :=
  match jsonRender (LeanJson.intoJson content) with
  | .ok body => .make body status_code headers (some media_type) h background
  | .error _ => .make "Internal Server Error" 500 [] (some "text/plain") (by decide)

/-- The characters `RedirectResponse` leaves unquoted in `location`. -/
def redirectSafe : List Char := ":/%#?=@[]!$&'()*+,;".toList

/-- `RedirectResponse(url, status_code=307, headers=None)`. -/
def RedirectResponse (url : String) (status_code : Nat := 307) (headers : List (String × String) := [])
    (background : BackgroundTasks := {}) (h : StatusCode.Valid status_code := by decide) :
    LeanStarlette.Response :=
  let r := LeanStarlette.Response.make {} status_code headers none h background
  { r with headers := r.headers.set "location" (quote url redirectSafe) }

/-- `StreamingResponse(content, status_code=200, headers=None,
media_type=None, background=None)`. The body is produced chunk by chunk as
it is sent; there is no `content-length` (upstream's `init_headers` has no
body to measure), so HTTP/1.1 sends it chunked. -/
def StreamingResponse (content : ContentStream) (status_code : Nat := 200)
    (headers : List (String × String) := []) (media_type : Option String := none)
    (background : BackgroundTasks := {}) (h : StatusCode.Valid status_code := by decide) :
    LeanStarlette.Response :=
  let hs := Headers.ofList headers
  let hs := match media_type with
    | some mt => if hs.contains "content-type" then hs else hs.append "content-type" (contentType mt)
    | none => hs
  { status_code, headers := hs, body := .empty, h_status := h, h_body := .inr rfl,
    stream := some content, background }

end Responses

export Responses (Response PlainTextResponse HTMLResponse JSONResponse RedirectResponse StreamingResponse)

namespace ContentStream

/-- A stream of the given chunks (an `Iterable[bytes]`). -/
def ofList (chunks : List ByteArray) : ContentStream := fun send => chunks.forM send

/-- A stream of text chunks, encoded as UTF-8 (upstream encodes `str`
chunks with the response charset). -/
def ofStrings (chunks : List String) : ContentStream := ofList (chunks.map String.toUTF8)

end ContentStream

/-! ## Accessors -/
namespace Response

/-- `response.media_type`'s header. -/
def contentTypeOf (r : LeanStarlette.Response) : Option String := r.headers.get? "content-type"

/-- `response.body` as text. -/
def text (r : LeanStarlette.Response) : String := String.fromUTF8? r.body |>.getD ""

/-- Replace a header (`response.headers[key] = value`). -/
def setHeader (r : LeanStarlette.Response) (key value : String) : LeanStarlette.Response :=
  { r with headers := r.headers.set key value }

end Response

end LeanStarlette
