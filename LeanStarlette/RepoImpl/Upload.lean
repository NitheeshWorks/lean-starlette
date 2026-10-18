import LeanStarlette.RepoImpl.Forms
import LeanStarlette.RepoImpl.Exceptions

/-!
# RepoImpl: `UploadFile`, `FormData`, `request.form()` (effectful)

`UploadFile` holds the file's bytes in memory (lean-multipart parses the
whole part into a `ByteArray`), with a position and a closed flag in an
`IO.Ref`, so `read`, `seek`, `write` and `close` behave as on Starlette's
`SpooledTemporaryFile` while it stays in memory. The parse itself is the pure
`formItems`; `Request.form` only opens the files of an accepted form, so a
form rejected by a limit leaves no file behind (Starlette closes the files it
had opened, `_files_to_close_on_error`).
-/

namespace LeanStarlette

/-- The state of an open upload: its bytes, the position, the size
Starlette tracks (`None` stays `None`; `write` adds to it), and whether it is
closed. -/
structure UploadState where
  data : ByteArray
  pos : Nat := 0
  size : Option Nat := none
  closed : Bool := false

/-- `UploadFile(file, size=…, filename=…, headers=…)`. -/
structure UploadFile where
  filename : Option String := none
  headers : Headers := Headers.empty
  file : IO.Ref UploadState

namespace UploadFile

/-- `UploadFile(file=BytesIO(data), size=size, filename=…, headers=…)`, at
position 0. -/
def new (data : ByteArray) (filename : Option String := none) (headers : Headers := Headers.empty)
    (size : Option Nat := none) : IO UploadFile := do
  return { filename, headers, file := ← IO.mkRef { data, size } }

/-- `upload.size`. -/
def size (f : UploadFile) : IO (Option Nat) := return (← f.file.get).size

/-- `upload.content_type`: the part's `Content-Type` header. -/
def content_type (f : UploadFile) : Option String := f.headers.get? "content-type"
abbrev contentType := @content_type

private def closedError : IO.Error := IO.userError "ValueError: I/O operation on closed file."

/-- `await upload.read(size=-1)`: up to `size` bytes from the position (all of
them for a negative size), moving the position past them. -/
def read (f : UploadFile) (size : Int := -1) : IO ByteArray := do
  let s ← f.file.get
  if s.closed then throw closedError
  let start := min s.pos s.data.size
  let stop := if size < 0 then s.data.size else min s.data.size (start + size.toNat)
  f.file.set { s with pos := s.pos + (stop - start) }
  return s.data.extract start stop

/-- `await upload.seek(offset)`: move to an absolute position. -/
def seek (f : UploadFile) (offset : Nat) : IO Unit := do
  let s ← f.file.get
  if s.closed then throw closedError
  f.file.set { s with pos := offset }

/-- `await upload.write(data)`: write at the position, overwriting and
extending (a gap past the end is zero-filled), and move past it. -/
def write (f : UploadFile) (bytes : ByteArray) : IO Unit := do
  let s ← f.file.get
  if s.closed then throw closedError
  let pad := if s.pos > s.data.size then ByteArray.mk (Array.replicate (s.pos - s.data.size) 0) else .empty
  let base := s.data ++ pad
  let after := base.extract (s.pos + bytes.size) base.size
  f.file.set { s with data := base.extract 0 s.pos ++ bytes ++ after, pos := s.pos + bytes.size,
                      size := s.size.map (· + bytes.size) }

/-- `await upload.close()`. Closing twice is allowed. -/
def close (f : UploadFile) : IO Unit := f.file.modify fun s => { s with closed := true }

/-- Whether the upload is closed. -/
def isClosed (f : UploadFile) : IO Bool := return (← f.file.get).closed

/-- Python's `repr(str)`: single quotes unless the text has a single quote
and no double quote; backslashes, the quote and control characters escaped. -/
def pyStrRepr (s : String) : String :=
  let q := if s.contains '\'' && !s.contains '"' then '"' else '\''
  let esc (c : Char) : String :=
    if c == '\\' then "\\\\" else if c == q then "\\" ++ c.toString
    else if c == '\n' then "\\n" else if c == '\r' then "\\r" else if c == '\t' then "\\t"
    else if c.toNat < 32 || c.toNat == 127 then "\\x" ++ String.ofList (Nat.toDigits 16 c.toNat |> fun d => if d.length < 2 then '0' :: d else d)
    else c.toString
  q.toString ++ String.join (s.toList.map esc) ++ q.toString

/-- Starlette's `repr(Headers)`: `Headers({...})` as a dict when no name
repeats, else `Headers(raw=[...])`. -/
def headersRepr (h : Headers) : String :=
  let names := h.raw.map (·.1)
  if (dedupStrings names).length == names.length then
    "Headers({" ++ ", ".intercalate (h.raw.map fun (k, v) => pyStrRepr k ++ ": " ++ pyStrRepr v) ++ "})"
  else
    "Headers(raw=[" ++ ", ".intercalate (h.raw.map fun (k, v) => "(b" ++ pyStrRepr k ++ ", b" ++ pyStrRepr v ++ ")") ++ "])"

/-- `repr(upload)`: `UploadFile(filename='file', size=4, headers=Headers({}))`. -/
def repr (f : UploadFile) : IO String := do
  let fn := match f.filename with | some n => pyStrRepr n | none => "None"
  let sz := match ← f.size with | some n => toString n | none => "None"
  return s!"UploadFile(filename={fn}, size={sz}, headers={headersRepr f.headers})"

end UploadFile

/-- A form value: `str` or `UploadFile`. -/
inductive FormValue where
  | text (s : String)
  | file (f : UploadFile)

namespace FormValue

/-- The text of a text value. -/
def text? : FormValue → Option String
  | .text s => some s
  | .file _ => none

/-- The upload of a file value. -/
def file? : FormValue → Option UploadFile
  | .file f => some f
  | .text _ => none

def isFile (v : FormValue) : Bool := v.file?.isSome

end FormValue

/-- `FormData`: Starlette's immutable multi-dict of text and uploads. A key
looks up its last value; `getlist` gives every value; `multi_items` every
pair in order. -/
structure FormData where
  multiItems : List (String × FormValue) := []

namespace FormData

/-- `form.multi_items()`. -/
def multi_items (fd : FormData) : List (String × FormValue) := fd.multiItems

/-- `form[key]`, `form.get(key)`: the last value for the key. -/
def get? (fd : FormData) (key : String) : Option FormValue :=
  (fd.multiItems.reverse.find? (·.1 == key)).map (·.2)

/-- `form.getlist(key)`. -/
def getlist (fd : FormData) (key : String) : List FormValue :=
  (fd.multiItems.filter (·.1 == key)).map (·.2)

/-- `form.keys()`: each key once, in first-seen order. -/
def keys (fd : FormData) : List String := dedupStrings (fd.multiItems.map (·.1))

/-- `form.items()`: each key with its last value, in first-seen order. -/
def items (fd : FormData) : List (String × FormValue) :=
  fd.keys.filterMap fun k => (fd.get? k).map (k, ·)

/-- `form.values()`. -/
def values (fd : FormData) : List FormValue := fd.items.map (·.2)

/-- `key in form`. -/
def contains (fd : FormData) (key : String) : Bool := fd.multiItems.any (·.1 == key)

/-- `len(form)`: the number of distinct keys. -/
def length (fd : FormData) : Nat := fd.keys.length

instance : GetElem? FormData String FormValue (fun fd k => fd.contains k = true) where
  getElem fd k _ := (fd.get? k).getD (.text "")
  getElem? fd k := fd.get? k

/-- `await form.close()`: close every upload. -/
def close (fd : FormData) : IO Unit :=
  fd.multiItems.forM fun (_, v) => match v with
    | .file f => f.close
    | .text _ => pure ()

/-- Open the uploads of parsed items, in order. The size is the number of
bytes the parser wrote, as Starlette counts it. -/
def ofItems (items : List (String × FormItem)) : IO FormData := do
  let vs ← items.mapM fun (k, v) => match v with
    | .text s => pure (k, FormValue.text s)
    | .file u => do
      return (k, .file (← UploadFile.new u.data (filename := u.filename) (headers := u.headers)
        (size := some u.data.size)))
  return { multiItems := vs }

/-- `repr(form)`: `FormData([('a', '123'), ('b', UploadFile(...))])`. -/
def repr (fd : FormData) : IO String := do
  let parts ← fd.multiItems.mapM fun (k, v) => do
    let vr ← match v with
      | .text s => pure (UploadFile.pyStrRepr s)
      | .file f => f.repr
    return s!"({UploadFile.pyStrRepr k}, {vr})"
  return "FormData([" ++ ", ".intercalate parts ++ "])"

end FormData

/-- `await request.form(max_files=1000, max_fields=1000, max_part_size=1024*1024)`.
A body over a limit, or malformed multipart, is `HTTPException(400)` with
Starlette's message (what Starlette raises inside an application). -/
def Request.form (r : Request) (max_files : Nat := 1000) (max_fields : Nat := 1000)
    (max_part_size : Nat := 1024 * 1024) : AppM FormData :=
  match formItems { maxFiles := max_files, maxFields := max_fields, maxPartSize := max_part_size }
      (r.headers.get? "content-type") r.bodyBytes with
  | .error e => throw (HTTPException 400 (detail := some (formErrorMessage e)))
  | .ok items => FormData.ofItems items

end LeanStarlette
