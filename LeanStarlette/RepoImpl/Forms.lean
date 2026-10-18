import LeanStarlette.RepoImpl.Request
import LeanMultipart.APIs.Form
import LeanMultipart.RepoImpl.Options

/-!
# RepoImpl: forms (`starlette/formparsers.py`), the pure part

`request.form()` on a body already read: lean-multipart's Starlette parsers
(`API.Starlette.parseUrlencoded`, `API.Starlette.parseMultipartForm`) enforce
`max_fields`, `max_files` and `max_part_size` as the bytes arrive; this module
decodes their output as Starlette does and names each limit error with
Starlette's message. `UploadFile` and `FormData`, which hold file state, are in
`RepoImpl/Upload.lean`.

* Urlencoded names and values: `unquote_plus(raw.decode("latin-1"))`,
  lean-multipart's `unquotePlusLatin1`.
* Multipart names, filenames and text values: the request charset
  (`Content-Type; charset=…`, default UTF-8), falling back to latin-1 when the
  bytes do not decode or the charset is unknown (`_user_safe_decode`).
-/

namespace LeanStarlette

/-- Bytes as latin-1 text: each byte is the code point of the same value. -/
def latin1Decode (b : ByteArray) : String := String.ofList (b.toList.map fun x => Char.ofNat x.toNat)

/-- How a form's text is decoded: the request charset as `codecs.lookup`
resolves it. UTF-8 (any spelling Python accepts) decodes as UTF-8; latin-1
and ASCII decode byte for byte (an ASCII decode that fails falls back to
latin-1, which gives the same text); an unknown charset is latin-1. -/
inductive FormCharset where
  | utf8
  | latin1
  deriving DecidableEq, Repr

/-- `codecs.lookup(charset).name`, for the charsets this port decodes:
Python's spellings of UTF-8 are `.utf8`; everything else, including the
latin-1 and ASCII spellings and unknown names, is `.latin1`. -/
def FormCharset.lookup (name : String) : FormCharset :=
  let n := String.ofList ((name.toList.map asciiLower).filter fun c => c != '-' && c != '_' && c != ' ')
  if ["utf8", "u8", "utf", "cp65001", "utf8ucs2", "utf8ucs4"].contains n then .utf8 else .latin1

/-- `_user_safe_decode(src, codec)`. -/
def userSafeDecode (cs : FormCharset) (b : ByteArray) : String :=
  match cs with
  | .utf8 => (String.fromUTF8? b).getD (latin1Decode b)
  | .latin1 => latin1Decode b

/-- The message of Starlette's `MultiPartException` for each limit error. -/
def formErrorMessage : LeanMultipart.LimitError → String
  | .tooManyFields m => s!"Too many fields. Maximum number of fields is {m}."
  | .tooManyFiles m => s!"Too many files. Maximum number of files is {m}."
  | .fieldTooLarge m => s!"Field exceeded maximum size of {m / 1024}KB."
  | .partTooLarge m => s!"Part exceeded maximum size of {m / 1024}KB."
  | .missingName => "The Content-Disposition header field \"name\" must be provided."
  | .missingBoundary => "Missing boundary in multipart."
  | .invalidMultipart => "Invalid multipart data."

/-- An uploaded file as the parser hands it over: Starlette's
`UploadFile(file, size, filename, headers)` before it is opened. -/
structure UploadData where
  filename : Option String
  /-- The part's headers (names lower-cased, values latin-1). -/
  headers : Headers
  data : ByteArray

/-- A form value as parsed: text, or a file. -/
inductive FormItem where
  | text (s : String)
  | file (f : UploadData)

def FormItem.isFile : FormItem → Bool
  | .file _ => true
  | .text _ => false

/-- One urlencoded field, decoded as Starlette's `FormParser` does:
lean-multipart's `decodeField`, `unquote_plus(raw.decode("latin-1"))` on the
name and the value (`unquotePlusLatin1`, proved equal to its byte-machine
spec and compiled to it). -/
def urlencodedItem (f : LeanMultipart.QsField) : String × FormItem :=
  let (k, v) := LeanMultipart.API.Starlette.decodeField f
  (k, .text v)

/-- One multipart part, decoded as Starlette's `MultiPartParser` does. -/
def multipartItem (cs : FormCharset) (p : LeanMultipart.StarlettePart) : String × FormItem :=
  let name := userSafeDecode cs p.name
  match p.filename with
  | none => (name, .text (userSafeDecode cs p.data))
  | some fn =>
    (name, .file { filename := some (userSafeDecode cs fn),
                   headers := Headers.ofList (p.headers.map fun h => (latin1Decode h.1, latin1Decode h.2)),
                   data := p.data })

/-- The media type of a `Content-Type` value, lower-cased, and its
`charset` parameter (python-multipart's `parse_options_header`). -/
def formContentType (ct : Option String) : String × FormCharset :=
  let (ty, params) := LeanMultipart.parseOptionsHeader (ct.getD "").toUTF8
  (latin1Decode ty, ((params.get "charset").map (FormCharset.lookup ∘ latin1Decode)).getD .utf8)

/-- A form as lean-multipart's Starlette parsers return it, before
decoding: the raw urlencoded fields, the multipart parts with the request
charset, or nothing (another content type). -/
inductive RawForm where
  | urlencoded (fs : List LeanMultipart.QsField)
  | multipart (cs : FormCharset) (ps : List LeanMultipart.StarlettePart)
  | empty

namespace RawForm

/-- Starlette's limits on a raw form: lean-multipart's
`UrlencodedWithinLimits` / `MultipartWithinLimits`. -/
def WithinLimits (lim : LeanMultipart.FormLimits) : RawForm → Prop
  | .urlencoded fs => LeanMultipart.Spec.UrlencodedWithinLimits lim fs
  | .multipart _ ps => LeanMultipart.Spec.MultipartWithinLimits lim ps
  | .empty => True

/-- The form's items, decoded as Starlette does. -/
def decode : RawForm → List (String × FormItem)
  | .urlencoded fs => fs.map urlencodedItem
  | .multipart cs ps => ps.map (multipartItem cs)
  | .empty => []

end RawForm

/-- What a form body parses to, by its `Content-Type`: Starlette's
`MultiPartParser` for `multipart/form-data`, its `FormParser` for
`application/x-www-form-urlencoded`, an empty form otherwise. The first
limit error stops the parse. The refinement is lean-multipart's own. -/
def parseRawForm (lim : LeanMultipart.FormLimits) (contentType : Option String) (body : ByteArray) :
    Except LeanMultipart.LimitError {r : RawForm // r.WithinLimits lim} :=
  let (ty, cs) := formContentType contentType
  if ty == "multipart/form-data" then
    (LeanMultipart.API.Starlette.parseMultipartForm lim (contentType.getD "").toUTF8 body).map
      fun ps => ⟨.multipart cs ps.val, ps.property⟩
  else if ty == "application/x-www-form-urlencoded" then
    (LeanMultipart.API.Starlette.parseUrlencoded lim body).map fun fs => ⟨.urlencoded fs.val, fs.property⟩
  else .ok ⟨.empty, trivial⟩

/-- The decoded items of a form body (what `request.form()` builds its
`FormData` from). -/
def formItems (lim : LeanMultipart.FormLimits) (contentType : Option String) (body : ByteArray) :
    Except LeanMultipart.LimitError (List (String × FormItem)) :=
  (parseRawForm lim contentType body).map (·.val.decode)

/-- Starlette's counting limits on decoded items: at most `max_files` files
and at most `max_fields` text fields. -/
def FormItemsWithinLimits (lim : LeanMultipart.FormLimits) (items : List (String × FormItem)) : Prop :=
  (items.filter (·.2.isFile)).length ≤ lim.maxFiles ∧
    (items.filter (! ·.2.isFile)).length ≤ lim.maxFields

end LeanStarlette
