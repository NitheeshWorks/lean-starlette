import LeanStarlette.Proofs.Forms

/-!
# APIs: forms

`Request.form` (in `RepoImpl/Upload.lean`) is what applications call, as in
Starlette: `let form ← request.form (max_files := 10)`, then
`form.get? "name"`, `form.getlist "files"`, and `UploadFile.read`/`seek`/
`close` on an upload. A body over a limit is `HTTPException(400)`
(`form_error_400`).

For a parse without the request, `parseForm` returns the decoded items
refined by the limits they meet (`form_limits_enforced`), and
`parseRawForm` the raw form refined by lean-multipart's own limits.
-/

namespace LeanStarlette

/-- A form body's decoded items, refined: at most `max_files` files and
`max_fields` text fields, decoded from a raw form within lean-multipart's
limits. -/
def parseForm (lim : LeanMultipart.FormLimits) (contentType : Option String) (body : ByteArray) :
    Except LeanMultipart.LimitError
      {items : List (String × FormItem) //
        FormItemsWithinLimits lim items ∧ ∃ r : RawForm, r.WithinLimits lim ∧ items = r.decode} :=
  (parseRawForm lim contentType body).map fun r =>
    ⟨r.val.decode, RawForm.decode_within r.property, r.val, r.property, rfl⟩

end LeanStarlette
