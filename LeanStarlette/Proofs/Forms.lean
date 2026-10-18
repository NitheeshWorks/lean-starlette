import LeanStarlette.RepoImpl.Upload

/-!
# Proofs: forms

`request.form()` is lean-multipart's Starlette parse, decoded: an accepted
form is the decoding of a raw form that meets lean-multipart's
`UrlencodedWithinLimits` / `MultipartWithinLimits` (the limits are
lean-multipart's theorems, carried by its refinements); the decoded items
then meet `max_files` and `max_fields`; and a rejected form is
`HTTPException(400)` with Starlette's message.
-/

namespace LeanStarlette

@[simp] theorem urlencodedItem_isFile (f : LeanMultipart.QsField) : (urlencodedItem f).2.isFile = false := rfl

@[simp] theorem multipartItem_isFile (cs : FormCharset) (p : LeanMultipart.StarlettePart) :
    (multipartItem cs p).2.isFile = p.isFile := by
  unfold multipartItem LeanMultipart.StarlettePart.isFile
  cases p.filename <;> rfl

private theorem filter_const_false {α} (l : List α) : l.filter (fun _ => false) = [] := by
  induction l <;> simp_all [List.filter]

private theorem filter_const_true {α} (l : List α) : l.filter (fun _ => true) = l := by
  induction l <;> simp_all [List.filter]

/-- A raw form within lean-multipart's limits decodes to items within
Starlette's counting limits. -/
theorem RawForm.decode_within {lim : LeanMultipart.FormLimits} :
    ∀ {r : RawForm}, r.WithinLimits lim → FormItemsWithinLimits lim r.decode
  | .urlencoded fs, h => by
    refine ⟨?_, ?_⟩
    · simp [RawForm.decode, List.filter_map, Function.comp_def, filter_const_false]
    · have := h.1; simpa [RawForm.decode, List.filter_map, Function.comp_def, filter_const_true] using this
  | .multipart cs ps, h => by
    obtain ⟨hf, ht, _⟩ := h
    refine ⟨?_, ?_⟩
    · simpa [RawForm.decode, List.filter_map, Function.comp_def] using hf
    · simpa [RawForm.decode, List.filter_map, Function.comp_def] using ht
  | .empty, _ => by simp [RawForm.decode, FormItemsWithinLimits]

/-- Form parse agrees with lean-multipart: accepted items are the decoding of
the raw form lean-multipart's parser returned, and that raw form is within
its limits. -/
theorem form_parse_agrees {lim : LeanMultipart.FormLimits} {ct : Option String} {body : ByteArray}
    {items : List (String × FormItem)} (h : formItems lim ct body = .ok items) :
    ∃ r : {r : RawForm // r.WithinLimits lim}, parseRawForm lim ct body = .ok r ∧ items = r.val.decode := by
  unfold formItems at h
  cases hp : parseRawForm lim ct body with
  | error e => simp [hp, Except.map] at h
  | ok r => simp [hp, Except.map] at h; exact ⟨r, rfl, h.symm⟩

/-- Limits enforced: accepted items have at most `max_files` files and
`max_fields` text fields, and the raw form meets lean-multipart's limits
(every text part within `max_part_size`). -/
theorem form_limits_enforced {lim : LeanMultipart.FormLimits} {ct : Option String} {body : ByteArray}
    {items : List (String × FormItem)} (h : formItems lim ct body = .ok items) :
    FormItemsWithinLimits lim items ∧ ∃ r : RawForm, r.WithinLimits lim ∧ items = r.decode := by
  obtain ⟨r, _, rfl⟩ := form_parse_agrees h
  exact ⟨RawForm.decode_within r.property, r.val, r.property, rfl⟩

/-- A form rejected by the parser is `HTTPException(400)` with Starlette's
message for the error. -/
theorem form_error_400 (r : Request) (max_files max_fields max_part_size : Nat)
    (e : LeanMultipart.LimitError)
    (h : formItems { maxFiles := max_files, maxFields := max_fields, maxPartSize := max_part_size }
      (r.headers.get? "content-type") r.bodyBytes = .error e) :
    r.form max_files max_fields max_part_size =
      throw (HTTPException 400 (detail := some (formErrorMessage e))) := by
  simp only [Request.form, h]

end LeanStarlette
