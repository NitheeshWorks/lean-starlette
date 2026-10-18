import LeanStarlette.APIs.Starlette

/-!
# Proofs: headers and responses

* `headers_get_ci`: header lookup is case-insensitive lookup in the fields
  as given; `get_ci` says two spellings of a name find the same field.
* `content_length_eq_body`: `Response` sets `content-length` to the size of
  the body it sends, unless the caller gave one or the status forbids a body.
* `no_body_204_304`: a 1xx, 204 or 304 response has an empty body (a field of
  `Response`; the theorem reads it off).
* `redirect_307`: `RedirectResponse` is a `307` with `location` set.
* `json_response_body`: `JSONResponse`'s body is JSON that parses back to
  the value: compact, and with no NaN (the type has none).
* `method_not_allowed_response`: the 405 the router raises renders with its
  `Allow` header.
-/

namespace LeanStarlette

/-! ## Headers -/

/-- **Case-insensitive headers.** Looking a name up in `Headers(...)` finds
the first field whose name equals it ignoring ASCII case. -/
theorem headers_get_ci (l : List (String × String)) (k : String) :
    (Headers.ofList l).get? k = (l.find? (fun p => lowerAscii p.1 == lowerAscii k)).map (·.2) := by
  simp only [Headers.ofList, Headers.get?, List.find?_map, Option.map_map]
  rfl

/-- Two spellings of a name that agree ignoring case find the same field. -/
theorem get_ci (h : Headers) {k k' : String} (e : lowerAscii k = lowerAscii k') :
    h.get? k = h.get? k' := by
  simp [Headers.get?, e]

theorem get?_append_none {h : Headers} {k : String} (hk : h.get? k = none) (k' v : String) :
    (h.append k' v).get? k = if lowerAscii k' == lowerAscii k then some v else none := by
  simp only [Headers.get?, Option.map_eq_none_iff] at hk
  simp only [Headers.get?, Headers.append, List.find?_append, hk, Option.none_or, List.find?_cons,
    List.find?_nil]
  split <;> simp_all

theorem get?_append_some {h : Headers} {k v : String} (hk : h.get? k = some v) (k' v' : String) :
    (h.append k' v').get? k = some v := by
  simp only [Headers.get?, Option.map_eq_some_iff] at hk
  obtain ⟨p, hp, rfl⟩ := hk
  simp [Headers.get?, Headers.append, List.find?_append, hp]

theorem contains_false {h : Headers} {k : String} (hk : h.contains k = false) : h.get? k = none := by
  simpa [Headers.contains] using hk

/-! ## Responses -/

/-- **`content-length` is the body's size.** For any content, status,
headers and media type: when the given headers have no `content-length` and
the status allows a body, the response's `content-length` is the size of the
body it sends. Every response function is `Response.make`, so this holds for
all of them. -/
theorem content_length_eq_body (c : Content) (s : Nat) (hs : List (String × String))
    (mt : Option String) (h : StatusCode.Valid s)
    (hcl : (Headers.ofList hs).contains "content-length" = false) (hb : bodyAllowed s = true) :
    (Response.make c s hs mt h).headers.get? "content-length" =
      some (toString (Response.make c s hs mt h).body.size) := by
  have h0 := contains_false hcl
  have h1 : ((Headers.ofList hs).append "content-length"
      (toString (allowedBody s c.bytes).size)).get? "content-length" =
      some (toString (allowedBody s c.bytes).size) := by
    rw [get?_append_none h0]; simp
  simp only [Response.make, initHeaders, hcl, hb, Bool.not_false, Bool.and_self, ↓reduceIte]
  cases mt with
  | none => exact h1
  | some m =>
    simp only
    split
    · exact h1
    · exact get?_append_some h1 _ _

/-- The body `Response` sends is the content, when the status allows one. -/
theorem body_eq_content (c : Content) (s : Nat) (hs : List (String × String)) (mt : Option String)
    (h : StatusCode.Valid s) (hb : bodyAllowed s = true) : (Response.make c s hs mt h).body = c.bytes := by
  simp [Response.make, allowedBody, hb]

/-- **No body for 1xx, 204 and 304.** -/
theorem no_body_204_304 (r : Response) (h : r.status_code < 200 ∨ r.status_code = 204 ∨ r.status_code = 304) :
    r.body.size = 0 := by
  rcases r.h_body with hb | hb
  · exfalso
    simp only [bodyAllowed, Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not,
      beq_eq_false_iff_ne, ne_eq] at hb
    omega
  · exact hb

theorem get?_set_self (h : Headers) (k v : String) : (h.set k v).get? k = some v := by
  unfold Headers.set
  dsimp only
  split
  · rename_i hany
    simp only [Headers.get?]
    have : ∀ l : List (String × String), l.any (fun p => p.1 == lowerAscii k) = true →
        (Headers.setAux (lowerAscii k) v l).find? (fun p => p.1 == lowerAscii k) = some (lowerAscii k, v) := by
      intro l hl
      induction l with
      | nil => simp at hl
      | cons q qs ih =>
        simp only [Headers.setAux]
        split
        · simp
        · rename_i hq
          simp only [List.any_cons, hq, Bool.false_or] at hl
          simp [hq, ih hl]
    simp [this _ hany]
  · rename_i hany
    have : h.get? k = none := by
      simp only [Headers.get?, Option.map_eq_none_iff, List.find?_eq_none]
      simp only [Bool.not_eq_true, List.any_eq_false, beq_iff_eq] at hany
      intro p hp; simpa using hany p hp
    rw [get?_append_none this]; simp

/-- **`RedirectResponse` is a 307 with `location`.** -/
theorem redirect_307 (url : String) :
    (RedirectResponse url).status_code = 307 ∧
      (RedirectResponse url).headers.get? "location" = some (quote url Responses.redirectSafe) :=
  ⟨rfl, get?_set_self _ _ _⟩

/-- **`JSONResponse`'s body is the value's JSON**: for a finite value (no
NaN or infinity, which upstream's `allow_nan=False` rejects) within
lean-json's integer and depth limits, and with no repeated object key (the
parser keeps the last, as a `dict` does), the body parses back to the value. -/
theorem json_response_body (j : LeanJson.Json) (hint : LeanJson.Spec.IntsFit j)
    (hkeys : LeanJson.Spec.KeysUnique j) (hd : j.height ≤ 200)
    (hfin : j.allFinite = true) :
    (LeanJson.from_json (JSONResponse j).body).map (·.val) = .ok j := by
  have : (JSONResponse j).body = (LeanJson.to_json j).val := by
    have hj : LeanJson.intoJson j = j := rfl
    simp only [JSONResponse, Responses.jsonRender, hj, hfin, ↓reduceIte, Response.make, allowedBody, bodyAllowed]
    rfl
  rw [this]
  exact LeanJson.from_json_to_json j none false hint hkeys hd

/-- **NaN and infinities are refused**, as `allow_nan=False` refuses them:
the response is a 500. -/
theorem json_response_nonfinite (j : LeanJson.Json) (hfin : j.allFinite = false) :
    (JSONResponse j).status_code = 500 := by
  have hj : LeanJson.intoJson j = j := rfl
  simp [JSONResponse, Responses.jsonRender, hj, hfin, Response.make]

/-- **The router's 405 renders with `Allow`.** -/
theorem method_not_allowed_response (allow : List String) :
    match methodNotAllowed allow with
    | .http s d hs h => (httpExceptionResponse s d hs h).status_code = 405 ∧
        (httpExceptionResponse s d hs h).headers.get? "allow" = some (", ".intercalate allow)
    | .custom .. => False := by
  simp only [methodNotAllowed, HTTPException, httpExceptionResponse]
  refine ⟨rfl, ?_⟩
  have h0 : (Headers.ofList [("Allow", ", ".intercalate allow)]).get? "allow" = some (", ".intercalate allow) := by
    have e : lowerAscii "Allow" = lowerAscii "allow" := by decide
    rw [headers_get_ci]; simp [e]
  simp only [Response.make, initHeaders]
  simp only [show (405 == 204 || 405 == 304) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  split
  · split
    · exact get?_append_some h0 _ _
    · exact get?_append_some (get?_append_some h0 _ _) _ _
  · split
    · exact h0
    · exact get?_append_some h0 _ _

end LeanStarlette
