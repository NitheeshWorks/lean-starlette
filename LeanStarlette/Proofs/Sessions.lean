import LeanStarlette.RepoImpl.Sessions

/-!
# Proofs: sessions

`session_sign_verify`: the cookie `SessionMiddleware` sets at time `ts`
loads back, at any `now` that `max_age` allows, as the same session. It
composes itsdangerous's `TimestampSigner.unsign_sign`, base64's
`decodeList_encodeList` and LeanJson's printed round trip (`Printed`), for
every session JSON can carry back: integers within Python's 4300 digits,
no repeated key, nested at most 200 deep.
-/

namespace LeanStarlette

open LeanJson LeanItsdangerous

theorem digit_lt (d : Nat) (h : d < 64) : (LeanHttpx.Base64.digit d).toNat < 128 := by
  have : ∀ d : Fin 64, (LeanHttpx.Base64.digit d.val).toNat < 128 := by decide
  exact this ⟨d, h⟩

theorem encodeList_ascii : ∀ (l : List UInt8), ∀ c ∈ LeanHttpx.Base64.encodeList l, c.toNat < 128
  | a :: b :: c :: r => by
    intro x hx
    simp only [LeanHttpx.Base64.encodeList, LeanHttpx.Base64.encodeGroup, List.cons_append, List.nil_append,
      List.mem_cons] at hx
    have ha := a.toNat_lt; have hb := b.toNat_lt; have hc := c.toNat_lt
    rcases hx with rfl | rfl | rfl | rfl | hx
    · exact digit_lt _ (by omega)
    · exact digit_lt _ (by omega)
    · exact digit_lt _ (by omega)
    · exact digit_lt _ (by omega)
    · exact encodeList_ascii r x hx
  | [a, b] => by
    intro x hx
    simp only [LeanHttpx.Base64.encodeList, List.mem_cons, List.not_mem_nil, or_false] at hx
    have ha := a.toNat_lt; have hb := b.toNat_lt
    rcases hx with rfl | rfl | rfl | rfl
    · exact digit_lt _ (by omega)
    · exact digit_lt _ (by omega)
    · exact digit_lt _ (by omega)
    · decide
  | [a] => by
    intro x hx
    simp only [LeanHttpx.Base64.encodeList, List.mem_cons, List.not_mem_nil, or_false] at hx
    have ha := a.toNat_lt
    rcases hx with rfl | rfl | rfl | rfl
    · exact digit_lt _ (by omega)
    · exact digit_lt _ (by omega)
    · decide
    · decide
  | [] => by simp [LeanHttpx.Base64.encodeList]

theorem latin1_char {c : Char} (h : c.toNat < 256) : Char.ofNat c.toNat.toUInt8.toNat = c := by
  have : c.toNat.toUInt8.toNat = c.toNat := by
    simp [Nat.toUInt8]; omega
  rw [this, Char.ofNat_toNat]

theorem latin1Chars_bytes {s : List Char} (h : ∀ c ∈ s, c.toNat < 256) :
    latin1Chars (s.map (·.toNat.toUInt8)) = s := by
  induction s with
  | nil => rfl
  | cons c s ih =>
    simp only [latin1Chars, List.map_cons, List.map_map] at ih ⊢
    rw [latin1_char (h c (by simp))]
    simp only [List.cons.injEq, true_and]
    exact ih (fun x hx => h x (by simp [hx]))

theorem latin1Bytes_chars (b : Bytes) : latin1Bytes? (latin1Chars b) = some b := by
  have hlt : ∀ x : UInt8, (Char.ofNat x.toNat).toNat = x.toNat := by
    intro x
    have hv : x.toNat.isValidChar := by unfold Nat.isValidChar; have := x.toNat_lt; omega
    simp [Char.ofNat, hv, Char.ofNatAux, Char.toNat]
  unfold latin1Bytes? latin1Chars
  have hall : (b.map fun x => Char.ofNat x.toNat).all (·.toNat < 256) = true := by
    simp only [List.all_eq_true, List.mem_map, decide_eq_true_eq]
    rintro c ⟨x, _, rfl⟩
    rw [hlt]; exact x.toNat_lt
  simp only [hall, ite_true, List.map_map, Option.some.injEq]
  conv => rhs; rw [← List.map_id b]
  apply List.map_congr_left
  intro x _
  simp [hlt]

/-- **A session cookie loads back as the session it was made from**,
within `max_age`. -/
theorem session_sign_verify (t : TimestampSigner) (d : Array (String × Json)) {maxAge : Option Nat}
    {now ts : UInt64} (hage : TimestampSigner.AgeOk maxAge now ts) (hints : Spec.IntsFit (.obj d))
    (hkeys : Spec.KeysUnique (.obj d)) (hh : (Json.obj d).height ≤ 200) :
    decodeSession t maxAge now (encodeSession t d ts) = .loaded d := by
  unfold decodeSession encodeSession
  rw [String.toList_ofList, latin1Bytes_chars]
  simp only
  rw [TimestampSigner.unsign_sign t hage]
  simp only
  rw [latin1Chars_bytes (fun c hc => by have := encodeList_ascii _ c hc; omega)]
  rw [sessionPayload, LeanHttpx.Base64.decodeList_encodeList]
  simp only
  have hp := (LeanJson.print (.obj d) sessionPrintOpts).property
  have hb : (⟨(LeanJson.print (.obj d) sessionPrintOpts).val.data.toList.toArray⟩ : ByteArray) =
      (LeanJson.print (.obj d) sessionPrintOpts).val := by simp
  rw [hb, hp.roundTripDefault (Or.inl rfl) hints hkeys hh]

end LeanStarlette
