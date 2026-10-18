import LeanStarlette.Specifications.Routing
import LeanStarlette.Proofs.Text

/-!
# Proofs: the five built-in convertors are lawful

These are the convertor `_ext` lemmas: each convertor's `render` is accepted
by its own recogniser and inverted by its `convert`, which is what the
routing round trip (`Proofs/Template.lean`) needs of it.
-/

namespace LeanStarlette

open LeanJson

theorem strConvertor_lawful : strConvertor.Lawful where
  allowed_of_accepts s h ch hch := by
    simp only [strConvertor, Bool.and_eq_true, List.all_eq_true] at h
    simpa [strConvertor] using h.2 ch hch
  accepts_render v s h := by
    cases v <;> simp only [strConvertor, reduceCtorEq] at h
    split at h
    · rename_i hc; cases h; simpa [strConvertor] using hc
    · cases h
  convert_render v s h := by
    cases v <;> simp only [strConvertor, reduceCtorEq] at h
    split at h
    · cases h; simp [strConvertor]
    · cases h
  render_convert s h := by
    simp only [strConvertor, Bool.and_eq_true] at h
    simpa [strConvertor, String.toList_ofList, List.all_eq_true] using h

theorem pathConvertor_lawful : pathConvertor.Lawful where
  allowed_of_accepts _ _ _ _ := rfl
  accepts_render _ _ _ := rfl
  convert_render v s h := by
    cases v <;> simp only [pathConvertor, reduceCtorEq, Option.some.injEq] at h
    subst h; simp [pathConvertor]
  render_convert _ _ := rfl

theorem intConvertor_lawful : intConvertor.Lawful where
  allowed_of_accepts s h ch hch := by
    simp only [intConvertor, Bool.and_eq_true, List.all_eq_true] at h
    exact h.2 ch hch
  accepts_render v s h := by
    cases v <;> simp only [intConvertor, reduceCtorEq, Option.some.injEq] at h
    subst h
    simp only [intConvertor, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true',
      List.isEmpty_eq_false_iff]
    exact ⟨natDigits_ne_nil _, natDigits_all _⟩
  convert_render v s h := by
    cases v <;> simp only [intConvertor, reduceCtorEq, Option.some.injEq] at h
    subst h; simp [intConvertor, ofDigits_natDigits]
  render_convert _ _ := rfl

/-! ## float -/

theorem splitFirst_of_not_mem {sep : Char} {a : List Char} (h : sep ∉ a) :
    splitFirst sep a = (a, none) := by
  induction a with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.mem_cons, not_or] at h
    simp [splitFirst, Ne.symm h.1, ih h.2]

theorem splitFirst_append {sep : Char} {a b : List Char} (h : sep ∉ a) :
    splitFirst sep (a ++ sep :: b) = (a, some b) := by
  induction a with
  | nil => simp [splitFirst]
  | cons c cs ih =>
    simp only [List.mem_cons, not_or] at h
    simp [splitFirst, Ne.symm h.1, ih h.2]

theorem splitFirst_none {sep : Char} {s a : List Char} (h : splitFirst sep s = (a, none)) : s = a := by
  induction s generalizing a with
  | nil => simp [splitFirst] at h; exact h.symm
  | cons c cs ih =>
    simp only [splitFirst] at h
    split at h
    · cases h
    · rcases hr : splitFirst sep cs with ⟨a', b'⟩
      rw [hr] at h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      rw [ih hr]

theorem splitFirst_some {sep : Char} {s a b : List Char} (h : splitFirst sep s = (a, some b)) :
    s = a ++ sep :: b := by
  induction s generalizing a with
  | nil => simp [splitFirst] at h
  | cons c cs ih =>
    simp only [splitFirst] at h
    split at h
    · rename_i hc; simp only [Prod.mk.injEq, Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; simp [hc]
    · rcases hr : splitFirst sep cs with ⟨a', b'⟩
      rw [hr] at h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      simp [ih hr]

theorem dot_not_digit {s : List Char} (h : ∀ c ∈ s, isDigitChar c = true) : '.' ∉ s :=
  fun hm => by have := h _ hm; simp [isDigitChar] at this

theorem normDec_shift {m : Nat} (hm : m % 10 ≠ 0) (k : Nat) (e : Int) :
    normDec (m * 10 ^ k) e = (m, e + k) := by
  induction k generalizing e with
  | zero =>
    rw [normDec]; simp only [Nat.pow_zero, Nat.mul_one]
    have : m ≠ 0 := by intro h; simp [h] at hm
    simp [this, hm]
  | succ k ih =>
    rw [normDec]
    have h0 : m * 10 ^ (k + 1) ≠ 0 := by
      have : m ≠ 0 := by intro h; simp [h] at hm
      exact Nat.mul_ne_zero this (Nat.ne_of_gt (Nat.pow_pos (by omega)))
    have h1 : m * 10 ^ (k + 1) % 10 = 0 := by
      rw [Nat.pow_succ, ← Nat.mul_assoc]; exact Nat.mul_mod_left _ _
    have h2 : m * 10 ^ (k + 1) / 10 = m * 10 ^ k := by
      rw [Nat.pow_succ, ← Nat.mul_assoc]; exact Nat.mul_div_cancel _ (by omega)
    simp only [h0, h1, h2, ↓reduceIte, ih]
    congr 1; omega

theorem mkDec_of_norm (d : Decimal) (hn : d.neg = false) (hk : d.exp = 0 ∨ d.mant % 10 ≠ 0)
    (m : Nat) (e : Int) (h : normDec m e = (d.mant, d.exp)) : mkDec m e = d := by
  obtain ⟨neg, mant, exp, hnorm⟩ := d
  simp only at hn h
  subst hn
  simp [mkDec, h]

theorem floatConvert_renderDec (d : Decimal) (hn : d.neg = false) :
    floatAccepts (renderDec d) = true ∧ floatConvert (renderDec d) = d := by
  obtain ⟨neg, m, e, hnorm⟩ := d
  simp only at hn; subst hn
  have hds := natDigits_all m
  cases e with
  | ofNat k =>
    simp only [renderDec]
    have hall : ∀ c ∈ natDigits m ++ List.replicate k '0', isDigitChar c = true := by
      intro c hc
      simp only [List.mem_append, List.mem_replicate] at hc
      rcases hc with hc | ⟨_, rfl⟩
      · exact hds c hc
      · rfl
    refine ⟨?_, ?_⟩
    · simp only [floatAccepts, splitFirst_of_not_mem (dot_not_digit hall), Bool.and_eq_true,
        Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true]
      exact ⟨by simp [natDigits_ne_nil], hall⟩
    · simp only [floatConvert, splitFirst_of_not_mem (dot_not_digit hall)]
      rw [ofDigits_append, ofDigits_natDigits]
      have hz : ofDigits (List.replicate k '0') = 0 := by
        have := ofDigits_replicate_zero k []; simpa [ofDigits] using this
      rw [hz, Nat.add_zero, List.length_replicate]
      rcases hnorm with ⟨rfl, hk⟩ | hm
      · simp at hk; subst hk; simp [mkDec, normDec]
      · simp only [mkDec, normDec_shift hm]; simp
  | negSucc k =>
    simp only [renderDec]
    have hm : m % 10 ≠ 0 := by rcases hnorm with ⟨_, h⟩ | h <;> simp_all
    generalize hpad : List.replicate (k + 2 - (natDigits m).length) '0' ++ natDigits m = pad
    have hlen : k + 2 ≤ pad.length := by
      rw [← hpad, List.length_append, List.length_replicate]; omega
    have hpadd : ∀ c ∈ pad, isDigitChar c = true := by
      intro c hc; rw [← hpad] at hc
      simp only [List.mem_append, List.mem_replicate] at hc
      rcases hc with ⟨_, rfl⟩ | hc
      · rfl
      · exact hds c hc
    have hip : ∀ c ∈ pad.take (pad.length - (k + 1)), isDigitChar c = true :=
      fun c hc => hpadd c (List.mem_of_mem_take hc)
    have hfp : ∀ c ∈ pad.drop (pad.length - (k + 1)), isDigitChar c = true :=
      fun c hc => hpadd c (List.mem_of_mem_drop hc)
    have hsplit := splitFirst_append (sep := '.') (b := pad.drop (pad.length - (k + 1)))
      (dot_not_digit hip)
    refine ⟨?_, ?_⟩
    · simp only [floatAccepts, hsplit, Bool.and_eq_true, Bool.not_eq_true',
        List.isEmpty_eq_false_iff, List.all_eq_true]
      refine ⟨⟨⟨?_, hip⟩, ?_⟩, hfp⟩
      · intro h; have := congrArg List.length h; simp at this; omega
      · intro h; have := congrArg List.length h; simp at this; omega
    · simp only [floatConvert, hsplit, List.take_append_drop, List.length_drop]
      rw [← hpad, ofDigits_replicate_zero, ofDigits_natDigits]
      have : -(((List.replicate (k + 2 - (natDigits m).length) '0' ++ natDigits m).length -
          ((List.replicate (k + 2 - (natDigits m).length) '0' ++ natDigits m).length - (k + 1)) : Nat) : Int)
          = Int.negSucc k := by
        rw [hpad]; omega
      rw [this]
      have h := normDec_shift hm 0 (Int.negSucc k)
      simp only [Nat.pow_zero, Nat.mul_one, Int.natCast_zero, Int.add_zero] at h
      simp [mkDec, h]

theorem floatConvertor_lawful : floatConvertor.Lawful where
  allowed_of_accepts s h ch hch := by
    simp only [floatConvertor] at h ⊢
    unfold floatAccepts at h
    split at h
    · rename_i ip hs
      simp only [Bool.and_eq_true, List.all_eq_true] at h
      rw [splitFirst_none hs] at hch; simp [h.2 ch hch]
    · rename_i ip fp hs
      simp only [Bool.and_eq_true, List.all_eq_true] at h
      rw [splitFirst_some hs] at hch
      simp only [List.mem_append, List.mem_cons] at hch
      rcases hch with hc | rfl | hc
      · simp [h.1.1.2 ch hc]
      · simp
      · simp [h.2 ch hc]
  accepts_render v s h := by
    cases v <;> simp only [floatConvertor, reduceCtorEq] at h
    rename_i d
    split at h
    · cases h
    · cases h; exact (floatConvert_renderDec d (Bool.eq_false_iff.mpr ‹_›)).1
  convert_render v s h := by
    cases v <;> simp only [floatConvertor, reduceCtorEq] at h
    rename_i d
    split at h
    · cases h
    · cases h; simp only [floatConvertor]; rw [(floatConvert_renderDec d (Bool.eq_false_iff.mpr ‹_›)).2]
  render_convert s _ := by
    simp [floatConvertor, floatConvert]; split <;> simp [mkDec]

/-! ## uuid -/

theorem char_le_iff (a b : Char) : a ≤ b ↔ a.toNat ≤ b.toNat := by
  simp only [Char.le_def, UInt32.le_iff_toNat_le]; rfl

theorem hex_ne_hyphen {c : Char} (h : isHexChar c = true) : c ≠ '-' := by
  rintro rfl; simp [isHexChar, isLowerHex, isDigitChar] at h

theorem isHexChar_of_lower {c : Char} (h : isLowerHex c = true) : isHexChar c = true := by
  simp [isHexChar, h]

theorem asciiLower_of_lowerHex {c : Char} (h : isLowerHex c = true) : asciiLower c = c := by
  unfold asciiLower
  simp only [isLowerHex, isDigitChar, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    char_le_iff] at h
  have : ¬ ('A' ≤ c ∧ c ≤ 'Z') := by
    simp only [char_le_iff]; intro ⟨h1, h2⟩
    rcases h with ⟨_, h3⟩ | ⟨h3, _⟩ <;> simp at * <;> omega
  rw [ite_eq_right (by simpa using this)]

theorem isLowerHex_asciiLower {c : Char} (h : isHexChar c = true) : isLowerHex (asciiLower c) = true := by
  unfold asciiLower
  by_cases hu : 'A' ≤ c ∧ c ≤ 'Z'
  · rw [ite_eq_left (by simpa using hu)]
    simp only [char_le_iff] at hu
    simp only [isHexChar, isLowerHex, isDigitChar, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq, char_le_iff] at h
    have hlt : c.toNat + 32 < 0xd800 := by simp at hu; omega
    simp only [isLowerHex, isDigitChar, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      char_le_iff, toNat_ofNat_lt hlt]
    simp at *; omega
  · rw [ite_eq_right (by simpa using hu)]
    simp only [isHexChar, isLowerHex, isDigitChar, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq, char_le_iff] at h hu ⊢
    simp at *; omega

theorem uuidGroups_sound : ∀ (gs : List Nat) (s : List Char), uuidGroups gs s = true →
    (∀ c ∈ s, isHexChar c = true ∨ c = '-') ∧ (s.filter (· ≠ '-')).length = gs.sum
  | [], s, h => by
    simp only [uuidGroups, List.isEmpty_iff] at h; subst h; simp
  | [g], s, h => by
    simp only [uuidGroups, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    refine ⟨fun c hc => .inl (h.2 c hc), ?_⟩
    rw [List.filter_eq_self.mpr (fun c hc => by simpa using hex_ne_hyphen (h.2 c hc))]; simp [h.1]
  | g :: g' :: gs, s, h => by
    simp only [uuidGroups, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨hlen, hhex⟩, hrest⟩ := h
    have hs : s = s.take g ++ s.drop g := (List.take_append_drop _ _).symm
    have htake : (s.take g).filter (· ≠ '-') = s.take g :=
      List.filter_eq_self.mpr (fun c hc => by simpa using hex_ne_hyphen (hhex c hc))
    split at hrest
    · rename_i r hr
      obtain ⟨ih1, ih2⟩ := uuidGroups_sound (g' :: gs) r hrest
      rw [hs, hr]
      refine ⟨?_, ?_⟩
      · intro c hc
        simp only [List.mem_append, List.mem_cons] at hc
        rcases hc with hc | rfl | hc
        · exact .inl (hhex c hc)
        · exact .inr rfl
        · exact ih1 c hc
      · rw [List.filter_append, htake]; simp at ih2 hlen ⊢; omega
    · rename_i r hr
      obtain ⟨ih1, ih2⟩ := uuidGroups_sound (g' :: gs) (s.drop g) hrest
      rw [hs]
      refine ⟨?_, ?_⟩
      · intro c hc
        simp only [List.mem_append] at hc
        rcases hc with hc | hc
        · exact .inl (hhex c hc)
        · exact ih1 c hc
      · rw [List.filter_append, htake]; simp at ih2 hlen ⊢; omega

theorem uuidGroups_hyphen {g g' : Nat} {gs : List Nat} {a r : List Char} (ha : a.length = g)
    (hh : ∀ c ∈ a, isHexChar c = true) :
    uuidGroups (g :: g' :: gs) (a ++ '-' :: r) = uuidGroups (g' :: gs) r := by
  subst ha
  simp [uuidGroups, List.take_left', List.drop_left', List.all_eq_true]
  exact fun _ => hh

theorem uuidHex_ok {s : List Char} (h : uuidGroups [8, 4, 4, 4, 12] s = true) :
    (uuidHex s).length = 32 ∧ ∀ c ∈ uuidHex s, isLowerHex c = true := by
  obtain ⟨h1, h2⟩ := uuidGroups_sound _ _ h
  refine ⟨by simp at h2; simpa [uuidHex] using h2, ?_⟩
  intro c hc
  simp only [uuidHex, List.mem_map, List.mem_filter] at hc
  obtain ⟨c', ⟨hc', hne⟩, rfl⟩ := hc
  rcases h1 c' hc' with hx | rfl
  · exact isLowerHex_asciiLower hx
  · simp at hne

theorem renderUUID_parts (u : UUID) :
    uuidGroups [8, 4, 4, 4, 12] (renderUUID u) = true ∧ uuidHex (renderUUID u) = u.hex := by
  obtain ⟨h, hl, hx⟩ := u
  have hex : ∀ c ∈ h, isHexChar c = true := fun c hc => isHexChar_of_lower (hx c hc)
  have hT : ∀ (n : Nat) (l : List Char), (∀ c ∈ l, isHexChar c = true) → ∀ c ∈ l.take n, isHexChar c = true :=
    fun _ _ hl c hc => hl c (List.mem_of_mem_take hc)
  have hD : ∀ (n : Nat), ∀ c ∈ h.drop n, isHexChar c = true :=
    fun _ c hc => hex c (List.mem_of_mem_drop hc)
  have hnoh : ∀ (l : List Char), (∀ c ∈ l, isHexChar c = true) → l.filter (· ≠ '-') = l :=
    fun l hl => List.filter_eq_self.mpr (fun c hc => by simpa using hex_ne_hyphen (hl c hc))
  refine ⟨?_, ?_⟩
  · unfold renderUUID
    simp only
    rw [uuidGroups_hyphen (by simp; omega) (hT _ _ hex), uuidGroups_hyphen (by simp; omega) (hT _ _ (hD _)),
      uuidGroups_hyphen (by simp; omega) (hT _ _ (hD _)), uuidGroups_hyphen (by simp; omega) (hT _ _ (hD _))]
    simp only [uuidGroups, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.length_drop]
    exact ⟨by omega, hD 20⟩
  · unfold uuidHex renderUUID
    simp only [List.filter_append, List.filter_cons, ne_eq, not_true_eq_false, decide_false,
      Bool.false_eq_true, ↓reduceIte]
    rw [hnoh _ (hT _ _ hex), hnoh _ (hT _ _ (hD _)), hnoh _ (hT _ _ (hD _)), hnoh _ (hT _ _ (hD _)),
      hnoh _ (hD _)]
    have e1 : (h.drop 16).take 4 ++ h.drop 20 = h.drop 16 := by
      conv => rhs; rw [← List.take_append_drop 4 (h.drop 16)]
      simp [List.drop_drop]
    have e2 : (h.drop 12).take 4 ++ h.drop 16 = h.drop 12 := by
      conv => rhs; rw [← List.take_append_drop 4 (h.drop 12)]
      simp [List.drop_drop]
    have e3 : (h.drop 8).take 4 ++ h.drop 12 = h.drop 8 := by
      conv => rhs; rw [← List.take_append_drop 4 (h.drop 8)]
      simp [List.drop_drop]
    rw [e1, e2, e3, List.take_append_drop]
    rw [List.map_congr_left (fun c hc => asciiLower_of_lowerHex (hx c hc)), List.map_id']

theorem uuidConvertor_lawful : uuidConvertor.Lawful where
  allowed_of_accepts s h ch hch := by
    simp only [uuidConvertor] at h ⊢
    rcases (uuidGroups_sound _ _ h).1 ch hch with hx | rfl
    · simp [hx]
    · simp
  accepts_render v s h := by
    cases v <;> simp only [uuidConvertor, reduceCtorEq, Option.some.injEq] at h
    subst h; exact (renderUUID_parts _).1
  convert_render v s h := by
    cases v <;> simp only [uuidConvertor, reduceCtorEq, Option.some.injEq] at h
    rename_i u
    subst h
    have hp := (renderUUID_parts u).2
    have hc : (uuidHex (renderUUID u)).length = 32 ∧ ∀ c ∈ uuidHex (renderUUID u), isLowerHex c = true := by
      rw [hp]; exact ⟨u.h_len, u.h_hex⟩
    simp only [uuidConvertor]
    rw [dite_eq_left hc]
    congr 1
    obtain ⟨hx, _, _⟩ := u
    simp only [UUID.mk.injEq]; exact hp
  render_convert s h := by
    simp only [uuidConvertor] at h ⊢
    rw [dite_eq_left (uuidHex_ok h)]; rfl

/-- The default `CONVERTOR_TYPES` are all lawful. -/
theorem defaultConvertors_lawful : ∀ c ∈ defaultConvertors, c.Lawful := by
  intro c hc
  simp only [defaultConvertors, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · exact strConvertor_lawful
  · exact pathConvertor_lawful
  · exact intConvertor_lawful
  · exact floatConvertor_lawful
  · exact uuidConvertor_lawful

end LeanStarlette
