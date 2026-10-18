import LeanStarlette.RepoImpl.Range

/-!
# Proofs: Range headers

* `range_within`: every range the parser hands out lies inside the file.
* `range_parse_print`: a header printed from byte ranges (sorted, with gaps,
  inside the file) parses back to the same ranges.
-/

namespace LeanStarlette

/-! ## Splitting text -/

theorem splitFirst_go_append (sep : Char) : ∀ (a b acc : List Char), sep ∉ a →
    splitFirst.go sep acc (a ++ sep :: b) = (acc.reverse ++ a, some b)
  | [], b, acc, _ => by simp [splitFirst.go]
  | c :: a, b, acc, h => by
    have hc : c ≠ sep := fun e => h (by simp [e])
    have ha : sep ∉ a := fun e => h (by simp [e])
    simp only [List.cons_append, splitFirst.go, hc, ↓reduceIte]
    rw [splitFirst_go_append sep a b (c :: acc) ha]
    simp

theorem splitFirst_append (sep : Char) (a b : List Char) (h : sep ∉ a) :
    splitFirst sep (a ++ sep :: b) = (a, some b) := by
  simp [splitFirst, splitFirst_go_append sep a b [] h]

/-- `str.split(sep)`, structurally: the specification of `splitAll`. -/
def splitSpec (sep : Char) : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    if c = sep then [] :: splitSpec sep cs
    else match splitSpec sep cs with
      | [] => [[c]]
      | x :: xs => (c :: x) :: xs

theorem splitSpec_ne_nil (sep : Char) : ∀ s, splitSpec sep s ≠ []
  | [] => by simp [splitSpec]
  | c :: cs => by
    simp only [splitSpec]
    split
    · simp
    · split <;> simp

/-- The step `splitAll` folds with. -/
def splitStep (sep : Char) (st : List Char × List (List Char)) (c : Char) : List Char × List (List Char) :=
  if c = sep then ([], st.1.reverse :: st.2) else (c :: st.1, st.2)

theorem splitAll_fold (sep : Char) : ∀ (s cur : List Char) (acc : List (List Char)),
    let r := s.foldl (splitStep sep) (cur, acc)
    (r.1.reverse :: r.2).reverse =
      acc.reverse ++ ((cur.reverse ++ (splitSpec sep s).headD []) :: (splitSpec sep s).tail)
  | [], cur, acc => by simp [splitSpec]
  | c :: cs, cur, acc => by
    simp only [List.foldl_cons]
    rw [splitAll_fold sep cs]
    simp only [splitStep, splitSpec]
    have hne := splitSpec_ne_nil sep cs
    by_cases hc : c = sep
    · cases h : splitSpec sep cs with
      | nil => exact absurd h hne
      | cons x xs => simp [hc]
    · simp only [hc, ↓reduceIte, List.reverse_cons, List.append_assoc]
      have hne := splitSpec_ne_nil sep cs
      cases h : splitSpec sep cs with
      | nil => exact absurd h hne
      | cons x xs => simp

theorem splitAll_eq_spec (sep : Char) (s : List Char) : splitAll sep s = splitSpec sep s := by
  have := splitAll_fold sep s [] []
  simp only [List.reverse_nil, List.nil_append] at this
  simp only [splitAll]
  have hfold : s.foldl (fun (st : List Char × List (List Char)) c =>
      if c = sep then ([], st.1.reverse :: st.2) else (c :: st.1, st.2)) ([], []) =
      s.foldl (splitStep sep) ([], []) := rfl
  rw [hfold, this]
  have hne := splitSpec_ne_nil sep s
  cases h : splitSpec sep s with
  | nil => exact absurd h hne
  | cons x xs => simp

theorem splitSpec_noSep (sep : Char) : ∀ (a rest : List Char), sep ∉ a →
    splitSpec sep (a ++ rest) = (a ++ (splitSpec sep rest).headD []) :: (splitSpec sep rest).tail
  | [], rest, _ => by
    have hne := splitSpec_ne_nil sep rest
    cases h : splitSpec sep rest with
    | nil => exact absurd h hne
    | cons x xs => simp [h]
  | c :: a, rest, h => by
    have hc : c ≠ sep := fun e => h (by simp [e])
    have ha : sep ∉ a := fun e => h (by simp [e])
    simp only [List.cons_append, splitSpec, hc, ↓reduceIte]
    rw [splitSpec_noSep sep a rest ha]

/-- **Splitting what was joined**: `sep.join(parts).split(sep) == parts` when
no part contains `sep`. -/
theorem splitAll_intercalate (sep : Char) : ∀ (p : List Char) (ps : List (List Char)),
    (∀ q ∈ p :: ps, sep ∉ q) → splitAll sep ([sep].intercalate (p :: ps)) = p :: ps
  | p, [], h => by
    rw [splitAll_eq_spec]
    simp only [List.intercalate_singleton]
    have := splitSpec_noSep sep p [] (h p (by simp))
    simp only [List.append_nil] at this
    rw [this]; simp [splitSpec]
  | p, q :: ps, h => by
    rw [List.intercalate_cons_cons, splitAll_eq_spec, List.append_assoc,
      splitSpec_noSep sep p _ (h p (by simp))]
    have ih := splitAll_intercalate sep q ps (fun r hr => h r (by simp_all))
    rw [splitAll_eq_spec] at ih
    simp [splitSpec, ih]

/-! ## Numbers -/

theorem dropWhile_of_none {p : Char → Bool} : ∀ (s : List Char), (∀ c ∈ s, p c = false) → s.dropWhile p = s
  | [], _ => rfl
  | c :: cs, h => by simp [h c (by simp)]

theorem stripWs_of_none (s : List Char) (h : ∀ c ∈ s, isWs c = false) : stripWs s = s := by
  unfold stripWs
  rw [dropWhile_of_none s h, dropWhile_of_none s.reverse (by simpa using h), List.reverse_reverse]

theorem isWs_of_digit (c : Char) (h : c.isDigit = true) : isWs c = false := by
  simp only [isWs, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> intro e <;> subst e <;> exact absurd h (by decide)

theorem decimal_length_le : ∀ (n k : Nat), n < 10 ^ k → 1 ≤ k → (Keel.Codec.decimal n).length ≤ k
  | n, k, h, hk => by
    rw [Keel.Codec.decimal]
    split
    · simp; omega
    · rename_i hn
      cases k with
      | zero => omega
      | succ k =>
        cases k with
        | zero => simp at h; omega
        | succ k =>
          have hd : n / 10 < 10 ^ (k + 1) :=
            (Nat.div_lt_iff_lt_mul (by decide)).mpr (by rw [Nat.pow_succ] at h; exact h)
          have := decimal_length_le (n / 10) (k + 1) hd (by omega)
          simp only [List.length_append, List.length_singleton]; omega
termination_by n => n
decreasing_by omega

theorem pyInt_digits (l : List Char) (hne : l ≠ []) (hdig : ∀ c ∈ l, c.isDigit = true)
    (hlen : l.length ≤ maxIntDigits) : pyInt? l = some (Keel.Codec.digitsValue l : Int) := by
  have hfilter : l.filter Char.isDigit = l := List.filter_eq_self.mpr hdig
  have hnu : ∀ c ∈ l, c ≠ '_' := fun c hc e => by
    have := hdig c hc; subst e; contradiction
  match l, hne with
  | d :: ds, _ =>
    have hd0 : d.isDigit = true := hdig d (by simp)
    have hm : d ≠ '-' := fun e => by subst e; contradiction
    have hp : d ≠ '+' := fun e => by subst e; contradiction
    have hall : (d :: ds).all (fun c => c.isDigit || c = '_') = true := by
      simp only [List.all_eq_true]; intro c hc; simp [hdig c hc]
    have hhead : (d :: ds).head? ≠ some '_' := by simpa using hnu d (by simp)
    have hlast : (d :: ds).getLast? ≠ some '_' := by
      intro e
      exact hnu _ (List.mem_of_getLast? e) rfl
    have hzip : ((d :: ds).zip (d :: ds).tail).any (fun p => p.1 = '_' && p.2 = '_') = false := by
      simp only [List.any_eq_false, Bool.and_eq_true, decide_eq_true_eq, not_and]
      intro p hp h1
      exact absurd h1 (hnu p.1 (List.of_mem_zip hp).1)
    unfold pyInt?
    split
    rename_i _ neg ds' heq
    split at heq
    · rename_i r e; simp at e; exact absurd e.1 hm
    · rename_i r e; simp at e; exact absurd e.1 hp
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only [hall, hzip, List.isEmpty_cons, Bool.not_false, Bool.true_and, Bool.and_true, ↓reduceIte,
        hfilter, boundedDigits?, hlen, Option.map_some, Bool.false_eq_true, digitsValueChunked_eq]
      have h2 : ((d :: ds).getLast? != some '_') = true := bne_iff_ne.mpr hlast
      simp [h2, hnu d (by simp)]

theorem pyInt_decimal (n : Nat) (h : n < maxPrintable) : pyInt? (Keel.Codec.decimal n) = some (n : Int) := by
  rw [pyInt_digits _ (Keel.Codec.decimal_ne_nil n) (Keel.Codec.decimal_isDigit n)
    (decimal_length_le n maxIntDigits h (by decide)), Keel.Codec.digitsValue_decimal]

theorem dash_not_digit (n : Nat) : '-' ∉ Keel.Codec.decimal n := fun h =>
  absurd (Keel.Codec.decimal_isDigit n '-' h) (by decide)

theorem stripWs_decimal (n : Nat) : stripWs (Keel.Codec.decimal n) = Keel.Codec.decimal n :=
  stripWs_of_none _ fun c hc => isWs_of_digit c (Keel.Codec.decimal_isDigit n c hc)

/-- **One printed range parses back**: `start-last` reads as `[start, last + 1)`. -/
theorem parseRangePart_print (size : Nat) (r : Nat × Nat) (hr : r.1 < r.2 ∧ r.2 ≤ size)
    (hs : size ≤ maxPrintable) :
    parseRangePart size (rangePartChars r) = some ((r.1 : Int), (r.2 : Int)) := by
  have ha := pyInt_decimal r.1 (by omega)
  have hb := pyInt_decimal (r.2 - 1) (by omega)
  have hstrip : stripWs (rangePartChars r) = rangePartChars r := by
    apply stripWs_of_none
    intro c hc
    simp only [rangePartChars, List.mem_append, List.mem_cons] at hc
    rcases hc with hc | rfl | hc
    · exact isWs_of_digit c (Keel.Codec.decimal_isDigit _ c hc)
    · decide
    · exact isWs_of_digit c (Keel.Codec.decimal_isDigit _ c hc)
  have hne : (rangePartChars r).isEmpty = false := by simp [rangePartChars]
  have hnd : (rangePartChars r == ['-']) = false := by
    have := Keel.Codec.decimal_ne_nil r.1
    cases h : Keel.Codec.decimal r.1 with
    | nil => exact absurd h this
    | cons x xs =>
      have hx : x ≠ '-' := fun e => dash_not_digit r.1 (by rw [h, e]; simp)
      simp [rangePartChars, h, hx]
  have hsplit : splitFirst '-' (rangePartChars r) = (Keel.Codec.decimal r.1, some (Keel.Codec.decimal (r.2 - 1))) :=
    splitFirst_append '-' _ _ (dash_not_digit r.1)
  have hsne : (Keel.Codec.decimal r.1).isEmpty = false := by
    simpa using Keel.Codec.decimal_ne_nil r.1
  have hene : (Keel.Codec.decimal (r.2 - 1)).isEmpty = false := by
    simpa using Keel.Codec.decimal_ne_nil (r.2 - 1)
  unfold parseRangePart
  simp only [hstrip, hne, hnd, Bool.or_false, Bool.false_eq_true, ↓reduceIte, hsplit, stripWs_decimal,
    hsne, ha, hene, hb, Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and]
  have : ((r.2 - 1 : Nat) : Int) < (size : Int) := by omega
  simp only [this, ↓reduceIte]; omega

/-! ## Sorting and merging leave gapped ranges alone -/

theorem gapped_pairwise : ∀ (l : List (Nat × Nat)), Gapped l → (∀ r ∈ l, r.1 < r.2) →
    l.Pairwise (fun a b => a.2 < b.1)
  | [], _, _ => List.Pairwise.nil
  | [_], _, _ => by simp
  | a :: b :: rest, ⟨hab, hg⟩, hw => by
    have ih := gapped_pairwise (b :: rest) hg (fun r hr => hw r (by simp_all))
    refine List.Pairwise.cons ?_ ih
    intro c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact hab
    · have hb := hw b (by simp)
      have hbc := (List.pairwise_cons.mp ih).1 c hc
      omega

theorem mergeSort_gapped (l : List (Nat × Nat)) (hg : Gapped l) (hw : ∀ r ∈ l, r.1 < r.2) :
    l.mergeSort rangeLe = l := by
  apply List.mergeSort_of_pairwise
  apply (gapped_pairwise l hg hw).imp_of_mem
  intro a b ha _ h
  have := hw a ha
  simp [rangeLe]; omega

theorem mergeRanges_gapped : ∀ (l : List (Nat × Nat)), Gapped l → mergeRanges l = l
  | [], _ => by simp [mergeRanges]
  | [_], _ => by simp [mergeRanges]
  | a :: b :: rest, ⟨hab, hg⟩ => by
    have hn : ¬ (b.1 ≤ a.2) := by omega
    rw [mergeRanges]; simp only [hn, ↓reduceIte, mergeRanges_gapped (b :: rest) hg]

/-! ## The whole header -/

theorem filterMap_map_some {α β γ : Type} (f : β → Option γ) (g : α → β) (h : α → γ) :
    ∀ (l : List α), (∀ a ∈ l, f (g a) = some (h a)) → (l.map g).filterMap f = l.map h
  | [], _ => rfl
  | a :: l, hl => by
    simp only [List.map_cons, List.filterMap_cons, hl a (by simp)]
    rw [filterMap_map_some f g h l (fun x hx => hl x (by simp [hx]))]

/-- The ranges as `Int` pairs, as `parseRangePart` gives them. -/
def asInts (rs : List (Nat × Nat)) : List (Int × Int) := rs.map fun r => ((r.1 : Int), (r.2 : Int))

theorem checkRanges_valid (size : Nat) (rs : ByteRanges size) :
    ∃ rs', checkRanges size (asInts rs.ranges) = .ranges rs' ∧ rs'.ranges = rs.ranges := by
  have hns : (asInts rs.ranges).map (fun r => (r.1.toNat, r.2.toNat)) = rs.ranges := by
    simp [asInts, Function.comp_def]
  have hne : asInts rs.ranges ≠ [] := by simpa [asInts] using rs.h_nonempty
  have hin : (asInts rs.ranges).any (fun r => !(0 ≤ r.1 && r.1 < size)) = false := by
    simp only [asInts, List.any_map, List.any_eq_false, Function.comp_def]
    intro r hr; have := rs.h_within r hr; simp; omega
  have hlt : (asInts rs.ranges).any (fun r => r.1 ≥ r.2) = false := by
    simp only [asInts, List.any_map, List.any_eq_false, Function.comp_def]
    intro r hr; have := rs.h_within r hr; simp; omega
  unfold checkRanges
  simp only [hne, ↓reduceDIte, hin, hlt, Bool.false_eq_true, ↓reduceIte]
  split
  · split
    · split
      · exact ⟨_, rfl, hns⟩
      · rename_i h1
        refine ⟨_, rfl, ?_⟩
        simp only [hns]
        have hlen : rs.ranges.length > 1 := by
          have := rs.h_nonempty
          have h1' : rs.ranges.length ≠ 1 := by simpa [hns] using h1
          cases h : rs.ranges with
          | nil => exact absurd h this
          | cons x xs =>
            rw [h] at h1'
            cases xs with
            | nil => exact absurd rfl h1'
            | cons y ys => simp
        have hg := rs.h_gaps hlen
        rw [mergeSort_gapped _ hg (fun r hr => (rs.h_within r hr).1), mergeRanges_gapped _ hg]
    · rename_i hc; exact absurd (by simpa [hns] using rs.h_count) hc
  · rename_i hw; exact absurd (by rw [hns]; exact rs.h_within) hw

theorem comma_not_in_part (r : Nat × Nat) : ',' ∉ rangePartChars r := by
  simp only [rangePartChars, List.mem_append, List.mem_cons, not_or]
  refine ⟨fun h => absurd (Keel.Codec.decimal_isDigit _ _ h) (by decide), by decide,
    fun h => absurd (Keel.Codec.decimal_isDigit _ _ h) (by decide)⟩

/-- **`range_parse_print`**: a `Range` header printed from byte ranges (inside
the file, sorted with gaps between them, at most `max_ranges`) parses back to
the same ranges, for files below `10 ^ 4300` bytes. -/
theorem range_parse_print (size : Nat) (rs : ByteRanges size) (hs : size ≤ maxPrintable) :
    ∃ rs', parseRangeHeader (printRanges rs.ranges) size = .ranges rs' ∧ rs'.ranges = rs.ranges := by
  obtain ⟨p, ps, hp⟩ : ∃ p ps, rs.ranges.map rangePartChars = p :: ps := by
    cases h : rs.ranges with
    | nil => exact absurd h rs.h_nonempty
    | cons x xs => exact ⟨_, _, rfl⟩
  have hparts : splitAll ',' ([','].intercalate (rs.ranges.map rangePartChars)) =
      rs.ranges.map rangePartChars := by
    rw [hp]; apply splitAll_intercalate; rw [← hp]
    intro q hq; simp only [List.mem_map] at hq
    obtain ⟨r, _, rfl⟩ := hq; exact comma_not_in_part r
  have hfm : (rs.ranges.map rangePartChars).filterMap (parseRangePart size) = asInts rs.ranges :=
    filterMap_map_some _ _ _ _ fun r hr => parseRangePart_print size r (rs.h_within r hr) hs
  have hhead : (printRanges rs.ranges).toList =
      ['b', 'y', 't', 'e', 's'] ++ '=' :: [','].intercalate (rs.ranges.map rangePartChars) := by
    simp [printRanges]
  unfold parseRangeHeader
  rw [hhead, splitFirst_append '=' _ _ (by decide)]
  have hbytes : ((stripWs ['b', 'y', 't', 'e', 's']).map asciiLower != "bytes".toList) = false := by decide
  simp only [hbytes, Bool.false_eq_true, ↓reduceIte, hparts, List.length_map]
  have hgt : ¬ (rs.ranges.length > maxRanges) := by have := rs.h_count; omega
  simp only [hgt, ↓reduceIte, hfm]
  exact checkRanges_valid size rs

/-- **`range_within`**: every byte range the parser hands out lies inside
the file and is non-empty. -/
theorem range_within (h : String) (size : Nat) (rs : ByteRanges size)
    (_hp : parseRangeHeader h size = .ranges rs) : ∀ r ∈ rs.ranges, r.1 < r.2 ∧ r.2 ≤ size :=
  rs.h_within

end LeanStarlette
