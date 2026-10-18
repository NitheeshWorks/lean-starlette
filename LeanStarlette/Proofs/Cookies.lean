import LeanStarlette.RepoImpl.Cookies
import LeanStarlette.Proofs.Range

/-!
# Proofs: cookies

* `cookie_parse_print`: the `Cookie` header a browser sends back for
  cookies set with `set_cookie` (names legal and distinct, any values)
  parses, by `cookie_parser`, to exactly those names and values.
  Underneath: `_unquote` undoes `_quote` for every string
  (`cookieUnquote_quote`).
* `set_cookie_receive` / `delete_cookie_receive`: after `set_cookie`, a
  browser holds the quoted value; after `delete_cookie`, it holds nothing
  under that name, whatever the response carried before.
-/

namespace LeanStarlette

/-! ## Whitespace: the table search finds only what the table holds -/

theorem inRanges_go_sound (t : Array (Nat × Nat)) (n : Nat) :
    ∀ fuel lo hi, PyRe.inRanges.go t n fuel lo hi = true → ∃ a b, (a, b) ∈ t.toList ∧ a ≤ n ∧ n ≤ b
  | 0, _, _ => by simp [PyRe.inRanges.go]
  | fuel + 1, lo, hi => by
    unfold PyRe.inRanges.go
    split
    · dsimp only
      split
      · rename_i a b hab
        split
        · exact inRanges_go_sound t n fuel _ _
        · split
          · exact inRanges_go_sound t n fuel _ _
          · intro _
            refine ⟨a, b, ?_, by omega, by omega⟩
            have := Array.mem_of_getElem? hab
            simpa using this
      · simp
    · simp

theorem isSpace_toNat {c : Char} (h : PyRe.isSpace c = true) : c.toNat ≤ 32 ∨ 133 ≤ c.toNat := by
  obtain ⟨a, b, hm, h1, h2⟩ := inRanges_go_sound _ _ _ _ _ h
  simp [PyRe.Unicode.space] at hm
  omega

theorem legal_range {c : Char} (h : isCookieLegal c = true) : 33 ≤ c.toNat ∧ c.toNat ≤ 126 := by
  unfold isCookieLegal at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, char_le_iff] at h
  have hall : ∀ x ∈ "!#$%&'*+-.^_`|~:".toList, 33 ≤ x.toNat ∧ x.toNat ≤ 126 := by decide
  rcases h with ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | h
  · simp at h1 h2; omega
  · simp at h1 h2; omega
  · simp at h1 h2; omega
  · exact hall c (List.elem_iff.mp h)

theorem legal_not_space {c : Char} (h : isCookieLegal c = true) : PyRe.isSpace c = false := by
  cases hs : PyRe.isSpace c
  · rfl
  · have := isSpace_toNat hs
    have := legal_range h
    omega

theorem quote_not_space : PyRe.isSpace '"' = false := by decide

theorem legal_ne {c : Char} (h : isCookieLegal c = true) : c ≠ ';' ∧ c ≠ '=' ∧ c ≠ '"' ∧ c ≠ '\\' := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> revert h <;> decide

/-! ## Stripping -/

theorem dropWhile_of_head {p : Char → Bool} : ∀ {s : List Char}, (∀ c ∈ s.head?, p c = false) → s.dropWhile p = s
  | [], _ => rfl
  | c :: s, h => by simp_all [List.dropWhile]

theorem pyStrip_of_ends {s : List Char} (h1 : ∀ c ∈ s.head?, PyRe.isSpace c = false)
    (h2 : ∀ c ∈ s.getLast?, PyRe.isSpace c = false) : pyStrip s = s := by
  unfold pyStrip
  rw [dropWhile_of_head h1, dropWhile_of_head (by simpa [List.head?_reverse] using h2), List.reverse_reverse]

theorem pyStrip_space_cons (s : List Char) : pyStrip (' ' :: s) = pyStrip s := by
  have : PyRe.isSpace ' ' = true := by decide
  simp [pyStrip, List.dropWhile, this]

/-! ## Quoting -/

theorem unquoteBody_cons {x : Char} (hx : x ≠ '\\') (r : List Char) : unquoteBody (x :: r) = x :: unquoteBody r := by
  rw [unquoteBody.eq_4 _ _ (fun _ _ h _ => hx h)]

theorem unquoteBody_esc_plain {a : Char} (ha : a = '"' ∨ a = '\\') (r : List Char) :
    unquoteBody ('\\' :: a :: r) = a :: unquoteBody r := by
  have hn : a ≠ '\n' := by rcases ha with rfl | rfl <;> decide
  rcases r with _ | ⟨b, _ | ⟨c, r⟩⟩
  · rw [unquoteBody.eq_3 _ _ (by intro _ _ _ _ h; simp at h)]; simp [hn]
  · rw [unquoteBody.eq_3 _ _ (by intro _ _ _ _ h; simp at h)]; simp [hn]
  · rw [unquoteBody.eq_2]
    have h0 : (decide ('0' ≤ a) && decide (a ≤ '3') && isOct b && isOct c) = false := by
      rcases ha with rfl | rfl <;> simp (config := { decide := true })
    simp [h0, hn]

theorem toNat_ofNat_valid {n : Nat} (h : n.isValidChar) : (Char.ofNat n).toNat = n := by
  have h' : n < UInt32.size := by
    unfold Nat.isValidChar at h; simp [UInt32.size]; omega
  simp [Char.ofNat, h, Char.ofNatAux, Char.toNat, UInt32.toNat_ofNatLT]

theorem digitChar_toNat {d : Nat} (h : d < 10) : (digitChar d).toNat = 48 + d := by
  simp only [digitChar]
  exact toNat_ofNat_valid (by unfold Nat.isValidChar; omega)

theorem unquoteBody_octal {c : Char} (hc : c.toNat < 256) (r : List Char) :
    unquoteBody ('\\' :: octal3 c.toNat ++ r) = c :: unquoteBody r := by
  have e1 := digitChar_toNat (d := c.toNat / 64 % 8) (by omega)
  have e2 := digitChar_toNat (d := c.toNat / 8 % 8) (by omega)
  have e3 := digitChar_toNat (d := c.toNat % 8) (by omega)
  simp only [octal3, List.cons_append, List.nil_append]
  rw [unquoteBody.eq_2]
  simp only [isOct, char_le_iff, e1, e2, e3, Bool.and_eq_true, decide_eq_true_eq]
  have hn : (48 + c.toNat / 64 % 8 - 48) * 64 + (48 + c.toNat / 8 % 8 - 48) * 8 + (48 + c.toNat % 8 - 48) = c.toNat := by
    omega
  have hcond : (('0'.toNat ≤ 48 + c.toNat / 64 % 8 ∧ 48 + c.toNat / 64 % 8 ≤ '3'.toNat) ∧
      ('0'.toNat ≤ 48 + c.toNat / 8 % 8 ∧ 48 + c.toNat / 8 % 8 ≤ '7'.toNat)) ∧
      ('0'.toNat ≤ 48 + c.toNat % 8 ∧ 48 + c.toNat % 8 ≤ '7'.toNat) := by
    simp; omega
  simp only [hcond, and_self, ite_true, hn, Char.ofNat_toNat]

theorem unquoteBody_escape (c : Char) (r : List Char) :
    unquoteBody (cookieEscape c ++ r) = c :: unquoteBody r := by
  unfold cookieEscape
  by_cases h1 : c = '"'
  · subst h1; simpa using unquoteBody_esc_plain (Or.inl rfl) r
  by_cases h2 : c = '\\'
  · subst h2; simpa using unquoteBody_esc_plain (Or.inr rfl) r
  simp only [h1, h2, ite_false]
  split
  · rename_i h3
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h3
    exact unquoteBody_octal h3.1 r
  · simpa using unquoteBody_cons h2 r

theorem unquoteBody_flatMap (v : List Char) : unquoteBody (v.flatMap cookieEscape) = v := by
  induction v with
  | nil => simp [unquoteBody]
  | cons c v ih => rw [List.flatMap_cons, unquoteBody_escape, ih]

/-- **`_unquote(_quote(v)) == v`** for every string. -/
theorem cookieUnquote_quote (v : List Char) : cookieUnquoteChars (cookieQuoteChars v) = v := by
  unfold cookieQuoteChars
  split
  · rename_i h
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    cases v with
    | nil => rfl
    | cons c v =>
      have hc : c ≠ '"' := (legal_ne (h.2 c (by simp))).2.2.1
      simp [cookieUnquoteChars, hc]
  · have : '"' :: (v.flatMap cookieEscape ++ ['"']) = '"' :: ((v.flatMap cookieEscape ++ ['"']) : List Char) := rfl
    cases hv : v.flatMap cookieEscape ++ ['"'] with
    | nil => simp at hv
    | cons t ts =>
      simp only [List.cons_append] at hv ⊢
      rw [show '"' :: (v.flatMap cookieEscape ++ ['"']) = '"' :: t :: ts by rw [hv]]
      simp only [cookieUnquoteChars]
      rw [← hv]
      simp [unquoteBody_flatMap]

theorem escape_no_semicolon (c : Char) : ';' ∉ cookieEscape c := by
  unfold cookieEscape
  split
  · simp
  split
  · simp
  split
  · rename_i h
    simp only [octal3, List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨by decide, ?_, ?_, ?_⟩ <;> intro e <;>
      · have := congrArg Char.toNat e
        rw [digitChar_toNat (by omega)] at this
        simp at this; omega
  · rename_i h3
    simp only [List.mem_singleton]
    rintro rfl
    simp [isCookieUnescaped, isCookieLegal] at h3

theorem quote_no_semicolon (v : List Char) : ';' ∉ cookieQuoteChars v := by
  unfold cookieQuoteChars
  split
  · rename_i h
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    intro hm
    exact (legal_ne (h.2 _ hm)).1 rfl
  · intro hm
    rw [List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_singleton] at hm
    rcases hm with (h | ⟨c, _, hc⟩) | h
    · exact absurd h (by decide)
    · exact escape_no_semicolon c hc
    · exact absurd h (by decide)

theorem quote_ends (v : List Char) :
    (∀ c ∈ (cookieQuoteChars v).head?, PyRe.isSpace c = false) ∧
    (∀ c ∈ (cookieQuoteChars v).getLast?, PyRe.isSpace c = false) := by
  unfold cookieQuoteChars
  split
  · rename_i h
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    refine ⟨fun c hc => legal_not_space (h.2 c (List.mem_of_mem_head? hc)),
      fun c hc => legal_not_space (h.2 c (List.mem_of_getLast? hc))⟩
  · refine ⟨by simp [quote_not_space], ?_⟩
    intro c hc
    rw [List.getLast?_concat] at hc
    simp only [Option.mem_def, Option.some.injEq] at hc
    subst hc; exact quote_not_space

/-! ## Splitting -/

theorem splitSpec_append (sep : Char) : ∀ (a b : List Char), sep ∉ a →
    splitSpec sep (a ++ sep :: b) = a :: splitSpec sep b
  | [], b, _ => by simp [splitSpec]
  | c :: a, b, h => by
    have hc : c ≠ sep := fun e => h (by simp [e])
    have ha : sep ∉ a := fun e => h (by simp [e])
    simp [splitSpec, hc, splitSpec_append sep a b ha]

theorem splitSpec_single (sep : Char) : ∀ (a : List Char), sep ∉ a → splitSpec sep a = [a]
  | [], _ => by simp [splitSpec]
  | c :: a, h => by
    have hc : c ≠ sep := fun e => h (by simp [e])
    have ha : sep ∉ a := fun e => h (by simp [e])
    simp [splitSpec, hc, splitSpec_single sep a ha]

/-! ## The parser on a printed header -/

/-- One printed pair. -/
def cookieEntry (p : String × String) : List Char := p.1.toList ++ '=' :: cookieQuoteChars p.2.toList

theorem cookieHeader_toList : ∀ (p : String × String) (rest : List (String × String)),
    (cookieHeader (p :: rest)).toList =
      cookieEntry p ++ (rest.flatMap fun q => ';' :: ' ' :: cookieEntry q)
  | (k, v), [] => by simp [cookieHeader, cookieEntry, cookieQuote]
  | (k, v), q :: rest => by
    rw [show cookieHeader ((k, v) :: q :: rest) = k ++ "=" ++ cookieQuote v ++ "; " ++ cookieHeader (q :: rest) from rfl]
    rw [String.toList_append, cookieHeader_toList q rest]
    simp [cookieEntry, cookieQuote]

theorem entry_no_semicolon {p : String × String} (hk : isCookieKey p.1 = true) : ';' ∉ cookieEntry p := by
  simp only [isCookieKey, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hk
  simp only [cookieEntry, List.mem_append, List.mem_cons, not_or]
  exact ⟨fun hm => (legal_ne (hk.1.2 _ hm)).1 rfl, by decide, quote_no_semicolon _⟩

theorem split_header (p : String × String) : ∀ (rest : List (String × String)),
    isCookieKey p.1 = true → (∀ q ∈ rest, isCookieKey q.1 = true) →
    splitSpec ';' (cookieEntry p ++ (rest.flatMap fun q => ';' :: ' ' :: cookieEntry q)) =
      cookieEntry p :: rest.map fun q => ' ' :: cookieEntry q
  | [], hp, _ => by simp [splitSpec_single _ _ (entry_no_semicolon hp)]
  | q :: rest, hp, hr => by
    simp only [List.flatMap_cons, List.cons_append, List.map_cons]
    rw [splitSpec_append _ _ _ (entry_no_semicolon hp)]
    have := split_header q rest (hr q (by simp)) (fun x hx => hr x (by simp [hx]))
    have hq : ';' ∉ ' ' :: cookieEntry q := by
      simp only [List.mem_cons, not_or]; exact ⟨by decide, entry_no_semicolon (hr q (by simp))⟩
    rw [show ' ' :: (cookieEntry q ++ List.flatMap (fun q => ';' :: ' ' :: cookieEntry q) rest) =
      (' ' :: cookieEntry q) ++ List.flatMap (fun q => ';' :: ' ' :: cookieEntry q) rest from rfl]
    congr 1
    have h2 := split_header q rest (hr q (by simp)) (fun x hx => hr x (by simp [hx]))
    -- the leading space stays on the piece
    induction rest generalizing q with
    | nil =>
      simp [splitSpec_single _ _ hq]
    | cons s rest' _ =>
      simp only [List.flatMap_cons, List.cons_append, List.map_cons] at h2 ⊢
      rw [show ' ' :: (cookieEntry q ++ ';' :: ' ' :: (cookieEntry s ++ List.flatMap (fun q => ';' :: ' ' :: cookieEntry q) rest')) =
        (' ' :: cookieEntry q) ++ ';' :: (' ' :: (cookieEntry s ++ List.flatMap (fun q => ';' :: ' ' :: cookieEntry q) rest')) from rfl]
      rw [splitSpec_append _ _ _ hq]
      rw [splitSpec_append _ _ _ (entry_no_semicolon (hr q (by simp)))] at h2
      simp only [List.cons.injEq] at h2
      rw [h2.2]

theorem chunk_entry (d : List (String × String)) (p : String × String) (hk : isCookieKey p.1 = true)
    (ws : List Char) (hws : ws = [] ∨ ws = [' ']) (hnew : ∀ q ∈ d, q.1 ≠ p.1) :
    cookieChunk d (ws ++ cookieEntry p) = d ++ [p] := by
  obtain ⟨k, v⟩ := p
  simp only [isCookieKey, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.isEmpty_eq_false_iff] at hk
  obtain ⟨⟨hne, hlegal⟩, _⟩ := hk
  have heq : '=' ∉ ws ++ k.toList := by
    rcases hws with rfl | rfl
    · exact fun hm => (legal_ne (hlegal _ hm)).2.1 rfl
    · simp only [List.cons_append, List.nil_append, List.mem_cons, not_or]
      exact ⟨by decide, fun hm => (legal_ne (hlegal _ hm)).2.1 rfl⟩
  have hkstrip : pyStrip k.toList = k.toList :=
    pyStrip_of_ends (fun c hc => legal_not_space (hlegal c (List.mem_of_mem_head? hc)))
      (fun c hc => legal_not_space (hlegal c (List.mem_of_getLast? hc)))
  have hwsstrip : pyStrip (ws ++ k.toList) = k.toList := by
    rcases hws with rfl | rfl
    · simpa using hkstrip
    · simpa [pyStrip_space_cons] using hkstrip
  obtain ⟨hq1, hq2⟩ := quote_ends v.toList
  unfold cookieChunk cookieChunkKV
  simp only [cookieEntry, ← List.append_assoc]
  rw [splitFirst_append _ _ _ heq]
  simp only [hwsstrip, pyStrip_of_ends hq1 hq2, cookieUnquote_quote, String.ofList_toList]
  have hkne : k.toList.isEmpty = false := by simpa using hne
  simp only [hkne, Bool.false_and, Bool.false_eq_true, ite_false, dictSet]
  have hany : d.any (·.1 == k) = false := by
    simp only [List.any_eq_false, beq_iff_eq]
    exact fun q hq => hnew q hq
  simp [hany]

theorem fold_entries : ∀ (d rest : List (String × String)), (∀ q ∈ rest, isCookieKey q.1 = true) →
    ((d ++ rest).map Prod.fst).Nodup →
    (rest.map fun q => ' ' :: cookieEntry q).foldl cookieChunk d = d ++ rest
  | d, [], _, _ => by simp
  | d, q :: rest, hr, hn => by
    simp only [List.map_cons, List.foldl_cons]
    have hnew : ∀ x ∈ d, x.1 ≠ q.1 := by
      intro x hx e
      simp only [List.map_append, List.map_cons, List.nodup_append, List.nodup_cons] at hn
      exact hn.2.2 x.1 (List.mem_map_of_mem hx) q.1 (by simp) e
    rw [show ' ' :: cookieEntry q = [' '] ++ cookieEntry q from rfl,
      chunk_entry d q (hr q (by simp)) _ (Or.inr rfl) hnew]
    rw [fold_entries (d ++ [q]) rest (fun x hx => hr x (by simp [hx])) (by simpa using hn)]
    simp

/-! ## The linear-time parser computes the specification -/

/-- A `CookieDict` represents a list `dict`: same entries, distinct names,
and the index gives each name's position. -/
structure CookieDict.Rep (d : CookieDict) (l : List (String × String)) : Prop where
  items : d.items.toList = l
  nodup : (l.map Prod.fst).Nodup
  some_ : ∀ k i, d.index[k]? = some i → ∃ h : i < l.length, l[i].1 = k
  none_ : ∀ k, d.index[k]? = none → ∀ p ∈ l, p.1 ≠ k

theorem set_eq_map (l : List (String × String)) (k v : String) (i : Nat) (hi : i < l.length)
    (hk : l[i].1 = k) (hn : (l.map Prod.fst).Nodup) :
    l.set i (k, v) = l.map (fun p => if p.1 == k then (p.1, v) else p) := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.getElem_set, List.getElem_map]
  by_cases hij : i = j
  · subst hij; simp [hk]
  · have hj : j < l.length := by simpa using h2
    have hne : l[j].1 ≠ k := by
      intro e
      exact hij (hn.eq_of_getElem_eq (by simpa using hi) (by simpa using hj) (by simp [hk, e]))
    simp [hij, hne]

theorem CookieDict.set_rep {d : CookieDict} {l : List (String × String)} (h : d.Rep l) (k v : String) :
    (d.set k v).Rep (dictSet l k v) := by
  unfold CookieDict.set dictSet
  cases hidx : d.index[k]? with
  | some i =>
    obtain ⟨hi, hk⟩ := h.some_ k i hidx
    have hany : l.any (·.1 == k) = true := List.any_eq_true.2 ⟨l[i], List.getElem_mem hi, by simp [hk]⟩
    simp only [hany, ite_true]
    have hmap : (l.map fun p => if p.1 == k then (p.1, v) else p).map Prod.fst = l.map Prod.fst := by
      simp only [List.map_map]; congr 1; funext p; simp only [Function.comp_apply]; split <;> rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [Array.set!, Array.toList_setIfInBounds, h.items, set_eq_map l k v i hi hk h.nodup]
    · rw [hmap]; exact h.nodup
    · intro k' j hj
      obtain ⟨hj', e⟩ := h.some_ k' j hj
      refine ⟨by simpa using hj', ?_⟩
      simp only [List.getElem_map]
      split <;> exact e
    · intro k' hn p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      have := h.none_ k' hn q hq
      split <;> exact this
  | none =>
    have hany : l.any (·.1 == k) = false := by
      simp only [List.any_eq_false, beq_iff_eq]; exact h.none_ k hidx
    simp only [hany, Bool.false_eq_true, ite_false]
    have hsz : d.items.size = l.length := by rw [← Array.length_toList, h.items]
    refine ⟨by simp [h.items], ?_, ?_, ?_⟩
    · simp only [List.map_append, List.map_cons, List.map_nil, List.nodup_append, List.nodup_cons,
        List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self, List.mem_cons, List.mem_map,
        true_and, h.nodup]
      intro a ha b hb e
      subst e
      obtain ⟨p, hp, rfl⟩ := ha
      exact h.none_ k hidx p hp (by simpa using hb)
    · intro k' j hj
      rw [Std.HashMap.getElem?_insert] at hj
      by_cases e : (k == k') = true
      · simp only [e, ite_true, Option.some.injEq] at hj
        subst hj
        have : k = k' := by simpa using e
        exact ⟨by simp [hsz], by simp [hsz, this]⟩
      · simp only [e, Bool.false_eq_true, ite_false] at hj
        obtain ⟨hj', e2⟩ := h.some_ k' j hj
        exact ⟨by simp; omega, by rw [List.getElem_append_left hj']; exact e2⟩
    · intro k' hn p hp
      rw [Std.HashMap.getElem?_insert] at hn
      by_cases e : (k == k') = true
      · simp [e] at hn
      · simp only [e, Bool.false_eq_true, ite_false] at hn
        rcases List.mem_append.1 hp with hp | hp
        · exact h.none_ k' hn p hp
        · simp only [List.mem_singleton] at hp
          subst hp
          simpa using e

theorem CookieDict.fold_rep : ∀ (cs : List (List Char)) (d : CookieDict) (l : List (String × String)),
    d.Rep l → (cs.foldl CookieDict.chunk d).Rep (cs.foldl cookieChunk l)
  | [], _, _, h => h
  | c :: cs, d, l, h => by
    simp only [List.foldl_cons]
    apply CookieDict.fold_rep cs
    unfold CookieDict.chunk cookieChunk
    cases cookieChunkKV c with
    | none => exact h
    | some kv => exact CookieDict.set_rep h kv.1 kv.2

/-- **The linear-time `cookieParser` is `cookieParserSpec`.** -/
theorem cookieParser_eq_spec (s : String) : cookieParser s = cookieParserSpec s :=
  (CookieDict.fold_rep _ {} [] ⟨rfl, List.nodup_nil, by simp, by simp⟩).items

/-- **`cookie_parser` reads back what a browser sends for cookies set with
`set_cookie`**: legal, distinct names and any values. -/
theorem cookie_parse_print (jar : List (String × String)) (hk : ∀ p ∈ jar, isCookieKey p.1 = true)
    (hd : (jar.map Prod.fst).Nodup) : cookieParser (cookieHeader jar) = jar := by
  rw [cookieParser_eq_spec]
  cases jar with
  | nil => simp [cookieParserSpec, cookieHeader, splitAll_eq_spec, splitSpec, cookieChunk, cookieChunkKV, splitFirst, splitFirst.go, pyStrip]
  | cons p rest =>
    unfold cookieParserSpec
    rw [splitAll_eq_spec, cookieHeader_toList, split_header p rest (hk p (by simp)) (fun q hq => hk q (by simp [hq]))]
    simp only [List.foldl_cons]
    rw [show cookieEntry p = [] ++ cookieEntry p from rfl, chunk_entry [] p (hk p (by simp)) [] (Or.inl rfl) (by simp)]
    simp only [List.nil_append]
    rw [fold_entries [p] rest (fun q hq => hk q (by simp [hq])) (by simpa using hd)]
    simp

/-! ## What a browser keeps -/

theorem lookup_filter_self (k : String) : ∀ (J : CookieJar), (J.filter (·.1 != k)).lookup k = none
  | [] => rfl
  | (a, b) :: J => by
    by_cases h : a = k
    · subst h; simp [lookup_filter_self a J]
    · have : (k == a) = false := by simp [Ne.symm h]
      have hne : (a != k) = true := by simp [h]
      simp [List.filter, hne, List.lookup, this, lookup_filter_self k J]

theorem lookup_filter_append (k x : String) : ∀ (J : CookieJar), (J.filter (·.1 != k) ++ [(k, x)]).lookup k = some x
  | [] => by simp
  | (a, b) :: J => by
    by_cases h : a = k
    · subst h; simp [lookup_filter_append a x J]
    · have : (k == a) = false := by simp [Ne.symm h]
      have hne : (a != k) = true := by simp [h]
      simp [List.filter, hne, List.lookup, this, lookup_filter_append k x J]

/-- Receiving a line `k=q; R` (a name `set_cookie` accepts, a quoted value). -/
theorem receive_line (J : CookieJar) (k v : String) (hk : isCookieKey k = true) (R : List Char) (line : String)
    (hline : line.toList = k.toList ++ '=' :: cookieQuoteChars v.toList ++ ';' :: R) :
    J.receive line = if (splitSpec ';' R).any maxAgeExpired then J.filter (·.1 != k)
      else J.filter (·.1 != k) ++ [(k, cookieQuote v)] := by
  have hent := entry_no_semicolon (p := (k, v)) hk
  simp only [isCookieKey, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hk
  have heq : '=' ∉ k.toList := fun hm => (legal_ne (hk.1.2 _ hm)).2.1 rfl
  have hkstrip : pyStrip k.toList = k.toList :=
    pyStrip_of_ends (fun c hc => legal_not_space (hk.1.2 c (List.mem_of_mem_head? hc)))
      (fun c hc => legal_not_space (hk.1.2 c (List.mem_of_getLast? hc)))
  obtain ⟨hq1, hq2⟩ := quote_ends v.toList
  unfold CookieJar.receive
  rw [splitAll_eq_spec, hline,
    show k.toList ++ '=' :: cookieQuoteChars v.toList ++ ';' :: R = cookieEntry (k, v) ++ ';' :: R by
      simp [cookieEntry],
    splitSpec_append _ _ _ hent]
  simp only [cookieEntry]
  rw [splitFirst_append _ _ _ heq]
  simp only [hkstrip, pyStrip_of_ends hq1 hq2, String.ofList_toList, cookieQuote]

theorem setCookieLine_toList (k v : String) :
    (setCookieLine k v none none (some "/") none false false (some .lax) false).toList =
      k.toList ++ '=' :: cookieQuoteChars v.toList ++ ';' :: " Path=/; SameSite=lax".toList := by
  simp [setCookieLine, String.intercalate_cons_cons, String.intercalate_singleton, SameSite.str, cookieQuote]

theorem deleteCookieLine_toList (k : String) :
    (setCookieLine k "" (some 0) (some (.date 0)) (some "/") none false false (some .lax) false).toList =
      k.toList ++ '=' :: cookieQuoteChars "".toList ++ ';' ::
        " expires=Thu, 01 Jan 1970 00:00:00 GMT; Max-Age=0; Path=/; SameSite=lax".toList := by
  have hd : formatHttpDate 0 = "Thu, 01 Jan 1970 00:00:00 GMT" := by decide
  have h0 : Int.repr 0 = "0" := by decide
  simp [setCookieLine, String.intercalate_cons_cons, String.intercalate_singleton, SameSite.str, cookieQuote, hd, h0]

theorem receiveAll_append (J : CookieJar) (r : Response) (line : String) :
    J.receiveAll { r with headers := r.headers.append "set-cookie" line } = (J.receiveAll r).receive line := by
  have : lowerAscii "set-cookie" = "set-cookie" := by decide
  simp [CookieJar.receiveAll, Headers.append, this, List.filter_append, List.foldl_append]

/-- **After `set_cookie(key, value)` a browser holds the (quoted) value
under the name; after `delete_cookie(key)` it holds nothing under it**,
whatever cookies it had and whatever the response set before. -/
theorem set_cookie_receive (r : Response) (J : CookieJar) (k v : String) (hk : isCookieKey k = true) :
    (CookieJar.receiveAll J (r.set_cookie k v (_h := hk))).lookup k = some (cookieQuote v) := by
  have hR : (splitSpec ';' " Path=/; SameSite=lax".toList).any maxAgeExpired = false := by decide
  simp only [Response.set_cookie]
  rw [receiveAll_append, receive_line _ k v hk _ _ (setCookieLine_toList k v), hR]
  simp [lookup_filter_append]

theorem delete_cookie_receive (r : Response) (J : CookieJar) (k : String) (hk : isCookieKey k = true) :
    (CookieJar.receiveAll J (r.delete_cookie k (h := hk))).lookup k = none := by
  have hR : (splitSpec ';' " expires=Thu, 01 Jan 1970 00:00:00 GMT; Max-Age=0; Path=/; SameSite=lax".toList).any
      maxAgeExpired = true := by decide
  simp only [Response.delete_cookie, Response.set_cookie]
  rw [receiveAll_append, receive_line _ k "" hk _ _ (deleteCookieLine_toList k), hR]
  simp [lookup_filter_self]

end LeanStarlette
