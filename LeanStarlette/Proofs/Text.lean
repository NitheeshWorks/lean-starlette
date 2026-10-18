import LeanStarlette.RepoImpl.Text

/-!
# Proofs: the decimal codec and the greedy split order

* `ofDigits_natDigits`: the decimal digit codec round-trips.
* `splits_append`: the candidates for `a ++ b` begin with those that extend
  `a`, the last of which is `a` itself. This is the one lemma behind every
  greedy match in the router.
-/

namespace LeanStarlette

theorem toNat_ofNat_lt {n : Nat} (h : n < 0xd800) : (Char.ofNat n).toNat = n := by
  have hv : n.isValidChar := Or.inl h
  simp [Char.ofNat, hv, Char.ofNatAux, Char.toNat]

theorem digitVal_digitChar {d : Nat} (h : d < 10) : digitVal (digitChar d) = d := by
  unfold digitVal digitChar
  rw [toNat_ofNat_lt (by omega)]; omega

theorem isDigitChar_digitChar {d : Nat} (h : d < 10) : isDigitChar (digitChar d) = true := by
  have := toNat_ofNat_lt (n := 48 + d) (by omega)
  unfold isDigitChar digitChar
  simp only [Bool.and_eq_true, decide_eq_true_eq, Char.le_def]
  simp only [Char.toNat] at this
  constructor <;> (show _ ≤ _; simp only [UInt32.le_iff_toNat_le]; simp at *; omega)

theorem natDigits_eq (n : Nat) :
    natDigits n = if n < 10 then [digitChar n] else natDigits (n / 10) ++ [digitChar (n % 10)] := by
  rw [natDigits]

theorem ofDigits_append (a b : List Char) :
    ofDigits (a ++ b) = ofDigits a * 10 ^ b.length + ofDigits b := by
  unfold ofDigits
  rw [List.foldl_append]
  generalize List.foldl (fun a c => a * 10 + digitVal c) 0 a = x
  induction b generalizing x with
  | nil => simp
  | cons c cs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, ih (0 * 10 + digitVal c)]
    simp only [Nat.pow_succ, Nat.zero_mul, Nat.zero_add, Nat.add_mul, Nat.add_assoc]
    rw [Nat.mul_assoc, Nat.mul_comm 10 (10 ^ cs.length)]

theorem ofDigits_singleton (c : Char) : ofDigits [c] = digitVal c := by simp [ofDigits]

theorem ofDigits_natDigits (n : Nat) : ofDigits (natDigits n) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [natDigits_eq]
    split
    · rw [ofDigits_singleton, digitVal_digitChar (by assumption)]
    · rw [ofDigits_append, ih _ (by omega), ofDigits_singleton, digitVal_digitChar (by omega)]
      simp; omega

theorem natDigits_ne_nil (n : Nat) : natDigits n ≠ [] := by
  rw [natDigits_eq]; split <;> simp

theorem natDigits_all (n : Nat) : ∀ c ∈ natDigits n, isDigitChar c = true := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [natDigits_eq]
    split
    · intro c hc; simp at hc; subst hc; exact isDigitChar_digitChar (by assumption)
    · intro c hc
      simp only [List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | hc
      · exact ih _ (by omega) c hc
      · subst hc; exact isDigitChar_digitChar (by omega)

theorem ofDigits_replicate_zero (k : Nat) (b : List Char) :
    ofDigits (List.replicate k '0' ++ b) = ofDigits b := by
  rw [ofDigits_append]
  have : ofDigits (List.replicate k '0') = 0 := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [List.replicate_succ', ofDigits_append, ih]; simp [ofDigits, digitVal]
  simp [this]

/-! ## Splits -/

theorem mem_splits {s : List Char} {pq : List Char × List Char} (h : pq ∈ splits s) :
    pq.1 ++ pq.2 = s := by
  induction s generalizing pq with
  | nil => simp [splits] at h; subst h; rfl
  | cons c cs ih =>
    simp only [splits, List.mem_append, List.mem_map, List.mem_singleton] at h
    rcases h with ⟨pq', h', rfl⟩ | rfl
    · simp [ih h']
    · rfl

/-- The candidates for `b` end with the empty first part. -/
theorem splits_last (b : List Char) :
    ∃ M, splits b = M ++ [([], b)] ∧ ∀ pq ∈ M, pq.1 ≠ [] := by
  cases b with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons c cs =>
    refine ⟨_, rfl, ?_⟩
    intro pq hpq
    simp only [List.mem_map] at hpq
    obtain ⟨_, _, rfl⟩ := hpq
    simp

/-- The candidates for `a ++ b` start with every candidate for `b`, extended
by `a`. -/
theorem splits_append (a b : List Char) :
    ∃ L, splits (a ++ b) = (splits b).map (fun pq => (a ++ pq.1, pq.2)) ++ L := by
  induction a with
  | nil => exact ⟨[], by simp⟩
  | cons c a ih =>
    obtain ⟨L, hL⟩ := ih
    refine ⟨L.map (fun p => (c :: p.1, p.2)) ++ [([], c :: (a ++ b))], ?_⟩
    rw [List.cons_append, splits, hL]
    simp [List.map_append, List.map_map, Function.comp_def]

/-- A greedy search over the candidates for `a ++ b` returns the answer at
`(a, b)` when every longer candidate fails. -/
theorem findSome_splits_greedy {f : List Char × List Char → Option β} {a b : List Char} {x : β}
    (hlong : ∀ pq ∈ splits b, pq.1 ≠ [] → f (a ++ pq.1, pq.2) = none)
    (hat : f (a, b) = some x) :
    (splits (a ++ b)).findSome? f = some x := by
  obtain ⟨L, hL⟩ := splits_append a b
  obtain ⟨M, hM, hne⟩ := splits_last b
  rw [hL, hM]
  simp only [List.map_append, List.map_cons, List.map_nil, List.append_nil, List.findSome?_append,
    List.findSome?_cons, List.append_assoc]
  have : (M.map fun pq => (a ++ pq.1, pq.2)).findSome? f = none := by
    rw [List.findSome?_eq_none_iff]
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨pq, hpq, rfl⟩ := hx
    exact hlong pq (by rw [hM]; simp [hpq]) (hne pq hpq)
  simp [this, hat]

end LeanStarlette
