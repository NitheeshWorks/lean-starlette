import LeanStarlette.RepoImpl.Text

/-!
# Proofs: the decimal codec

* `ofDigits_natDigits`: the decimal digit codec round-trips.
-/

namespace LeanStarlette

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

end LeanStarlette
