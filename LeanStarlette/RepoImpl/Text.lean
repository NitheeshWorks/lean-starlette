import LeanStarlette.DataTypes.Chars
import Std.Data.HashSet
import Keel.RepoImpl.CodecBasic

/-!
# RepoImpl: text primitives

Decimal digits, splitting on a separator, and small list helpers. All structural or well-founded on a size that shrinks.
-/

namespace LeanStarlette

/-! ## Characters -/

theorem char_le_iff (a b : Char) : a ≤ b ↔ a.toNat ≤ b.toNat := by
  simp only [Char.le_def, UInt32.le_iff_toNat_le]; rfl
theorem toNat_ofNat_lt {n : Nat} (h : n < 0xd800) : (Char.ofNat n).toNat = n := by
  have hv : n.isValidChar := Or.inl h
  simp [Char.ofNat, hv, Char.ofNatAux, Char.toNat]
theorem asciiLower_of_not_upper {d : Char} (h : ¬('A' ≤ d ∧ d ≤ 'Z')) : asciiLower d = d := by
  unfold asciiLower; simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ite_eq_right h
theorem asciiLower_idem (c : Char) : asciiLower (asciiLower c) = asciiLower c := by
  by_cases h : 'A' ≤ c ∧ c ≤ 'Z'
  · have e : asciiLower c = Char.ofNat (c.toNat + 32) := by
      unfold asciiLower; simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ite_eq_left h
    rw [e]; apply asciiLower_of_not_upper
    rw [char_le_iff, char_le_iff] at h
    have hA : 'A'.toNat = 65 := rfl
    have hZ : 'Z'.toNat = 90 := rfl
    rw [char_le_iff, char_le_iff, toNat_ofNat_lt (n := c.toNat + 32) (by omega), hA, hZ]; omega
  · rw [asciiLower_of_not_upper h, asciiLower_of_not_upper h]

/-- The digit character for `d < 10`. -/
def digitChar (d : Nat) : Char := Char.ofNat (48 + d)

/-- The value of a digit character. -/
def digitVal (c : Char) : Nat := c.toNat - 48

/-- The number a string of decimal digits denotes (Python's `int(s)` on
`[0-9]+`). Leading zeros are allowed. -/
def ofDigits (s : List Char) : Nat := s.foldl (fun a c => a * 10 + digitVal c) 0

/-- Python's default `sys.int_max_str_digits`: `int()` refuses a string of
more digits (leading zeros count, underscores do not) with `ValueError`. -/
def maxIntDigits : Nat := 4300

theorem foldl_digits (l : List Char) (acc : Nat) :
    l.foldl (fun a c => a * 10 + Keel.Codec.digitValue c) acc =
      acc * 10 ^ l.length + l.foldl (fun a c => a * 10 + Keel.Codec.digitValue c) 0 := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (acc * 10 + _), ih (0 * 10 + _)]
    simp only [Nat.zero_mul, Nat.zero_add, Nat.pow_succ, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
    rw [Nat.mul_comm 10 (10 ^ xs.length)]

/-- `Keel.Codec.digitsValue`, 18 digits per big-number step: the same value
(`digitsValueChunked_eq`) in `n / 18` multiplications of the accumulator
instead of `n`. -/
def digitsValueChunked (l : List Char) : Nat := go l 0
where
  go : List Char → Nat → Nat
    | [], acc => acc
    | x :: xs, acc => go ((x :: xs).drop 18)
        (acc * 10 ^ ((x :: xs).take 18).length + Keel.Codec.digitsValue ((x :: xs).take 18))
  termination_by l => l.length
  decreasing_by simp only [List.length_drop, List.length_cons]; omega

theorem digitsValueChunked_go (l : List Char) (acc : Nat) :
    digitsValueChunked.go l acc = l.foldl (fun a c => a * 10 + Keel.Codec.digitValue c) acc := by
  induction l, acc using digitsValueChunked.go.induct with
  | case1 acc => simp [digitsValueChunked.go]
  | case2 x xs acc ih =>
    rw [digitsValueChunked.go, ih]
    conv => rhs; rw [← List.take_append_drop 18 (x :: xs), List.foldl_append, foldl_digits (List.take 18 (x :: xs))]
    rfl

theorem digitsValueChunked_eq (l : List Char) : digitsValueChunked l = Keel.Codec.digitsValue l := by
  simp only [digitsValueChunked, digitsValueChunked_go, Keel.Codec.digitsValue]

/-- Python's `int(s)` on decimal digits, under its digit limit: `none` for more
than `maxIntDigits` digits. Linear in `s`. -/
def boundedDigits? (s : List Char) : Option Nat :=
  if s.length ≤ maxIntDigits then some (digitsValueChunked s) else none

/-- Split at the first occurrence of `sep`: `(before, some after)`, or
`(s, none)` when `sep` does not occur. Tail-recursive: request paths and
query strings can be 64 KiB long. -/
def splitFirst (sep : Char) (s : List Char) : List Char × Option (List Char) :=
  go [] s
where
  go (acc : List Char) : List Char → List Char × Option (List Char)
    | [] => (acc.reverse, none)
    | c :: cs => if c = sep then (acc.reverse, some cs) else go (c :: acc) cs

/-- Split on every occurrence of `sep` (Python's `str.split(sep)`), in one
left-to-right pass. -/
def splitAll (sep : Char) (s : List Char) : List (List Char) :=
  let (cur, acc) := s.foldl (fun (st : List Char × List (List Char)) c =>
    if c = sep then ([], st.1.reverse :: st.2) else (c :: st.1, st.2)) ([], [])
  (cur.reverse :: acc).reverse

/-- Drop leading and trailing ASCII whitespace (Python's `str.strip()` on
the characters HTTP uses). -/
def isWs (c : Char) : Bool := c = ' ' || c = '\t' || c = '\n' || c = '\r'

def stripWs (s : List Char) : List Char := (s.dropWhile isWs).reverse.dropWhile isWs |>.reverse

/-- Deduplicate, keeping first occurrences in order. Quadratic, so only for
short lists (route methods, `Allow`); see `dedupStrings` for request data. -/
def dedup [BEq α] (xs : List α) : List α :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- Deduplicate strings in linear time, keeping first occurrences in order
(for header names and query keys, which a client controls). -/
def dedupStrings (xs : List String) : List String :=
  (xs.foldl (fun (st : Std.HashSet String × List String) x =>
    if st.1.contains x then st else (st.1.insert x, x :: st.2)) ({}, [])).2.reverse

/-- Hexadecimal value of a character, if it is a hex digit. -/
def hexVal? (c : Char) : Option Nat :=
  if isDigitChar c then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55)
  else none

/-- Upper-case hexadecimal digit for `d < 16`. -/
def hexDigit (d : Nat) : Char := if d < 10 then digitChar d else Char.ofNat (55 + d)

end LeanStarlette
