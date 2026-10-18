import LeanStarlette.DataTypes.Chars

/-!
# RepoImpl: text primitives

Decimal digits, the prefix/suffix splits the router backtracks over, and
small list helpers. All structural or well-founded on a size that shrinks.
-/

namespace LeanStarlette

/-- The digit character for `d < 10`. -/
def digitChar (d : Nat) : Char := Char.ofNat (48 + d)

/-- The value of a digit character. -/
def digitVal (c : Char) : Nat := c.toNat - 48

/-- Decimal digits of `n`, most significant first, without leading zeros
(Python's `str(n)` for `n ≥ 0`). -/
def natDigits (n : Nat) : List Char :=
  if n < 10 then [digitChar n] else natDigits (n / 10) ++ [digitChar (n % 10)]
termination_by n
decreasing_by omega

/-- The number a string of decimal digits denotes (Python's `int(s)` on
`[0-9]+`). Leading zeros are allowed. -/
def ofDigits (s : List Char) : Nat := s.foldl (fun a c => a * 10 + digitVal c) 0

/-- Every way to cut `s` in two, longest first part first. This is the order
in which a greedy regular-expression quantifier tries its candidates, so the
router's backtracking agrees with Python's `re`. -/
def splits : List Char → List (List Char × List Char)
  | [] => [([], [])]
  | c :: cs => (splits cs).map (fun p => (c :: p.1, p.2)) ++ [([], c :: cs)]

/-- Split at the first occurrence of `sep`: `(before, some after)`, or
`(s, none)` when `sep` does not occur. -/
def splitFirst (sep : Char) : List Char → List Char × Option (List Char)
  | [] => ([], none)
  | c :: cs =>
    if c = sep then ([], some cs)
    else let r := splitFirst sep cs; (c :: r.1, r.2)

/-- Split on every occurrence of `sep` (Python's `str.split(sep)`). -/
def splitAll (sep : Char) : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    if c = sep then [] :: splitAll sep cs
    else match splitAll sep cs with
      | [] => [[c]]
      | w :: ws => (c :: w) :: ws

/-- Drop leading and trailing ASCII whitespace (Python's `str.strip()` on
the characters HTTP uses). -/
def isWs (c : Char) : Bool := c = ' ' || c = '\t' || c = '\n' || c = '\r'

def stripWs (s : List Char) : List Char := (s.dropWhile isWs).reverse.dropWhile isWs |>.reverse

/-- Deduplicate, keeping first occurrences in order. -/
def dedup [BEq α] (xs : List α) : List α :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- Hexadecimal value of a character, if it is a hex digit. -/
def hexVal? (c : Char) : Option Nat :=
  if isDigitChar c then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55)
  else none

/-- Upper-case hexadecimal digit for `d < 16`. -/
def hexDigit (d : Nat) : Char := if d < 10 then digitChar d else Char.ofNat (55 + d)

end LeanStarlette
