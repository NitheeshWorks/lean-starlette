/-!
# DataTypes: character classes

The small character predicates that the invariants below are stated with.
They are ASCII-only on purpose: HTTP field names, URL path convertors and
hexadecimal digits are all ASCII grammars (RFC 9110 section 5.1, RFC 3986).
-/

namespace LeanStarlette

/-- `0-9`. -/
def isDigitChar (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- `0-9a-f`: the alphabet of a canonical (lower-case) UUID. -/
def isLowerHex (c : Char) : Bool := isDigitChar c || ('a' ≤ c && c ≤ 'f')

/-- `0-9a-fA-F`. -/
def isHexChar (c : Char) : Bool := isLowerHex c || ('A' ≤ c && c ≤ 'F')

/-- ASCII lower-casing of one character, as `bytes.lower()` does. -/
def asciiLower (c : Char) : Char :=
  if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

/-- ASCII lower-casing of a string. HTTP field names are ASCII tokens, so this
is the case folding RFC 9110 section 5.1 asks for. -/
def lowerAscii (s : String) : String := String.ofList (s.toList.map asciiLower)

/-- A string with no ASCII upper-case letter: the invariant of a stored header name. -/
def IsLower (s : String) : Prop := lowerAscii s = s

instance (s : String) : Decidable (IsLower s) := inferInstanceAs (Decidable (_ = _))

end LeanStarlette
