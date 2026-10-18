import Keel.Regex
import LeanStarlette.RepoImpl.PyRe.Unicode

/-!
# RepoImpl: Python's `re` dialect, over `Keel.Regex`

`CORSMiddleware(allow_origin_regex=...)` runs `re.compile(pattern)` and then
`fullmatch(origin)`. This module is only the dialect: its atoms (`Atom`,
with `\d`, `\w`, `\s` from Python's own Unicode tables) and a parser from
the pattern text to `Keel.Regex`. The matcher, its linear-time scan and its
laws are Keel's; `compile` asks for `Mode.full`, which is `re.fullmatch`.

The parser follows `re._parser` (CPython 3.13): the same escapes, class
syntax, quantifier forms (a `{` that does not start one is a literal) and
the same errors (`nothing to repeat`, `multiple repeat`, `bad escape`,
`bad character range`, `unbalanced parenthesis`, …).

Not supported, and an error at construction (`Unsupported`): backreferences
(`\1`, `(?P=name)`), lookahead and lookbehind, conditionals, atomic groups
and possessive quantifiers (they change what is accepted, and a
backtracking-free matcher cannot express them), inline flags (`(?i)`, …),
`\N{...}`. One construct differs: `$` is the end of the text (`\Z`), where
Python also accepts it before a final `\n`; under `fullmatch` that matters
only when the pattern goes on to match the `\n` (`a$\n`). Repeat counts are
at most 1000, and the expanded pattern at most 100 000 nodes.
-/

namespace LeanStarlette.PyRe

open Keel

/-- Whether a code point is in a sorted table of ranges (binary search). -/
def inRanges (t : Array (Nat × Nat)) (n : Nat) : Bool :=
  go 32 0 t.size
where
  go : Nat → Nat → Nat → Bool
    | 0, _, _ => false
    | fuel + 1, lo, hi =>
      if lo < hi then
        let mid := (lo + hi) / 2
        match t[mid]? with
        | some (a, b) => if n < a then go fuel lo mid else if b < n then go fuel (mid + 1) hi else true
        | none => false
      else false

/-- `\w`, and the word characters `\b` reads. -/
def isWord (c : Char) : Bool := inRanges Unicode.word c.toNat
/-- `\d` -/
def isDigit (c : Char) : Bool := inRanges Unicode.digit c.toNat
/-- `\s` -/
def isSpace (c : Char) : Bool := inRanges Unicode.space c.toNat

/-- The dialect's atoms. -/
inductive Atom where
  | char (c : Char)
  | range (lo hi : Char)
  /-- `.`: any character but `\n`. -/
  | dot
  | digit
  | word
  | space
  deriving DecidableEq, Hashable, Repr

instance : CharClass Atom where
  test
    | .char a, c => c == a
    | .range lo hi, c => lo ≤ c && c ≤ hi
    | .dot, c => c != '\n'
    | .digit, c => isDigit c
    | .word, c => isWord c
    | .space, c => isSpace c
  word := isWord

/-- The classes: atoms under union and negation. -/
abbrev K := Regex.Cls Atom

/-- A parsed pattern. -/
abbrev Re := Regex K

/-- Why a pattern was refused. -/
inductive Error where
  /-- What `re.compile` refuses too (`re.error`). -/
  | invalid (msg : String)
  /-- What Python accepts and this dialect does not (a documented deviation). -/
  | unsupported (what : String)
  deriving DecidableEq, Repr

instance : ToString Error where
  toString
    | .invalid m => m
    | .unsupported w => s!"unsupported regular-expression feature: {w}"

/-- The largest repeat count. -/
def maxRepeat : Nat := 1000

/-- The largest expanded pattern. -/
def maxNodes : Nat := 100000

/-- Number of nodes of a term. -/
def size : Re → Nat
  | .alt r s | .cat r s => size r + size s + 1
  | .star r => size r + 1
  | _ => 1

private def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

private def isOct (c : Char) : Bool := '0' ≤ c && c ≤ '7'

private def isDig (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- Exactly `k` hex digits. -/
private def takeHex : Nat → List Char → Nat → Option (Nat × List Char)
  | 0, s, acc => some (acc, s)
  | k + 1, c :: s, acc => (hexVal c).bind fun v => takeHex k s (acc * 16 + v)
  | _ + 1, [], _ => none

/-- Up to `k` more octal digits. -/
private def takeOct : Nat → List Char → Nat → Nat × List Char
  | k + 1, c :: s, acc => if isOct c then takeOct k s (acc * 8 + (c.toNat - '0'.toNat)) else (acc, c :: s)
  | _, s, acc => (acc, s)

private def charOf (n : Nat) (what : String) : Except Error Char :=
  if n.isValidChar then .ok (Char.ofNat n)
  else .error (.invalid s!"bad escape {what}")

/-- What an escape stands for. -/
inductive Esc where
  | lit (c : Char)
  | cls (k : K)
  | assert (a : Regex.Assertion)

/-- The escape after a `\`, in a class (`inClass`) or not. -/
def escape (inClass : Bool) : List Char → Except Error (Esc × List Char)
  | [] => .error (.invalid "bad escape (end of pattern)")
  | c :: s =>
    match c with
    | 'd' => .ok (.cls (.atom .digit), s)
    | 'D' => .ok (.cls (.neg (.atom .digit)), s)
    | 'w' => .ok (.cls (.atom .word), s)
    | 'W' => .ok (.cls (.neg (.atom .word)), s)
    | 's' => .ok (.cls (.atom .space), s)
    | 'S' => .ok (.cls (.neg (.atom .space)), s)
    | 'n' => .ok (.lit '\n', s)
    | 't' => .ok (.lit '\t', s)
    | 'r' => .ok (.lit '\r', s)
    | 'f' => .ok (.lit '\x0c', s)
    | 'v' => .ok (.lit '\x0b', s)
    | 'a' => .ok (.lit '\x07', s)
    | 'b' => if inClass then .ok (.lit '\x08', s) else .ok (.assert .wordBoundary, s)
    | 'B' => if inClass then .error (.invalid "bad escape \\B") else .ok (.assert .notWordBoundary, s)
    | 'A' => if inClass then .error (.invalid "bad escape \\A") else .ok (.assert .start, s)
    | 'Z' => if inClass then .error (.invalid "bad escape \\Z") else .ok (.assert .finish, s)
    | 'x' => match takeHex 2 s 0 with
      | some (n, s) => do return (.lit (← charOf n "\\x"), s)
      | none => .error (.invalid "incomplete escape \\x")
    | 'u' => match takeHex 4 s 0 with
      | some (n, s) => do return (.lit (← charOf n "\\u"), s)
      | none => .error (.invalid "incomplete escape \\u")
    | 'U' => match takeHex 8 s 0 with
      | some (n, s) => do return (.lit (← charOf n "\\U"), s)
      | none => .error (.invalid "incomplete escape \\U")
    | 'N' => .error (.unsupported "named character escape \\N{...}")
    | '0' => let (n, s) := takeOct 2 s 0; do return (.lit (← charOf n "\\0"), s)
    | c =>
      if isDig c then
        if inClass then
          if isOct c then
            let (n, s) := takeOct 2 s (c.toNat - '0'.toNat)
            if n > 0o377 then .error (.invalid "octal escape value outside of range 0-0o377")
            else do return (.lit (← charOf n "\\"), s)
          else .error (.invalid s!"bad escape \\{c}")
        else
          match s with
          | d :: e :: s' =>
            if isOct c && isOct d && isOct e then
              let n := ((c.toNat - 48) * 8 + (d.toNat - 48)) * 8 + (e.toNat - 48)
              if n > 0o377 then .error (.invalid "octal escape value outside of range 0-0o377")
              else do return (.lit (← charOf n "\\"), s')
            else .error (.unsupported "backreference")
          | _ => .error (.unsupported "backreference")
      else if c.isAlpha then .error (.invalid s!"bad escape \\{c}")
      else .ok (.lit c, s)

/-- One member of a class: a character, or a class escape. -/
private def classAtom : List Char → Except Error (Esc × List Char)
  | '\\' :: s => escape true s
  | c :: s => .ok (.lit c, s)
  | [] => .error (.invalid "unterminated character set")

/-- The body of `[...]` after `[` (and `^`); `first` while no member has
been read, when `]` is a literal. -/
def classBody : Nat → Bool → Option K → List Char → Except Error (K × List Char)
  | 0, _, _, _ => .error (.invalid "unterminated character set")
  | fuel + 1, first, acc, s =>
    let add (k : K) : Option K := some (match acc with | some a => .union a k | none => k)
    match s, first with
    | ']' :: s, false => match acc with
      | some k => .ok (k, s)
      | none => .error (.invalid "unterminated character set")
    | [], _ => .error (.invalid "unterminated character set")
    | s, _ => do
      let (a, s) ← classAtom s
      match s with
      | '-' :: ']' :: _ | '-' :: [] =>
        let k : K := match a with | .lit c => .atom (.char c) | .cls k => k | .assert _ => .atom (.char '-')
        classBody fuel false (add k) s
      | '-' :: s' => do
        let (b, s'') ← classAtom s'
        match a, b with
        | .lit lo, .lit hi =>
          if hi < lo then .error (.invalid "bad character range")
          else classBody fuel false (add (.atom (.range lo hi))) s''
        | _, _ => .error (.invalid "bad character range")
      | _ =>
        match a with
        | .lit c => classBody fuel false (add (.atom (.char c))) s
        | .cls k => classBody fuel false (add k) s
        | .assert _ => .error (.invalid "bad escape")

/-- A quantifier at the head of the text: its bounds, laziness ignored
(`re.fullmatch` accepts the same texts either way). `none` when there is
none (a `{` that does not start one is a literal). -/
def quantifier : List Char → Except Error (Option ((Nat × Option Nat) × List Char))
  | c :: s =>
    let rest (b : Nat × Option Nat) (s : List Char) : Except Error (Option ((Nat × Option Nat) × List Char)) :=
      match s with
      | '?' :: s => .ok (some (b, s))
      | '+' :: _ => .error (.unsupported "possessive quantifier")
      | s => .ok (some (b, s))
    match c with
    | '*' => rest (0, none) s
    | '+' => rest (1, none) s
    | '?' => rest (0, some 1) s
    | '{' =>
      if s.head? = some '}' then .ok none else
      let lo := s.takeWhile isDig
      let s1 := s.dropWhile isDig
      let (hi, s2) := match s1 with
        | ',' :: t => (some (t.takeWhile isDig), t.dropWhile isDig)
        | t => (none, t)
      match s2 with
      | '}' :: s3 =>
        let m := if lo.isEmpty then 0 else lo.foldl (fun a c => a * 10 + (c.toNat - 48)) 0
        let n : Option Nat := match hi with
          | none => some m
          | some h => if h.isEmpty then none else some (h.foldl (fun a c => a * 10 + (c.toNat - 48)) 0)
        if n.any (· < m) then .error (.invalid "min repeat greater than max repeat")
        else if m > maxRepeat || n.any (· > maxRepeat) then
          .error (.unsupported s!"repeat count above {maxRepeat}")
        else rest (m, n) s3
      | _ => .ok none
    | _ => .ok none
  | [] => .ok none

/-- `r` repeated `m` to `n` times. -/
def «repeat» (r : Re) (m : Nat) (n : Option Nat) : Re :=
  let pre := (List.replicate m r).foldr (fun x acc => .cat x acc) .eps
  match n with
  | none => .cat pre (.star r)
  | some n => .cat pre ((List.replicate (n - m) r).foldr (fun x acc => .alt (.cat x acc) .eps) .eps)

/-- An item of a sequence: what a quantifier sees as its operand. -/
inductive Item where
  | atom (r : Re)
  | assert (r : Re)
  | repeated (r : Re)

def Item.re : Item → Re
  | .atom r | .assert r | .repeated r => r

/-- Whether a name is a Python identifier (for `(?P<name>...)`). -/
def isIdent (s : List Char) : Bool :=
  match s with
  | c :: r => (c.isAlpha || c == '_' || c.toNat ≥ 128) && r.all (fun c => c.isAlphanum || c == '_' || c.toNat ≥ 128)
  | [] => false

mutual
/-- `a|b|…` up to a `)` or the end. -/
def alt : Nat → List Char → Except Error (Re × List Char)
  | 0, _ => .error (.unsupported "pattern nesting too deep")
  | fuel + 1, s => do
    let (r, s) ← seq fuel [] s
    match s with
    | '|' :: s => do
      let (r2, s) ← alt fuel s
      return (.alt r r2, s)
    | s => return (r, s)

/-- A sequence of items (kept last-first). -/
def seq : Nat → List Item → List Char → Except Error (Re × List Char)
  | 0, _, _ => .error (.unsupported "pattern nesting too deep")
  | fuel + 1, items, s =>
    let done := fun s => Except.ok ((items.reverse.map Item.re).foldr (fun x acc => if let .eps := acc then x else .cat x acc) .eps, s)
    match s with
    | [] => done []
    | ')' :: _ | '|' :: _ => done s
    | s => do
      match ← quantifier s with
      | some ((m, n), s') =>
        match items with
        | [] | .assert _ :: _ => .error (.invalid "nothing to repeat")
        | .repeated _ :: _ => .error (.invalid "multiple repeat")
        | .atom r :: rest => seq fuel (.repeated («repeat» r m n) :: rest) s'
      | none =>
        let (it, s) ← atom fuel s
        match it with
        | some it => seq fuel (it :: items) s
        | none => seq fuel items s

/-- One atom; `none` for a comment `(?#...)`. -/
def atom : Nat → List Char → Except Error (Option Item × List Char)
  | 0, _ => .error (.unsupported "pattern nesting too deep")
  | fuel + 1, s =>
    match s with
    | '.' :: s => .ok (some (.atom (.cls (.atom .dot))), s)
    | '^' :: s => .ok (some (.assert (.assert .start)), s)
    | '$' :: s => .ok (some (.assert (.assert .finish)), s)
    | '\\' :: s => do
      let (e, s) ← escape false s
      match e with
      | .lit c => return (some (.atom (.cls (.atom (.char c)))), s)
      | .cls k => return (some (.atom (.cls k)), s)
      | .assert a => return (some (.assert (.assert a)), s)
    | '[' :: s => do
      let (neg, s) := match s with | '^' :: s => (true, s) | s => (false, s)
      let (k, s) ← classBody (s.length + 1) true none s
      return (some (.atom (.cls (if neg then .neg k else k))), s)
    | '(' :: s =>
      let group (s : List Char) : Except Error (Option Item × List Char) := do
        let (r, s) ← alt fuel s
        match s with
        | ')' :: s => return (some (.atom r), s)
        | _ => .error (.invalid "missing ), unterminated subpattern")
      match s with
      | '?' :: ':' :: s => group s
      | '?' :: 'P' :: '<' :: s =>
        let name := s.takeWhile (· ≠ '>')
        match s.dropWhile (· ≠ '>') with
        | '>' :: s => if isIdent name then group s else .error (.invalid "bad character in group name")
        | _ => .error (.invalid "missing >, unterminated name")
      | '?' :: 'P' :: '=' :: _ => .error (.unsupported "backreference")
      | '?' :: '#' :: s =>
        match s.dropWhile (· ≠ ')') with
        | ')' :: s => .ok (none, s)
        | _ => .error (.invalid "missing ), unterminated comment")
      | '?' :: '=' :: _ | '?' :: '!' :: _ => .error (.unsupported "lookahead")
      | '?' :: '<' :: '=' :: _ | '?' :: '<' :: '!' :: _ => .error (.unsupported "lookbehind")
      | '?' :: '>' :: _ => .error (.unsupported "atomic group")
      | '?' :: '(' :: _ => .error (.unsupported "conditional group")
      | '?' :: c :: _ =>
        if "aiLmsux-".toList.contains c then .error (.unsupported "inline flags")
        else .error (.invalid s!"unknown extension ?{c}")
      | ['?'] => .error (.invalid "unexpected end of pattern")
      | s => group s
    | c :: s => .ok (some (.atom (.cls (.atom (.char c)))), s)
    | [] => .ok (none, [])
end

/-- **Parse a pattern** as `re.compile` does. -/
def parse (p : String) : Except Error Re := do
  let s := p.toList
  let (r, rest) ← alt (4 * s.length + 4) s
  match rest with
  | [] => if size r > maxNodes then .error (.unsupported s!"expanded pattern above {maxNodes} nodes") else .ok r
  | _ => .error (.invalid "unbalanced parenthesis")

/-- **`re.compile(pattern).fullmatch`**: the pattern compiled once in
`Mode.full`. -/
def compile (p : String) : Except Error (Regex.Matcher K) := (parse p).map (·.compile .full)

end LeanStarlette.PyRe
