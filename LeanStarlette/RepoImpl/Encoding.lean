import LeanStarlette.RepoImpl.Text

/-!
# RepoImpl: percent-encoding and UTF-8

What Python's `urllib.parse` does for Starlette: `unquote`/`unquote_plus`
(percent-decoding, then UTF-8 with `errors="replace"`), `quote` with a safe
set (for `RedirectResponse`'s `location`), and `quote_plus` (for
`urlencode`). Every function is total; the decoder recurses on the bytes
left, each step consuming at least one.
-/

namespace LeanStarlette

/-! ## UTF-8 decoding with replacement -/

/-- The allowed range of the second byte after a lead byte, and how many
continuation bytes follow (Unicode Table 3-7, well-formed UTF-8). -/
def utf8Lead (b : UInt8) : Option (Nat × UInt8 × UInt8) :=
  let n := b.toNat
  if 0xC2 ≤ n ∧ n ≤ 0xDF then some (1, 0x80, 0xBF)
  else if n = 0xE0 then some (2, 0xA0, 0xBF)
  else if (0xE1 ≤ n ∧ n ≤ 0xEC) ∨ n = 0xEE ∨ n = 0xEF then some (2, 0x80, 0xBF)
  else if n = 0xED then some (2, 0x80, 0x9F)
  else if n = 0xF0 then some (3, 0x90, 0xBF)
  else if 0xF1 ≤ n ∧ n ≤ 0xF3 then some (3, 0x80, 0xBF)
  else if n = 0xF4 then some (3, 0x80, 0x8F)
  else none

/-- How many continuation bytes of `need` are present at the head of `bs`,
the first in `[lo, hi]` and the rest in `[0x80, 0xBF]`. -/
def contRun (lo hi : UInt8) : Nat → List UInt8 → Nat
  | 0, _ => 0
  | _ + 1, [] => 0
  | k + 1, b :: bs => if lo ≤ b ∧ b ≤ hi then 1 + contRun 0x80 0xBF k bs else 0

theorem contRun_le (lo hi : UInt8) : ∀ k bs, contRun lo hi k bs ≤ k
  | 0, _ => by simp [contRun]
  | _ + 1, [] => by simp [contRun]
  | k + 1, b :: bs => by
    simp only [contRun]; split
    · have := contRun_le 0x80 0xBF k bs; omega
    · omega

/-- The code point of a complete sequence. -/
def utf8Value (lead : UInt8) (conts : List UInt8) : Nat :=
  let init := match conts.length with
    | 1 => lead.toNat % 0x20
    | 2 => lead.toNat % 0x10
    | _ => lead.toNat % 0x08
  conts.foldl (fun acc c => acc * 64 + c.toNat % 64) init

/-- `bytes.decode("utf-8", errors="replace")`: each maximal ill-formed
subpart becomes U+FFFD. -/
def decodeUtf8 (bs : List UInt8) : List Char :=
  match bs with
  | [] => []
  | b :: rest =>
    if b.toNat < 0x80 then Char.ofNat b.toNat :: decodeUtf8 rest
    else match utf8Lead b with
      | none => '�' :: decodeUtf8 rest
      | some (need, lo, hi) =>
        let k := contRun lo hi need rest
        have : rest.length - k ≤ rest.length := by omega
        if k = need then Char.ofNat (utf8Value b (rest.take k)) :: decodeUtf8 (rest.drop k)
        else '�' :: decodeUtf8 (rest.drop k)
termination_by bs.length
decreasing_by all_goals (simp; try omega)

/-! ## Percent-decoding -/

/-- A character of a percent-encoded string: a decoded `%XX` byte, or a
character kept as it is. -/
inductive PctTok where
  | byte (b : UInt8)
  | char (c : Char)

/-- Read `%XX` escapes (an invalid one is kept literally, as Python does). -/
def pctTokens : List Char → List PctTok
  | [] => []
  | '%' :: a :: b :: rest =>
    match hexVal? a, hexVal? b with
    | some x, some y => .byte (UInt8.ofNat (x * 16 + y)) :: pctTokens rest
    | _, _ => .char '%' :: pctTokens (a :: b :: rest)
  | c :: rest => .char c :: pctTokens rest

/-- Decode each run of bytes as UTF-8 and keep the characters between. -/
def pctDecode (pending : List UInt8) : List PctTok → List Char
  | [] => decodeUtf8 pending.reverse
  | .byte b :: ts => pctDecode (b :: pending) ts
  | .char c :: ts => decodeUtf8 pending.reverse ++ c :: pctDecode [] ts

/-- `urllib.parse.unquote(s)`: runs of valid `%XX` escapes are decoded as
UTF-8 (with replacement); everything else is kept. -/
def unquoteList (s : List Char) : List Char := pctDecode [] (pctTokens s)

def unquote (s : String) : String := String.ofList (unquoteList s.toList)

/-- `urllib.parse.unquote_plus(s)`: `+` is a space, then `unquote`. -/
def unquotePlus (s : String) : String :=
  String.ofList (unquoteList (s.toList.map fun c => if c = '+' then ' ' else c))

/-! ## Percent-encoding -/

/-- `A-Za-z0-9_.-~`: never quoted. -/
def isUnreserved (c : Char) : Bool := isIdentChar c || c = '.' || c = '-' || c = '~'
where isIdentChar (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || isDigitChar c || c = '_'

/-- `%XX` for each UTF-8 byte of `c`. -/
def escapeChar (c : Char) : List Char :=
  (String.singleton c).toUTF8.toList.flatMap fun b => ['%', hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]

/-- `urllib.parse.quote(s, safe=safe)`. -/
def quote (s : String) (safe : List Char := ['/']) : String :=
  String.ofList (s.toList.flatMap fun c => if isUnreserved c || safe.contains c then [c] else escapeChar c)

/-- `urllib.parse.quote_plus(s, safe='')`. -/
def quotePlus (s : String) : String :=
  String.ofList (s.toList.flatMap fun c =>
    if c = ' ' then ['+'] else if isUnreserved c then [c] else escapeChar c)

end LeanStarlette
