import LeanStarlette.DataTypes.Path
import LeanStarlette.RepoImpl.Text

/-!
# RepoImpl: the five built-in convertors

`starlette/convertors.py`: `str`, `path`, `int`, `float`, `uuid`. Each regular
expression becomes a total recogniser, each `convert`/`to_string` pair a
`convert`/`render` pair. `Proofs/Convertors.lean` proves all five lawful.
-/

namespace LeanStarlette

open LeanJson

/-- `[^/]+`: one non-empty path segment. -/
def strConvertor : Convertor where
  name := "str"
  regex := "[^/]+"
  accepts s := !s.isEmpty && s.all (· ≠ '/')
  allowed c := c ≠ '/'
  convert s := .str (String.ofList s)
  render
    | .str v => if !v.toList.isEmpty && v.toList.all (· ≠ '/') then some v.toList else none
    | _ => none

/-- `.*`: the rest of the path, slashes included. -/
def pathConvertor : Convertor where
  name := "path"
  regex := ".*"
  accepts _ := true
  allowed _ := true
  convert s := .str (String.ofList s)
  render
    | .str v => some v.toList
    | _ => none

/-- `[0-9]+`, converted with `int(...)`. Negative integers do not render,
as upstream asserts. -/
def intConvertor : Convertor where
  name := "int"
  regex := "[0-9]+"
  accepts s := !s.isEmpty && s.all isDigitChar
  allowed := isDigitChar
  convert s := .int (ofDigits s)
  render
    | .int n => some (natDigits n)
    | _ => none

/-! ## Exact decimals for the `float` convertor -/

/-- Strip trailing decimal zeros from `m * 10^e`, giving `LeanJson.Decimal`'s
normal form. -/
def normDec (m : Nat) (e : Int) : Nat × Int :=
  if m = 0 then (0, 0) else if m % 10 = 0 then normDec (m / 10) (e + 1) else (m, e)
termination_by m
decreasing_by omega

theorem normDec_spec (m : Nat) (e : Int) :
    ((normDec m e).1 = 0 ∧ (normDec m e).2 = 0) ∨ (normDec m e).1 % 10 ≠ 0 := by
  induction m using Nat.strongRecOn generalizing e with
  | _ m ih =>
    unfold normDec
    by_cases h0 : m = 0
    · simp [h0]
    · by_cases h1 : m % 10 = 0
      · simp only [h0, h1, ↓reduceIte]; exact ih _ (by omega) _
      · simp [h0, h1]

/-- The non-negative decimal `m * 10^e` in normal form. -/
def mkDec (m : Nat) (e : Int) : Decimal :=
  ⟨false, (normDec m e).1, (normDec m e).2, normDec_spec m e⟩

/-- The digits of `d` in plain positional notation (no exponent): Python's
`("%0.20f" % v).rstrip("0").rstrip(".")` without the rounding to 20 places
(UP-029). -/
def renderDec (d : Decimal) : List Char :=
  match d.exp with
  | .ofNat k => natDigits d.mant ++ List.replicate k '0'
  | .negSucc k =>
    let ds := natDigits d.mant
    let pad := List.replicate (k + 2 - ds.length) '0' ++ ds
    pad.take (pad.length - (k + 1)) ++ '.' :: pad.drop (pad.length - (k + 1))

/-- `[0-9]+(\.[0-9]+)?` -/
def floatAccepts (s : List Char) : Bool :=
  match splitFirst '.' s with
  | (ip, none) => !ip.isEmpty && ip.all isDigitChar
  | (ip, some fp) => !ip.isEmpty && ip.all isDigitChar && !fp.isEmpty && fp.all isDigitChar

/-- `float(s)` on an accepted string, exactly. -/
def floatConvert (s : List Char) : Decimal :=
  match splitFirst '.' s with
  | (ip, none) => mkDec (ofDigits ip) 0
  | (ip, some fp) => mkDec (ofDigits (ip ++ fp)) (-(fp.length : Int))

def floatConvertor : Convertor where
  name := "float"
  regex := "[0-9]+(\\.[0-9]+)?"
  accepts := floatAccepts
  allowed c := isDigitChar c || c = '.'
  convert s := .float (floatConvert s)
  render
    | .float d => if d.neg then none else some (renderDec d)
    | _ => none

/-! ## UUIDs -/

/-- Hex groups of a UUID, each optionally followed by a hyphen:
`[0-9a-fA-F]{8}-?[0-9a-fA-F]{4}-?[0-9a-fA-F]{4}-?[0-9a-fA-F]{4}-?[0-9a-fA-F]{12}`.
A hex digit is never a hyphen, so the optional hyphens are deterministic. -/
def uuidGroups : List Nat → List Char → Bool
  | [], s => s.isEmpty
  | [g], s => s.length = g && s.all isHexChar
  | g :: gs, s =>
    (s.take g).length = g && (s.take g).all isHexChar &&
      match s.drop g with
      | '-' :: r => uuidGroups gs r
      | r => uuidGroups gs r

/-- The canonical 32 hex digits of an accepted UUID string. -/
def uuidHex (s : List Char) : List Char := (s.filter (· ≠ '-')).map asciiLower

/-- `str(uuid)`: `8-4-4-4-12` lower-case hex. -/
def renderUUID (u : UUID) : List Char :=
  u.hex.take 8 ++ ('-' :: ((u.hex.drop 8).take 4 ++ ('-' :: ((u.hex.drop 12).take 4 ++ ('-' ::
    ((u.hex.drop 16).take 4 ++ ('-' :: u.hex.drop 20)))))))

def uuidConvertor : Convertor where
  name := "uuid"
  regex := "[0-9a-fA-F]{8}-?[0-9a-fA-F]{4}-?[0-9a-fA-F]{4}-?[0-9a-fA-F]{4}-?[0-9a-fA-F]{12}"
  accepts := uuidGroups [8, 4, 4, 4, 12]
  allowed c := isHexChar c || c = '-'
  convert s :=
    if h : (uuidHex s).length = 32 ∧ ∀ c ∈ uuidHex s, isLowerHex c = true then
      .uuid ⟨uuidHex s, h.1, h.2⟩
    else .str (String.ofList s)
  render
    | .uuid u => some (renderUUID u)
    | _ => none

/-- `CONVERTOR_TYPES`: the convertors a template may name. Pass a longer list
to `compilePath` for `register_url_convertor`. -/
def defaultConvertors : List Convertor :=
  [strConvertor, pathConvertor, intConvertor, floatConvertor, uuidConvertor]

end LeanStarlette
