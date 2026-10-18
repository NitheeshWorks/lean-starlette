import LeanStarlette.RepoImpl.Convertors

/-!
# RepoImpl: compiling, matching and rendering path templates

* `compilePath` is `compile_path`: it finds `{name}` and `{name:type}`
  placeholders exactly where upstream's `PARAM_REGEX` would, and rejects
  unknown convertors and duplicated names with upstream's messages.
* `Template.match` is `path_regex.match(route_path)` followed by the
  convertors' `convert`: greedy, backtracking in the same order as Python's
  `re`, but anchored at the true end of the path (UP-030).
* `Template.urlFor` is `replace_params`, with `url_path_for`'s check that the
  given parameters are exactly the template's.
-/

namespace LeanStarlette

/-! ## Compiling -/

/-- `[a-zA-Z_]` -/
def isIdentStart (c : Char) : Bool := ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || c = '_'

/-- `[a-zA-Z0-9_]` -/
def isIdentChar (c : Char) : Bool := isIdentStart c || isDigitChar c

/-- After a `{`: `ident (':' ident)? '}'`, giving the name, the convertor
type (default `str`) and the rest. -/
def scanParam (s : List Char) : Option (String × String × List Char) :=
  match s with
  | c :: rest =>
    if isIdentStart c then
      let name := c :: rest.takeWhile isIdentChar
      match rest.dropWhile isIdentChar with
      | '}' :: r => some (String.ofList name, "str", r)
      | ':' :: t :: r =>
        if isIdentStart t then
          let ty := t :: r.takeWhile isIdentChar
          match r.dropWhile isIdentChar with
          | '}' :: r' => some (String.ofList name, String.ofList ty, r')
          | _ => none
        else none
      | _ => none
    else none
  | [] => none

theorem dropWhile_length_le (p : α → Bool) (l : List α) : (l.dropWhile p).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.dropWhile_cons]; split <;> simp <;> omega

theorem scanParam_length {s : List Char} {r : String × String × List Char}
    (h : scanParam s = some r) : r.2.2.length < s.length := by
  unfold scanParam at h
  split at h
  · rename_i c rest
    split at h
    · have h1 := dropWhile_length_le isIdentChar rest
      split at h
      · rename_i r' hr; cases h; simp only [List.length_cons]; rw [hr] at h1; simp at h1; omega
      · rename_i t r' hr
        split at h
        · have h2 := dropWhile_length_le isIdentChar r'
          split at h
          · rename_i r'' hr'; cases h; rw [hr] at h1; rw [hr'] at h2
            simp at h1 h2; simp; omega
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- A raw piece before convertor lookup. -/
inductive RawPiece where
  | lit (c : Char)
  | param (name ty : String)

/-- Scan a path for placeholders, left to right, as `PARAM_REGEX.finditer`. -/
def scanPath (s : List Char) : List RawPiece :=
  match s with
  | [] => []
  | '{' :: rest =>
    match h : scanParam rest with
    | some (n, ty, r) =>
      have : r.length < rest.length := scanParam_length h
      .param n ty :: scanPath r
    | none => .lit '{' :: scanPath rest
  | c :: rest => .lit c :: scanPath rest
termination_by s.length

/-- Join adjacent literal characters into literal pieces. -/
def joinLits : List RawPiece → List (List Char ⊕ (String × String))
  | [] => []
  | .lit c :: ps =>
    match joinLits ps with
    | .inl l :: qs => .inl (c :: l) :: qs
    | qs => .inl [c] :: qs
  | .param n ty :: ps => .inr (n, ty) :: joinLits ps

/-- The sorted, deduplicated names that occur more than once. -/
def duplicates (names : List String) : List String :=
  let ds := dedup (names.filter fun n => names.count n > 1)
  ds.mergeSort (fun a b => decide (a ≤ b))

/-- `compile_path(path)` for a route path: the template, or upstream's error
message for an unknown convertor or a duplicated parameter name. -/
def compilePath (path : String) (convertors : List Convertor := defaultConvertors) :
    Except String Template := do
  let raw := joinLits (scanPath path.toList)
  let pieces ← raw.mapM fun
    | .inl l => pure (Piece.lit l)
    | .inr (n, ty) => match convertors.find? (·.name == ty) with
      | some c => pure (Piece.param n c)
      | none => throw s!"Unknown path convertor '{ty}'"
  let names := pieces.filterMap Piece.paramName?
  if h : names.Nodup then
    pure ⟨path, pieces, h⟩
  else
    let ds := duplicates names
    let ending := if ds.length > 1 then "s" else ""
    throw s!"Duplicated param name{ending} {", ".intercalate ds} at path {path}"

/-! ## Matching -/

/-- Match pieces against the whole of `s`, converting each parameter. A
parameter tries its candidate lengths longest first and backtracks, as a
greedy quantifier does; the match must consume all of `s`. -/
def matchPieces : List Piece → List Char → Option PathParams
  | [], s => if s.isEmpty then some [] else none
  | .lit l :: ps, s => if l.isPrefixOf s then matchPieces ps (s.drop l.length) else none
  | .param n c :: ps, s => (splits s).findSome? fun pq =>
      if c.accepts pq.1 then (matchPieces ps pq.2).map ((n, c.convert pq.1) :: ·) else none

/-- `path_regex.match(path)`, converted: the path parameters on a match. -/
def Template.match (t : Template) (path : String) : Option PathParams :=
  matchPieces t.pieces path.toList

/-! ## Rendering -/

/-- Fill in every parameter from `ps`; `none` if one is missing or does not
render. -/
def renderPieces (ps : PathParams) : List Piece → Option (List Char)
  | [] => some []
  | .lit l :: rest => (renderPieces ps rest).map (l ++ ·)
  | .param n c :: rest => do
    let v ← ps.lookup n
    let s ← c.render v
    let r ← renderPieces ps rest
    pure (s ++ r)

/-- `url_path_for`'s parameter check: the given names are exactly the
template's (as sets, as upstream compares them). -/
def Template.acceptsParams (t : Template) (ps : PathParams) : Bool :=
  ps.all (fun p => t.paramNames.contains p.1) && t.paramNames.all (fun n => (ps.lookup n).isSome)

/-- `replace_params(path_format, ...)` behind `url_path_for`: the path with
the parameters filled in, or `none` (upstream's `NoMatchFound` or
`AssertionError`). -/
def Template.urlFor (t : Template) (ps : PathParams) : Option String :=
  if t.acceptsParams ps then (renderPieces ps t.pieces).map String.ofList else none

end LeanStarlette
