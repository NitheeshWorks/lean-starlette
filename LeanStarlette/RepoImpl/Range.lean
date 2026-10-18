import Keel.Codec
import LeanStarlette.RepoImpl.Text

/-!
# RepoImpl: the `Range` header

`FileResponse._parse_range_header` and `_parse_ranges`, as a total function
from the header text and the file size to a decision:

* `full`: serve the whole file (no usable range, or more than
  `max_ranges = 100` of them, which upstream also answers with the whole
  file);
* `ranges`: byte ranges `[start, end)`, each non-empty and inside the file,
  at most 100, and, when there are several, sorted with gaps between them
  (overlapping and touching ranges merged). These are fields of
  `ByteRanges`, so a caller cannot read past the file;
* `malformed` (400) and `unsatisfiable` (416).

The work is linear in the header's length, which `Std.Http` caps at 8 KiB:
the count check comes before any range is parsed.

Numbers are read as Python's `int()` reads them after `strip()`: an optional
sign and digits with single underscores between them (Unicode digits are not
accepted; see `CONTRIBUTING.md`).
-/

namespace LeanStarlette

/-- At most this many ranges are honoured (`FileResponse.max_ranges`). -/
def maxRanges : Nat := 100

/-- Offsets the digit bound allows: CPython's `int()` reads up to 4300
digits, so offsets below `10 ^ 4300`. -/
def maxPrintable : Nat := 10 ^ maxIntDigits

/-- `int(s)` for `s` already stripped, including its digit limit: more than
`maxIntDigits` digits is upstream's `ValueError`, so `none`. Linear in `s`. -/
def pyInt? (s : List Char) : Option Int :=
  let (neg, ds) := match s with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | r => (false, r)
  let ok := !ds.isEmpty && ds.all (fun c => c.isDigit || c = '_') &&
    ds.head? != some '_' && ds.getLast? != some '_' && !(ds.zip ds.tail).any (fun p => p.1 = '_' && p.2 = '_')
  if ok then
    (boundedDigits? (ds.filter Char.isDigit)).map fun (n : Nat) => if neg then -(n : Int) else n
  else none

/-- One `start-end` part of a `Range` header, as upstream reads it, or
`none` when upstream ignores the part. -/
def parseRangePart (size : Nat) (part : List Char) : Option (Int × Int) :=
  let part := stripWs part
  if part.isEmpty || part == ['-'] then none else
  match splitFirst '-' part with
  | (_, none) => none
  | (s, some e) =>
    let s := stripWs s
    let e := stripWs e
    if s.isEmpty then
      (pyInt? e).map fun n => (max ((size : Int) - n) 0, (size : Int))
    else
      match pyInt? s with
      | none => none
      | some st =>
        if e.isEmpty then some (st, size)
        else (pyInt? e).map fun (en : Int) => (st, if en < (size : Int) then en + 1 else (size : Int))

/-- Consecutive ranges are separated by a gap: each ends before the next
starts. -/
def Gapped : List (Nat × Nat) → Prop
  | a :: b :: rest => a.2 < b.1 ∧ Gapped (b :: rest)
  | _ => True

/-- Byte ranges `[start, end)` inside a file of `size` bytes. -/
structure ByteRanges (size : Nat) where
  ranges : List (Nat × Nat)
  h_nonempty : ranges ≠ []
  h_within : ∀ r ∈ ranges, r.1 < r.2 ∧ r.2 ≤ size
  h_count : ranges.length ≤ maxRanges
  h_gaps : ranges.length > 1 → Gapped ranges

/-- What to do with a `Range` header. -/
inductive RangeDecision (size : Nat) where
  | full
  | ranges (rs : ByteRanges size)
  | malformed (message : String)
  | unsatisfiable

/-- Merge overlapping or touching ranges of a list sorted by start. -/
def mergeRanges : List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | [r] => [r]
  | a :: b :: rest =>
    if b.1 ≤ a.2 then mergeRanges ((a.1, max a.2 b.2) :: rest) else a :: mergeRanges (b :: rest)
termination_by l => l.length

theorem mergeRanges_head : ∀ (a : Nat × Nat) (rest : List (Nat × Nat)),
    ∃ e rs, mergeRanges (a :: rest) = (a.1, e) :: rs
  | a, [] => ⟨a.2, [], by simp [mergeRanges]⟩
  | a, b :: rest => by
    rw [mergeRanges]
    split
    · obtain ⟨e, rs, h⟩ := mergeRanges_head (a.1, max a.2 b.2) rest
      exact ⟨e, rs, h⟩
    · exact ⟨a.2, _, rfl⟩
termination_by _ rest => rest.length

theorem mergeRanges_within (size : Nat) : ∀ (l : List (Nat × Nat)),
    (∀ r ∈ l, r.1 < r.2 ∧ r.2 ≤ size) → ∀ r ∈ mergeRanges l, r.1 < r.2 ∧ r.2 ≤ size
  | [], _ => by simp [mergeRanges]
  | [x], h => by simpa [mergeRanges] using h
  | a :: b :: rest, h => by
    rw [mergeRanges]
    have ha := h a (by simp)
    have hb := h b (by simp)
    split
    · apply mergeRanges_within size
      intro r hr
      simp only [List.mem_cons] at hr
      rcases hr with rfl | hr
      · constructor <;> simp <;> omega
      · exact h r (by simp [hr])
    · intro r hr
      simp only [List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact ha
      · exact mergeRanges_within size (b :: rest) (fun r hr => h r (by simp_all)) r hr
termination_by l => l.length

theorem mergeRanges_gaps : ∀ (l : List (Nat × Nat)), Gapped (mergeRanges l)
  | [] => by unfold mergeRanges; trivial
  | [x] => by unfold mergeRanges; trivial
  | a :: b :: rest => by
    unfold mergeRanges
    split
    · exact mergeRanges_gaps _
    · rename_i hlt
      obtain ⟨e, rs, he⟩ := mergeRanges_head b rest
      have ih := mergeRanges_gaps (b :: rest)
      rw [he] at ih ⊢
      exact ⟨by simp; omega, ih⟩
termination_by l => l.length

theorem mergeRanges_length : ∀ (l : List (Nat × Nat)), (mergeRanges l).length ≤ l.length
  | [] => by simp [mergeRanges]
  | [x] => by simp [mergeRanges]
  | a :: b :: rest => by
    rw [mergeRanges]
    split
    · have := mergeRanges_length ((a.1, max a.2 b.2) :: rest); simp at this ⊢; omega
    · have := mergeRanges_length (b :: rest); simp at this ⊢; omega
termination_by l => l.length

theorem mergeRanges_ne_nil : ∀ (l : List (Nat × Nat)), l ≠ [] → mergeRanges l ≠ []
  | [], h => absurd rfl h
  | a :: rest, _ => by
    obtain ⟨e, rs, h⟩ := mergeRanges_head a rest
    rw [h]; simp

/-- Lexicographic order on ranges, as Python sorts tuples. -/
def rangeLe (a b : Nat × Nat) : Bool := a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2)

/-- Check the parsed ranges and turn them into byte ranges. -/
def checkRanges (size : Nat) (rs : List (Int × Int)) : RangeDecision size :=
  if hne : rs = [] then .malformed "Range header: range must be requested"
  else if rs.any (fun r => !(0 ≤ r.1 && r.1 < size)) then .unsatisfiable
  else if rs.any (fun r => r.1 ≥ r.2) then .malformed "Range header: start must be less than end"
  else
    let ns := rs.map fun r => (r.1.toNat, r.2.toNat)
    if hw : ∀ r ∈ ns, r.1 < r.2 ∧ r.2 ≤ size then
      if hc : ns.length ≤ maxRanges then
        if h1 : ns.length = 1 then
          .ranges ⟨ns, by simp [ns, hne], hw, hc, fun h => absurd h1 (by omega)⟩
        else
          let ms := mergeRanges (ns.mergeSort rangeLe)
          .ranges ⟨ms,
            mergeRanges_ne_nil _ (by
              intro h
              have := congrArg List.length h
              simp [List.length_mergeSort, ns] at this
              exact hne this),
            mergeRanges_within size _ (fun r hr => hw r ((List.mem_mergeSort).mp hr)),
            Nat.le_trans (mergeRanges_length _) (by simp [List.length_mergeSort]; exact hc),
            fun _ => mergeRanges_gaps (ns.mergeSort rangeLe)⟩
      else .full
    else .unsatisfiable

/-- `_parse_range_header(http_range, file_size)`. -/
def parseRangeHeader (h : String) (size : Nat) : RangeDecision size :=
  match splitFirst '=' h.toList with
  | (_, none) => .malformed "Malformed range header."
  | (units, some r) =>
    if (stripWs units).map asciiLower != "bytes".toList then .malformed "Only support bytes range"
    else
      let parts := splitAll ',' r
      if parts.length > maxRanges then .full
      else checkRanges size (parts.filterMap (parseRangePart size))

/-- `start-last` of one range. -/
def rangePartChars (r : Nat × Nat) : List Char :=
  Keel.Codec.decimal r.1 ++ '-' :: Keel.Codec.decimal (r.2 - 1)

/-- A `Range` header for byte ranges: `bytes=0-99,200-299` (last byte
inclusive, as the header writes it). -/
def printRanges (rs : List (Nat × Nat)) : String :=
  String.ofList ("bytes=".toList ++ List.intercalate [','] (rs.map rangePartChars))

/-- `Content-Range: bytes start-(end-1)/size`. -/
def contentRange (r : Nat × Nat) (size : Nat) : String :=
  s!"bytes {r.1}-{r.2 - 1}/{size}"

end LeanStarlette
