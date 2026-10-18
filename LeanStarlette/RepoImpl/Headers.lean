import LeanStarlette.DataTypes.Http
import LeanStarlette.RepoImpl.Text
import Std.Data.HashMap

/-!
# RepoImpl: headers

`Headers` and the `MutableHeaders` operations, as functions returning new
headers. Every name is lower-cased on the way in, so every lookup is
case-insensitive (`headers_get_ci`, `Proofs/Headers.lean`).
-/

namespace LeanStarlette

theorem lowerAscii_idem (s : String) : IsLower (lowerAscii s) := by
  unfold IsLower lowerAscii
  simp [String.toList_ofList, List.map_map, Function.comp_def, asciiLower_idem]

namespace Headers

/-- No headers. -/
def empty : Headers := ⟨[], by simp⟩

instance : EmptyCollection Headers := ⟨empty⟩
instance : Inhabited Headers := ⟨empty⟩

/-- `Headers(headers={...})`: names are lower-cased, order kept. -/
def ofList (l : List (String × String)) : Headers :=
  ⟨l.map (fun p => (lowerAscii p.1, p.2)), by
    intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨q, _, rfl⟩ := hp
    exact lowerAscii_idem q.1⟩

/-- `headers.get(key)`: the first value for `key`, any case. -/
def get? (h : Headers) (key : String) : Option String :=
  (h.raw.find? (fun p => p.1 == lowerAscii key)).map (·.2)

/-- `headers.getlist(key)`: every value for `key`, in order. -/
def getlist (h : Headers) (key : String) : List String :=
  (h.raw.filter (fun p => p.1 == lowerAscii key)).map (·.2)

/-- `key in headers`. -/
def contains (h : Headers) (key : String) : Bool := (h.get? key).isSome

/-- `headers.keys()`, `values()`, `items()`. -/
def keys (h : Headers) : List String := h.raw.map (·.1)
def values (h : Headers) : List String := h.raw.map (·.2)
def items (h : Headers) : List (String × String) := h.raw

/-- `dict(headers)`: each name once, with its first value. -/
def dict (h : Headers) : List (String × String) :=
  let first : Std.HashMap String String := h.raw.foldl (fun m p => if m.contains p.1 then m else m.insert p.1 p.2) {}
  (dedupStrings h.keys).map fun k => (k, first.getD k "")

/-- `headers.multi_items()`: every field, in order (`items()` upstream). -/
def multiItems (h : Headers) : List (String × String) := h.raw
abbrev multi_items := @multiItems

/-- `MutableHeaders.append(key, value)`: add a field, keeping duplicates. -/
def append (h : Headers) (key value : String) : Headers :=
  ⟨h.raw ++ [(lowerAscii key, value)], by
    intro p hp
    simp only [List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact h.h_lower p hp
    · exact lowerAscii_idem key⟩

/-- `del headers[key]`: remove every field named `key`. -/
def delete (h : Headers) (key : String) : Headers :=
  ⟨h.raw.filter (fun p => p.1 != lowerAscii key), fun p hp => h.h_lower p ((List.mem_filter.mp hp).1)⟩

/-- Replace the value of the first field named `k` (lower-case), dropping
later ones. -/
def setAux (k v : String) : List (String × String) → List (String × String)
  | [] => []
  | p :: ps => if p.1 == k then (k, v) :: ps.filter (fun q => q.1 != k) else p :: setAux k v ps

/-- `headers[key] = value`: replace the first field named `key` in place and
drop any duplicates, or append it (`MutableHeaders.__setitem__`). -/
def set (h : Headers) (key value : String) : Headers :=
  let k := lowerAscii key
  if h.raw.any (fun p => p.1 == k) then
    ⟨setAux k value h.raw, by
      have hk : IsLower k := lowerAscii_idem key
      have : ∀ (l : List (String × String)), (∀ p ∈ l, IsLower p.1) → ∀ p ∈ setAux k value l, IsLower p.1 := by
        intro l hl
        induction l with
        | nil => simp [setAux]
        | cons q qs ih =>
          intro p hp
          simp only [setAux] at hp
          split at hp
          · simp only [List.mem_cons] at hp
            rcases hp with rfl | hp
            · exact hk
            · exact hl p (List.mem_cons_of_mem _ ((List.mem_filter.mp hp).1))
          · simp only [List.mem_cons] at hp
            rcases hp with rfl | hp
            · exact hl _ (List.mem_cons_self ..)
            · exact ih (fun p hp => hl p (List.mem_cons_of_mem _ hp)) p hp
      exact this h.raw h.h_lower⟩
  else h.append key value

/-- `headers.setdefault(key, value)`. -/
def setdefault (h : Headers) (key value : String) : Headers :=
  if h.contains key then h else h.append key value

/-- `MutableHeaders.update(mapping)`. -/
def update (h : Headers) (other : List (String × String)) : Headers :=
  other.foldl (fun acc p => acc.set p.1 p.2) h

/-- `add_vary_header`. -/
def addVaryHeader (h : Headers) (vary : String) : Headers :=
  match h.get? "vary" with
  | some existing => h.set "vary" (existing ++ ", " ++ vary)
  | none => h.set "vary" vary

/-- `headers["key"]?`, `headers["key"]!`. -/
instance : GetElem? Headers String String (fun h k => (h.get? k).isSome) where
  getElem h k ok := (h.get? k).get ok
  getElem? h k := h.get? k

instance : Repr Headers where
  reprPrec h _ := "Headers(" ++ repr h.raw ++ ")"

end Headers

end LeanStarlette
