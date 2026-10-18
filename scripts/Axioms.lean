import Lean

/-!
# The verification gate

Run with `lake env lean --run scripts/Axioms.lean <LibraryRoot>`.

Every declaration in a module under the given library root is checked, not only
the theorems, because a proof can hide inside a definition (a refinement
`⟨x, by admit⟩` is a definition). The check fails if any declaration:

* reaches an axiom outside Lean's own `propext`, `Quot.sound` and
  `Classical.choice`. `sorry` and `admit` reach `sorryAx`, and `native_decide`
  and `bv_decide` reach `Lean.ofReduceBool`, so all four are caught here;
* is `unsafe`, or is a `partial def` (Lean compiles one to an opaque constant
  with an unsafe implementation). The one tolerated exception is the printer
  that `deriving Repr` generates for a nested inductive, which is display-only;
  each one is listed;
* carries `@[implemented_by]` or `@[extern]`, either of which swaps in code the
  kernel never checked.

These are checked on the compiled environment, so a doc comment that merely
mentions a banned word is not a false positive. Theorems are reported by axiom
set; every violation is listed by name.
-/

open Lean

instance : MonadEnv (ReaderT Environment Id) where
  getEnv := read
  modifyEnv _ := pure ()

def allowed : List Name := [``propext, ``Quot.sound, ``Classical.choice]

/-- `deriving Repr` on a nested inductive emits `instReprT.repr` as a
`partial def`. It only renders values for display, so it is the one partial
definition the gate tolerates, and it is listed in the output. -/
def isDerivedRepr (n : Name) : Bool :=
  match n with
  | .str (.str _ inst) "repr" => inst.startsWith "instRepr"
  | _ => false

unsafe def main (args : List String) : IO UInt32 := do
  let some root := args.head? | IO.eprintln "usage: Axioms.lean <LibraryRoot>"; return 2
  let root := root.toName
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := root }] {} (loadExts := true)
  let mut bad : Array String := #[]
  let mut allowedNotes : Array String := #[]
  let mut theorems := 0
  let mut decls := 0
  let mut buckets : Std.HashMap (List Name) Nat := {}
  for (n, ci) in env.constants.map₁.toList do
    let some modIdx := env.getModuleIdxFor? n | continue
    let modName := env.header.moduleNames[modIdx.toNat]!
    unless root.isPrefixOf modName do continue
    -- `partial def f` makes `f` an opaque constant implemented by `f._unsafe_rec`.
    -- A definition by well-founded recursion also gets an `_unsafe_rec` twin
    -- for code generation, but `f` stays a checked definition, so only an
    -- opaque base counts as partial.
    if let .str base "_unsafe_rec" := n then
      if let some (.opaqueInfo _) := env.find? base then
        if isDerivedRepr base then
          allowedNotes := allowedNotes.push s!"allowed: {base} (derived Repr printer; display only, never in a specification)"
        else
          bad := bad.push s!"PARTIAL: {base} is a partial def"
      continue
    if n.isInternal then continue
    if ci.isUnsafe then
      bad := bad.push s!"UNSAFE: {n} is unsafe"
    if let .defnInfo d := ci then
      if d.safety == .partial then bad := bad.push s!"PARTIAL: {n} is a partial def"
    if (Compiler.implementedByAttr.getParam? env n).isSome then
      bad := bad.push s!"IMPLEMENTED_BY: {n} has @[implemented_by]"
    if isExtern env n then
      bad := bad.push s!"EXTERN: {n} has @[extern]"
    if ci.isUnsafe then continue
    decls := decls + 1
    let axioms : Array Name := (collectAxioms (m := ReaderT Environment Id) n).run env
    let axioms := axioms.qsort (·.toString < ·.toString)
    if ci matches .thmInfo _ then
      theorems := theorems + 1
      buckets := buckets.insert axioms.toList (buckets.getD axioms.toList 0 + 1)
    let impure := axioms.filter (fun a => !(allowed.contains a))
    unless impure.isEmpty do
      bad := bad.push s!"AXIOM: {n} depends on {impure}"
  IO.println s!"{theorems} theorems, {decls} declarations checked under {root}"
  for (ax, k) in buckets.toList do
    let label := if ax.isEmpty then "none (fully constructive)" else ", ".intercalate (ax.map toString)
    IO.println s!"  {k}\t{label}"
  for a in allowedNotes do IO.println s!"  {a}"
  if bad.isEmpty then
    IO.println "verification gate: clean"
    return 0
  for b in bad do IO.eprintln b
  IO.eprintln s!"verification gate: {bad.size} violation(s)"
  return 1
