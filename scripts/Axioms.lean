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
  with an unsafe implementation). That includes the printer `deriving Repr`
  generates for a nested inductive: write that instance structurally instead;
* carries `@[implemented_by]` or `@[extern]`, either of which swaps in code the
  kernel never checked.

The only way past the last two checks is an entry in `scripts/gate-allow.txt`
(`<Name> <reason>`), which the gate prints on every run. No entry can excuse an
axiom.

These are checked on the compiled environment, so a doc comment that merely
mentions a banned word is not a false positive. Theorems are reported by axiom
set; every violation is listed by name.
-/

open Lean

instance : MonadEnv (ReaderT Environment Id) where
  getEnv := read
  modifyEnv _ := pure ()

def allowed : List Name := [``propext, ``Quot.sound, ``Classical.choice]

/-- Exceptions the repo has justified, one per line in `scripts/gate-allow.txt`:
`<FullyQualifiedName> <reason>`. Blank lines and `#` comments are ignored. An
entry without a reason is rejected, and so is an entry that matches nothing, so
the list cannot go stale. See STYLE.md section 3: write the definition totally
wherever that is possible, and list it here only when it truly is not. -/
def loadAllowlist : IO (Array (Name × String)) := do
  let path : System.FilePath := "scripts/gate-allow.txt"
  unless ← path.pathExists do return #[]
  let mut out := #[]
  for line in (← IO.FS.lines path) do
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then continue
    match line.splitOn " " with
    | n :: rest => out := out.push (n.toName, " ".intercalate rest |>.trimAscii.toString)
    | [] => pure ()
  return out

unsafe def main (args : List String) : IO UInt32 := do
  let some root := args.head? | IO.eprintln "usage: Axioms.lean <LibraryRoot>"; return 2
  let root := root.toName
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := root }] {} (loadExts := true)
  let mut bad : Array String := #[]
  let mut allowedNotes : Array String := #[]
  let allow ← loadAllowlist
  let mut used : Std.HashSet Name := {}
  for (n, why) in allow do
    if why.isEmpty then bad := bad.push s!"ALLOWLIST: {n} has no reason in scripts/gate-allow.txt"
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
        if let some (_, why) := allow.find? (·.1 == base) then
          used := used.insert base
          allowedNotes := allowedNotes.push s!"allowed partial: {base} ({why})"
        else
          bad := bad.push s!"PARTIAL: {base} is a partial def (write it totally, or justify it in scripts/gate-allow.txt)"
      continue
    if n.isInternal then continue
    let excused := allow.any (·.1 == n)
    if excused then used := used.insert n
    let flag (msg : String) : Array String → Array String := fun b => if excused then b else b.push msg
    if ci.isUnsafe then bad := flag s!"UNSAFE: {n} is unsafe" bad
    if let .defnInfo d := ci then
      if d.safety == .partial then bad := flag s!"PARTIAL: {n} is a partial def" bad
    if (Compiler.implementedByAttr.getParam? env n).isSome then
      bad := flag s!"IMPLEMENTED_BY: {n} has @[implemented_by]" bad
    if isExtern env n then bad := flag s!"EXTERN: {n} has @[extern]" bad
    if excused then allowedNotes := allowedNotes.push s!"allowed: {n} ({(allow.find? (·.1 == n)).map (·.2) |>.getD ""})"
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
  for (n, _) in allow do
    unless used.contains n do bad := bad.push s!"ALLOWLIST: {n} is listed in scripts/gate-allow.txt but matches nothing; remove it"
  let mut printed : Std.HashSet Name := {}
  for (n, why) in allow do
    if used.contains n && !printed.contains n then
      printed := printed.insert n
      IO.println s!"  allowed by scripts/gate-allow.txt: {n} ({why})"
  if bad.isEmpty then
    IO.println "verification gate: clean"
    return 0
  for b in bad do IO.eprintln b
  IO.eprintln s!"verification gate: {bad.size} violation(s)"
  return 1
