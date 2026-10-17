import Lean
/-!
# Axiom hygiene

Run with `lake env lean --run scripts/Axioms.lean <Lib>`.

Walks every theorem in modules under the given library root and collects the
axioms each one depends on. Exits non-zero if any theorem reaches an axiom
outside Lean's own three (`propext`, `Quot.sound`, `Classical.choice`) or is
admitted (`sorryAx`). This is the whole gate; nothing else in CI decides what
counts as proved.
-/

open Lean

instance : MonadEnv (ReaderT Environment Id) where
  getEnv := read
  modifyEnv _ := pure ()

def allowed : List Name := [``propext, ``Quot.sound, ``Classical.choice]

unsafe def main (args : List String) : IO UInt32 := do
  let some root := args.head? | IO.eprintln "usage: Axioms.lean <LibraryRoot>"; return 2
  let root := root.toName
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := root }] {} (loadExts := true)
  let mut bad : Array (Name × Array Name) := #[]
  let mut total := 0
  let mut buckets : Std.HashMap (List Name) Nat := {}
  for (n, ci) in env.constants.map₁.toList do
    let some modIdx := env.getModuleIdxFor? n | continue
    let modName := env.header.moduleNames[modIdx.toNat]!
    unless root.isPrefixOf modName do continue
    unless ci matches .thmInfo _ do continue
    if n.isInternal then continue
    total := total + 1
    let axioms : Array Name := (collectAxioms (m := ReaderT Environment Id) n).run env
    let axioms := axioms.qsort (·.toString < ·.toString)
    buckets := buckets.insert axioms.toList (buckets.getD axioms.toList 0 + 1)
    if axioms.any (fun a => !(allowed.contains a)) then
      bad := bad.push (n, axioms)
  IO.println s!"{total} theorems under {root}"
  for (ax, k) in buckets.toList do
    let label := if ax.isEmpty then "none (fully constructive)" else ", ".intercalate (ax.map toString)
    IO.println s!"  {k}\t{label}"
  if bad.isEmpty then
    IO.println "axiom hygiene: clean"
    return 0
  for (n, ax) in bad do
    IO.eprintln s!"IMPURE: {n} depends on {ax}"
  return 1
