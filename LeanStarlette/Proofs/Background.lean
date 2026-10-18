import LeanStarlette.RepoImpl.Background

/-!
# Proofs: background tasks run in order

`BackgroundTasks.run` is `runAll` on the task list: each task starts after
the previous one returns, and an exception from one skips the rest (the
monad's bind). Core Lean v4.35 builds `IO` on `EST` and states no
`LawfulMonad` for it, so this file proves it (`instLawfulMonadEST`); the
order is then proved for `run` in `IO` itself (`background_run_order_io`),
for `runAll` in every lawful monad, and, concretely, in a trace monad where
each task records its index.
-/

namespace LeanStarlette

/-- `EST` (and so `IO`) satisfies the monad laws: its `pure` and `bind` are
ordinary definitions by cases on `EST.Out`, and `map`/`seq` default to
`bind`. -/
instance instLawfulMonadEST (ε σ : Type) : LawfulMonad (EST ε σ) :=
  LawfulMonad.mk'
    (id_map := fun x => by
      funext s
      show EST.bind x (fun a => EST.pure (id a)) s = x s
      simp only [EST.bind, EST.pure, id]
      cases x s <;> rfl)
    (pure_bind := fun a f => by funext s; rfl)
    (bind_assoc := fun x f g => by
      funext s
      show EST.bind (EST.bind x f) g s = EST.bind x (fun a => EST.bind (f a) g) s
      simp only [EST.bind]
      cases x s <;> rfl)

/-- `IO` is a lawful monad. -/
instance instLawfulMonadIO : LawfulMonad IO := inferInstanceAs (LawfulMonad (EST IO.Error IO.RealWorld))

namespace BackgroundTasks

/-- `run` is `runAll` on the tasks, in the order they were added. -/
theorem run_eq (bt : BackgroundTasks) : bt.run = runAll bt.tasks := rfl

/-- `add_task` appends. -/
theorem addTask_tasks (bt : BackgroundTasks) (t : IO Unit) : (bt.addTask t).tasks = bt.tasks ++ [t] := rfl

/-- The first task runs, then the rest. -/
theorem runAll_cons {m : Type → Type} [Monad m] (t : m PUnit) (ts : List (m PUnit)) :
    runAll (t :: ts) = (do t; runAll ts) := by
  simp [runAll]

/-- **`background_run_order`**: in any lawful monad, the tasks run in the
order they were added, a task added last running after all the others. -/
theorem background_run_order {m : Type → Type} [Monad m] [LawfulMonad m] (ts : List (m PUnit))
    (t : m PUnit) : runAll (ts ++ [t]) = (do runAll ts; t) := by
  simp [runAll, List.forM_append]

/-- **`background_run_order` for `IO`**: running the tasks after `add_task t`
runs the earlier tasks, then `t`. -/
theorem background_run_order_io (bt : BackgroundTasks) (t : IO Unit) :
    (bt.addTask t).run = (do bt.run; t) := by
  rw [run_eq, run_eq, addTask_tasks, background_run_order]

/-- A task that records its index. -/
def logTask (i : Nat) : StateM (List Nat) PUnit := modify (· ++ [i])

/-- **Every task runs, once, in order**: tasks that record their index leave
the indices in the order the tasks were added. -/
theorem run_order_trace (is : List Nat) (log : List Nat) :
    ((runAll (is.map logTask)).run log).2 = log ++ is := by
  induction is generalizing log with
  | nil => simp [runAll]; rfl
  | cons i is ih =>
    simp only [List.map_cons, runAll_cons]
    show ((runAll (is.map logTask)).run (log ++ [i])).2 = log ++ i :: is
    rw [ih]; simp

end BackgroundTasks

end LeanStarlette
