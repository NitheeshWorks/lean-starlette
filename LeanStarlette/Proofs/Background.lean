import LeanStarlette.RepoImpl.Background

/-!
# Proofs: background tasks run in order

`BackgroundTasks.run` is `runAll` on the task list: each task starts after
the previous one returns, and an exception from one skips the rest (the
monad's bind). Core Lean has no `LawfulMonad IO` instance, so the order is
proved for `runAll` in every lawful monad, and, concretely, in a trace monad
where each task records its index.
-/

namespace LeanStarlette.BackgroundTasks

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

end LeanStarlette.BackgroundTasks
