import LeanStarlette.DataTypes.Http

/-!
# RepoImpl: background tasks

`starlette/background.py`. A task is an `IO Unit` (Python's
`BackgroundTask(func, *args)` is the closure `func args`). `run` runs them
in order, each after the previous one finishes, and stops at the first that
throws (`background_run_order`, `Proofs/Background.lean`).
-/

namespace LeanStarlette

/-- `BackgroundTask(func, *args, **kwargs)`: one task. -/
def BackgroundTask (task : IO Unit) : BackgroundTasks := ⟨[task]⟩

namespace BackgroundTasks

/-- `BackgroundTasks(tasks=None)`. -/
def new (tasks : List (IO Unit) := []) : BackgroundTasks := ⟨tasks⟩

/-- `tasks.add_task(func, *args)`. -/
def addTask (bt : BackgroundTasks) (task : IO Unit) : BackgroundTasks := ⟨bt.tasks ++ [task]⟩
abbrev add_task := @addTask

/-- Run actions in sequence, in any monad: the code `run` executes, stated
generically so its order is a theorem for every lawful monad (core Lean has
no `LawfulMonad IO` instance). -/
def runAll {m : Type → Type} [Monad m] (ts : List (m PUnit)) : m PUnit := ts.forM id

/-- `await tasks()`: run every task, in order. -/
def run (bt : BackgroundTasks) : IO Unit := runAll bt.tasks

end BackgroundTasks

end LeanStarlette
