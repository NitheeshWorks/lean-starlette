import LeanStarlette.RepoImpl.Applications

/-!
# APIs: `Starlette`, `Route`, `Mount`, `Router`

The constructors a Starlette user writes, with Starlette's names and
defaults:

```lean
def homepage (request : Request) : IO Response :=
  return JSONResponse (json% {"hello": "world"})

def app := Starlette (routes := [Route "/" homepage])
```

Each returns its value with its invariant in the type: a `Route` that
allows `GET` allows `HEAD` (`BaseRoute.route`'s `h_head`).
-/

namespace LeanStarlette

namespace Routing

/-- `Route(path, endpoint, methods=["GET"], name=...)`. Methods are
upper-cased, and `HEAD` is added to `GET`; an empty list allows every
method, as upstream's empty set does. A path that does not start with `/`,
names an unknown convertor or repeats a parameter never matches, and
`Application.checkRoutes` reports it. Lean functions have no runtime name,
so `name` defaults to `""` rather than the endpoint's `__name__`. -/
def Route {α : Type} [ToApp α] (path : String) (endpoint : α) (methods : List String := ["GET"])
    (name : String := "") : BaseRoute :=
  let (t, err) := compileOr path
  let err := if path.startsWith "/" then err else some "Routed paths must start with '/'"
  let ms := normaliseMethods methods
  .route path { path := t, methods := if ms.isEmpty then none else some ms, endpoint := ToApp.toApp endpoint }
    name err (by
      intro ms' h hg
      split at h
      · cases h
      · cases h; exact head_mem_normaliseMethods methods hg)

/-- `Mount(path, routes=[...])` or `Mount(path, app=...)`: everything under
`path` goes to the routes (or app), with the prefix moved into `root_path`. -/
def Mount (path : String) (routes : List BaseRoute := []) (app : Option App := none)
    (name : Option String := none) : BaseRoute :=
  let p := String.ofList (path.toList.reverse.dropWhile (· = '/')).reverse
  let (t, err) := compileOr (p ++ "/{path:path}")
  let err := if path.isEmpty || path.startsWith "/" then err else some "Routed paths must start with '/'"
  .mount p t routes (app.getD (routerApp routes)) name err

/-- `Router(routes, redirect_slashes=True)`, as an application. -/
def Router (routes : List BaseRoute := []) (redirect_slashes : Bool := true) : Application :=
  { routes, redirect_slashes }

/-- `Starlette(debug=False, routes=None, middleware=None,
exception_handlers=None, max_body_size=None)`. -/
def Starlette (debug : Bool := false) (routes : List BaseRoute := []) (middleware : List Middleware := [])
    (exception_handlers : List (ExceptionKey × ExceptionHandler) := []) (max_body_size : Option Nat := none) :
    Application :=
  { routes, debug, middleware, exception_handlers, max_body_size }

end Routing

export Routing (Route Mount Router Starlette)

/-- The compile errors of an application's routes, with their paths. -/
def Application.checkRoutes (a : Application) : List (String × String) :=
  go a.routes
where
  go : List BaseRoute → List (String × String)
    | [] => []
    | .route p _ _ (some e) _ :: rs => (p, e) :: go rs
    | .route _ _ _ none _ :: rs => go rs
    | .mount p _ inner _ _ err :: rs =>
      (match err with | some e => [(p, e)] | none => []) ++ go inner ++ go rs

end LeanStarlette
