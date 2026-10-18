import LeanStarlette.RepoImpl.Exceptions

/-!
# RepoImpl: routes, mounts and the router

`starlette/routing.py` on top of `Keel.Route`: Keel supplies the path
templates, their greedy matching, the convertors and first-match dispatch;
this module adds what is Starlette's own.

* `BaseRoute.matches` is `Route.matches` / `Mount.matches`: a three-way
  `Keel.Match` whose full result says how to continue (`Child`).
* `Router.resolve` is the decision `Router.app` makes: the first full match,
  else `405` with `Allow`, else a `redirect_slashes` redirect, else `404`.
  `Allow` lists the methods of every partially matching route (UP-027).
* `routerApp` runs the decision; `BaseRoute.urlPathFor` is `url_path_for`
  through routes and mounts.
-/

namespace LeanStarlette

open Keel

/-! ## Endpoints -/

/-- What can be a route endpoint: an `App`, or a function from the request
to an `IO` response or a plain response (Starlette accepts sync and async
functions alike). -/
class ToApp (α : Type) where
  toApp : α → App

instance : ToApp App := ⟨id⟩
instance : ToApp (Request → IO Response) := ⟨fun f r => liftM (f r)⟩
instance : ToApp (Request → Response) := ⟨fun f r => pure (f r)⟩
instance : ToApp (AppM Response) := ⟨fun m _ => m⟩
instance : ToApp (IO Response) := ⟨fun m _ => liftM m⟩
instance : ToApp Response := ⟨fun r _ => pure r⟩

/-! ## Compiled routes -/

/-- Upper-case ASCII (`method.upper()`). -/
def upperAscii (s : String) : String :=
  String.ofList (s.toList.map fun c => if 'a' ≤ c && c ≤ 'z' then Char.ofNat (c.toNat - 32) else c)

/-- Route methods as Starlette normalises them: upper-cased, each once, and
`HEAD` added when `GET` is present. -/
def normaliseMethods (ms : List String) : List String :=
  let ms := dedup (ms.map upperAscii)
  if ms.contains "GET" && !ms.contains "HEAD" then ms ++ ["HEAD"] else ms

theorem head_mem_normaliseMethods (ms : List String) :
    "GET" ∈ normaliseMethods ms → "HEAD" ∈ normaliseMethods ms := by
  unfold normaliseMethods
  simp only
  split
  · intro _; simp
  · rename_i h
    intro hg
    simp only [Bool.and_eq_true, Bool.not_eq_true', not_and, Bool.not_eq_false] at h
    simpa using h (List.contains_iff_mem.mpr hg)

/-- A template that never matches, for a path that failed to compile. -/
def emptyTemplate : PathTemplate := ⟨[.lit ['\x00']]⟩

/-- The template of a path, or the compile error. -/
def compileOr (path : String) : PathTemplate × Option String :=
  match PathTemplate.compile path with
  | .ok t => (t, none)
  | .error e => (emptyTemplate, some e)

/-- The converted captures of a match, by name, as `PathParam`s. -/
def namedParams : (ps : List Piece) → Args ps → List (String × PathParam)
  | [], _ => []
  | .lit _ :: ps, v => namedParams ps v
  | .cap n c :: ps, (x, v) => (n, ⟨c.name, String.ofList (c.render x)⟩) :: namedParams ps v

/-- Where a full match continues: the request's new path parameters and
root path, and the application to run. -/
structure Child where
  params : PathParams
  root_path : String
  handler : App

namespace BaseRoute

/-- The methods a route allows (empty for a mount, which allows all). -/
def methodsOf : BaseRoute → List String
  | .route _ r _ _ _ _ => r.methods.getD []
  | .mount .. => []

/-- Whether a route accepts a method (a mount, or a route without methods,
accepts all). -/
def allows (r : BaseRoute) (m : String) : Bool :=
  match r with
  | .route _ rt _ _ _ _ => rt.allows m
  | .mount .. => true

/-- Whether the route adds `HEAD` to `GET`: `Route` does, `RouteExact` does
not; a mount has no method set of its own. -/
def autoHead : BaseRoute → Bool
  | .route _ _ _ _ ah _ => ah
  | .mount .. => true

/-- `name` of a route (a mount's may be absent). -/
def nameOf : BaseRoute → Option String
  | .route _ _ n _ _ _ => some n
  | .mount _ _ _ _ n _ => n

/-- `route.matches(scope)`. A `Route` checks the template and then the
method; a `Mount` checks `path + "/{path:path}"` and passes the rest of the
path down, moving the matched prefix into `root_path`. -/
def «matches» (req : Request) : BaseRoute → Keel.Match Child
  | .route _ r _ err _ _ =>
    if err.isSome then .none else
    match r.matches req.method req.routePath with
    | .full v => .full ⟨⟨req.path_params.items ++ namedParams r.path.pieces v⟩, req.root_path, r.endpoint⟩
    | .partial => .partial
    | .none => .none
  | .mount _ t _ handler _ err =>
    if err.isSome then .none else
    match t.match req.routePath with
    | some v =>
      let ps := namedParams t.pieces v
      let rest := "/" ++ ((ps.lookup "path").map (·.text)).getD ""
      let rp := req.routePath
      let matched := String.ofList (rp.toList.take (rp.length - rest.length))
      .full ⟨⟨req.path_params.items ++ ps.filter (·.1 != "path")⟩, req.root_path ++ matched, handler⟩
    | none => .none

end BaseRoute

/-! ## The router decision -/

/-- What `Router.app` does with a request. -/
inductive Resolution where
  /-- Hand over to the first fully matching route. -/
  | found (child : Child)
  /-- `405 Method Not Allowed`, with these methods in `Allow`. -/
  | methodNotAllowed (allow : List String)
  /-- `redirect_slashes`: `307` to this URL. -/
  | redirect (url : String)
  /-- `404 Not Found`. -/
  | notFound

/-- Whether a match is none. -/
def _root_.Keel.Match.isNone {β : Type} : Keel.Match β → Bool
  | .none => true
  | _ => false

/-- `Allow`: the methods of every route that matched the path but not the
method, each once, in route order. -/
def allowOf (routes : List BaseRoute) (req : Request) : List String :=
  dedup (routes.flatMap fun r => if (r.matches req).isPartial then r.methodsOf else [])

/-- The request `redirect_slashes` tries: the path with its trailing slashes
removed, or with one added. -/
def toggleSlash (req : Request) : Request :=
  if req.routePath.endsWith "/" then
    { req with path := String.ofList (req.path.toList.reverse.dropWhile (· = '/')).reverse }
  else { req with path := req.path ++ "/" }

/-- **`Router.app`'s decision**, for a request against a list of routes. The
`Allow` list of a `405` follows `policy` (Keel's `AllowPolicy`): upstream
lists the first partial route's methods (`.firstPartial`); lean-starlette
selects `.unionOfPartials` (see `routerApp` and UP-027). -/
def Router.resolve (routes : List BaseRoute) (redirect_slashes : Bool) (req : Request)
    (policy : Keel.AllowPolicy) : Resolution :=
  match dispatch (β := fun _ => Child) (BaseRoute.matches req) routes with
  | .found _ c => .found c
  | .partial r => .methodNotAllowed
      (match policy with
       | .firstPartial => r.methodsOf
       | .unionOfPartials => allowOf routes req)
  | .none =>
    if redirect_slashes && req.routePath != "/" &&
        routes.any (fun r => !((r.matches (toggleSlash req)).isNone)) then
      .redirect (toString (toggleSlash req).url)
    else .notFound

/-- The `HTTPException` for a 405 with its `Allow` header. -/
def methodNotAllowed (allow : List String) : Exception :=
  HTTPException 405 (headers := [("Allow", ", ".intercalate allow)])

/-- **`Router.app`**: run the decision. Inside an application a 404 or 405
is raised as an `HTTPException` for the exception middleware to render.

The `Allow` policy is selected here, explicitly: `.unionOfPartials`, every
method of every route that matches the path, once each, in declaration order.
Upstream (Starlette 1.8.0) lists only the first partial route's methods, which
leaves out methods other routes on the same path accept, contrary to RFC 9110
15.5.6 (UP-027). -/
def routerApp (routes : List BaseRoute) (redirect_slashes : Bool := true) : App := fun req =>
  match Router.resolve routes redirect_slashes req (policy := .unionOfPartials) with
  | .found c => c.handler { req with path_params := c.params, root_path := c.root_path }
  | .methodNotAllowed allow => throw (methodNotAllowed allow)
  | .redirect url => pure (RedirectResponse url)
  | .notFound => throw (HTTPException 404)

/-! ## url_path_for -/

/-- Values for a template's captures from their texts: each is parsed by its
convertor and must render to text the convertor accepts (upstream's
`to_string` assertions: no empty or `/`-containing `str`). -/
def argsOf (kw : List (String × String)) : (ps : List Piece) → Option (Args ps)
  | [] => some ()
  | .lit _ :: ps => argsOf kw ps
  | .cap n c :: ps => do
    let t ← kw.lookup n
    let x ← c.parse t.toList
    if c.accepts (c.render x) then
      let v ← argsOf kw ps
      pure (x, v)
    else none

/-- `replace_params` with `url_path_for`'s check that the names are exactly
the template's. -/
def renderTemplate (t : PathTemplate) (kw : List (String × String)) : Option String :=
  let names := PathTemplate.names t.pieces
  if kw.all (fun p => names.contains p.1) && names.all (fun n => (kw.lookup n).isSome) then
    (argsOf kw t.pieces).map t.urlFor
  else none

/-- `name` with its mount prefix removed: `"users:user"` under the mount
`users` is `"user"`. -/
def stripMountName (mname : Option String) (name : String) : Option String :=
  match mname with
  | none => some name
  | some m => if name.startsWith (m ++ ":") then some (name.drop (m.length + 1)).toString else none

mutual
/-- `route.url_path_for(name, **path_params)`. -/
def BaseRoute.urlPathFor : BaseRoute → String → List (String × String) → Option URLPath
  | .route _ r rname err _ _, name, kw =>
    if err.isSome || name != rname then none
    else (renderTemplate r.path kw).map (URLPath.ofPath · "http")
  | .mount _ t routes _ mname err, name, kw =>
    if err.isSome then none else
    let own : Option URLPath :=
      if mname == some name && (kw.lookup "path").isSome then
        let kw' := kw.map fun p => if p.1 == "path" then (p.1, String.ofList (p.2.toList.dropWhile (· = '/'))) else p
        (renderTemplate t kw').map (URLPath.ofPath ·)
      else none
    match own with
    | some u => some u
    | none =>
      match stripMountName mname name with
      | none => none
      | some rest =>
        let names := PathTemplate.names t.pieces
        let own := kw.filter fun p => names.contains p.1 && p.1 != "path"
        let others := kw.filter fun p => !names.contains p.1
        match renderTemplate t (own ++ [("path", "")]) with
        | none => none
        | some pfx =>
          let pfx := String.ofList (pfx.toList.reverse.dropWhile (· = '/')).reverse
          let childKw := match kw.lookup "path" with
            | some p => others ++ [("path", p)]
            | none => others
          (urlPathForList routes rest childKw).map fun u => URLPath.ofPath (pfx ++ u.path) u.protocol
/-- `Router.url_path_for`: the first route that can build the URL. -/
def urlPathForList : List BaseRoute → String → List (String × String) → Option URLPath
  | [], _, _ => none
  | r :: rs, name, kw =>
    match r.urlPathFor name kw with
    | some u => some u
    | none => urlPathForList rs name kw
end

end LeanStarlette
