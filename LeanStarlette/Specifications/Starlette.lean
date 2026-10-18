import LeanStarlette.APIs.Starlette

/-!
# Specifications: what the router and the responses promise

The headline properties, as `Prop`s over the public functions. Each is
proved in `Proofs/Routing.lean` or `Proofs/Http.lean` and has a slot in
`Proofs/Verified.lean`.
-/

namespace LeanStarlette.Spec

open Keel

/-- The router hands over to the first fully matching route. -/
def RouteFirstMatch : Prop :=
  ∀ (rs : List BaseRoute) (b : Bool) (req : Request) (c : Child),
    Router.resolve rs b req = .found c ↔
      ∃ pre r post, rs = pre ++ r :: post ∧ r.matches req = .full c ∧
        ∀ r' ∈ pre, ¬ (r'.matches req).IsFull

/-- 405 exactly when nothing matches fully and something matches the path,
with `Allow` the union of the partial matches' methods. -/
def PartialIff405 : Prop :=
  ∀ (rs : List BaseRoute) (b : Bool) (req : Request) (allow : List String),
    Router.resolve rs b req = .methodNotAllowed allow ↔
      (∀ r ∈ rs, ¬ (r.matches req).IsFull) ∧ (∃ r ∈ rs, r.matches req = .partial) ∧
        allow = allowOf rs req

/-- `Allow` lists exactly the methods of the partially matching routes. -/
def AllowUnion : Prop :=
  ∀ (rs : List BaseRoute) (req : Request) (m : String),
    m ∈ allowOf rs req ↔ ∃ r ∈ rs, (r.matches req).isPartial = true ∧ m ∈ r.methodsOf

/-- 404 exactly when nothing matches and the slash redirect does not apply. -/
def NoMatch404 : Prop :=
  ∀ (rs : List BaseRoute) (b : Bool) (req : Request),
    Router.resolve rs b req = .notFound ↔
      (∀ r ∈ rs, r.matches req = .none) ∧
        ¬ (b = true ∧ req.routePath ≠ "/" ∧ ∃ r ∈ rs, (r.matches (toggleSlash req)).isNone = false)

/-- `redirect_slashes` redirects exactly when the toggled path would match. -/
def RedirectSlashes : Prop :=
  ∀ (rs : List BaseRoute) (b : Bool) (req : Request) (url : String),
    Router.resolve rs b req = .redirect url ↔
      (∀ r ∈ rs, r.matches req = .none) ∧ b = true ∧ req.routePath ≠ "/" ∧
        (∃ r ∈ rs, (r.matches (toggleSlash req)).isNone = false) ∧
        url = toString (toggleSlash req).url

/-- A route that allows `GET` treats `HEAD` as `GET`. -/
def HeadImpliesGet : Prop :=
  ∀ (r : BaseRoute) (req : Request), r.allows "GET" = true →
    r.matches { req with method := "HEAD" } = r.matches { req with method := "GET" }

/-- Header lookup ignores ASCII case. -/
def HeadersGetCI : Prop :=
  ∀ (l : List (String × String)) (k : String),
    (Headers.ofList l).get? k = (l.find? (fun p => lowerAscii p.1 == lowerAscii k)).map (·.2)

/-- `content-length` is the size of the body sent. -/
def ContentLengthEqBody : Prop :=
  ∀ (c : Content) (s : Nat) (hs : List (String × String)) (mt : Option String) (h : StatusCode.Valid s),
    (Headers.ofList hs).contains "content-length" = false → bodyAllowed s = true →
    (Response.make c s hs mt h).headers.get? "content-length" =
      some (toString (Response.make c s hs mt h).body.size)

/-- 1xx, 204 and 304 responses have no body. -/
def NoBody204304 : Prop :=
  ∀ (r : Response), (r.status_code < 200 ∨ r.status_code = 204 ∨ r.status_code = 304) → r.body.size = 0

/-- `RedirectResponse` is a 307 with `location`. -/
def Redirect307 : Prop :=
  ∀ (url : String), (RedirectResponse url).status_code = 307 ∧
    (RedirectResponse url).headers.get? "location" = some (quote url Responses.redirectSafe)

/-- `JSONResponse`'s body parses back to a finite value. -/
def JsonResponseBody : Prop :=
  ∀ (j : LeanJson.Json), LeanJson.Spec.IntsFit j → j.height ≤ 200 → j.allFinite = true →
    (LeanJson.from_json (JSONResponse j).body).map (·.val) = .ok j

/-- A route's URL for valid captures routes back to them (aligned templates). -/
def CompileMatchUrlPathFor : Prop :=
  ∀ {α : Type} [ToApp α] (p : String) (e : α) (ms : List String) (n : String) {t : PathTemplate},
    PathTemplate.compile p = .ok t → p.startsWith "/" = true → t.Aligned →
    ∀ (v : Args t.pieces), PathTemplate.ArgsValid t.pieces v →
    ∀ (req : Request), req.root_path = "" → (Route p e ms n).allows req.method = true →
      req.path = t.urlFor v →
      ∃ c, (Route p e ms n).matches req = .full c ∧
        c.params.items = req.path_params.items ++ namedParams t.pieces v

/-- A canonical path is the URL of its captures. -/
def UrlPathForMatch : Prop :=
  ∀ (t : PathTemplate) {path : String} {v : Args t.pieces},
    t.match path = some v → t.Canonical path → t.urlFor v = path

end LeanStarlette.Spec
