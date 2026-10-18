import LeanStarlette.APIs.Starlette
import LeanStarlette.APIs.Forms

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
  ∀ (rs : List BaseRoute) (b : Bool) (req : Request) (p : AllowPolicy) (c : Child),
    Router.resolve rs b req p = .found c ↔
      ∃ pre r post, rs = pre ++ r :: post ∧ r.matches req = .full c ∧
        ∀ r' ∈ pre, ¬ (r'.matches req).IsFull

/-- 405 exactly when nothing matches fully and something matches the path,
with `Allow` the union of the partial matches' methods. -/
def PartialIff405 : Prop :=
  ∀ (rs : List BaseRoute) (b : Bool) (req : Request) (allow : List String),
    Router.resolve rs b req .unionOfPartials = .methodNotAllowed allow ↔
      (∀ r ∈ rs, ¬ (r.matches req).IsFull) ∧ (∃ r ∈ rs, r.matches req = .partial) ∧
        allow = allowOf rs req

/-- `Allow` lists exactly the methods of the partially matching routes. -/
def AllowUnion : Prop :=
  ∀ (rs : List BaseRoute) (req : Request) (m : String),
    m ∈ allowOf rs req ↔ ∃ r ∈ rs, (r.matches req).isPartial = true ∧ m ∈ r.methodsOf

/-- 404 exactly when nothing matches and the slash redirect does not apply. -/
def NoMatch404 : Prop :=
  ∀ (rs : List BaseRoute) (b : Bool) (req : Request) (p : AllowPolicy),
    Router.resolve rs b req p = .notFound ↔
      (∀ r ∈ rs, r.matches req = .none) ∧
        ¬ (b = true ∧ req.routePath ≠ "/" ∧ ∃ r ∈ rs, (r.matches (toggleSlash req)).isNone = false)

/-- `redirect_slashes` redirects exactly when the toggled path would match. -/
def RedirectSlashes : Prop :=
  ∀ (rs : List BaseRoute) (b : Bool) (req : Request) (p : AllowPolicy) (url : String),
    Router.resolve rs b req p = .redirect url ↔
      (∀ r ∈ rs, r.matches req = .none) ∧ b = true ∧ req.routePath ≠ "/" ∧
        (∃ r ∈ rs, (r.matches (toggleSlash req)).isNone = false) ∧
        url = toString (toggleSlash req).url

/-- A route that allows `GET` treats `HEAD` as `GET`. -/
def HeadImpliesGet : Prop :=
  ∀ {α : Type} [ToApp α] (p : String) (e : α) (ms : List String) (n : String) (req : Request),
    (Route p e ms n).allows "GET" = true →
    (Route p e ms n).matches { req with method := "HEAD" } =
      (Route p e ms n).matches { req with method := "GET" }

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
  ∀ (j : LeanJson.Json), LeanJson.Spec.IntsFit j → LeanJson.Spec.KeysUnique j → j.height ≤ 200 →
    j.allFinite = true →
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

/-- Background tasks run in the order they were added (in every lawful monad;
`BackgroundTasks.run` is `runAll` at `IO`). -/
def BackgroundRunOrder : Prop :=
  ∀ {m : Type → Type} [Monad m] [LawfulMonad m] (ts : List (m PUnit)) (t : m PUnit),
    BackgroundTasks.runAll (ts ++ [t]) = (do BackgroundTasks.runAll ts; t)

/-- `BackgroundTasks.run` in `IO`: a task added last runs after the others. -/
def BackgroundRunOrderIO : Prop :=
  ∀ (bt : BackgroundTasks) (t : IO Unit), (bt.addTask t).run = (do bt.run; t)

/-- A printed `Range` header parses back to its byte ranges. -/
def RangeParsePrint : Prop :=
  ∀ (size : Nat) (rs : ByteRanges size), size ≤ maxPrintable →
    ∃ rs', parseRangeHeader (printRanges rs.ranges) size = .ranges rs' ∧ rs'.ranges = rs.ranges

/-- Every parsed byte range lies inside the file. -/
def RangeWithin : Prop :=
  ∀ (h : String) (size : Nat) (rs : ByteRanges size), parseRangeHeader h size = .ranges rs →
    ∀ r ∈ rs.ranges, r.1 < r.2 ∧ r.2 ≤ size

/-- With a non-empty `If-None-Match`, a static file is 304 iff it lists the
file's ETag or is `*`. -/
def Etag304Iff : Prop :=
  ∀ (path : String) (size : Nat) (mtimeNs : Int) (req : Headers) (inm : String),
    req.get? "if-none-match" = some inm → inm ≠ "" →
    ((staticFileResponse path size mtimeNs req).status_code = 304 ↔
      (String.ofList (stripWs inm.toList) = "*" ∨ fileETag size mtimeNs ∈ ifNoneMatchTags inm))

/-- A served static path is the directory followed by plain entry names. -/
def ServedPathInside : Prop :=
  ∀ (dir p : String) (segs : List String), staticSegments p = some segs →
    joinUnder dir segs = dir ++ String.join (segs.map ("/" ++ ·)) ∧
      ∀ s ∈ segs, s.isEmpty = false ∧ s ≠ "." ∧ s ≠ ".." ∧
        s.contains '/' = false ∧ (System.Platform.isWindows && s.contains '\\') = false ∧
        s.contains '\x00' = false

/-- Form parse agrees with lean-multipart: the items `request.form()` builds
on are the decoding of the raw form lean-multipart's Starlette parser
returned (refined by its `UrlencodedWithinLimits` / `MultipartWithinLimits`). -/
def FormParseAgrees : Prop :=
  ∀ (lim : LeanMultipart.FormLimits) (ct : Option String) (body : ByteArray) (items : List (String × FormItem)),
    formItems lim ct body = .ok items →
      ∃ r, parseRawForm lim ct body = .ok r ∧ items = r.val.decode

/-- Limits enforced: an accepted form has at most `max_files` files and
`max_fields` text fields, and its raw parts meet lean-multipart's limits
(each text part within `max_part_size`). -/
def FormLimitsEnforced : Prop :=
  ∀ (lim : LeanMultipart.FormLimits) (ct : Option String) (body : ByteArray) (items : List (String × FormItem)),
    formItems lim ct body = .ok items →
      FormItemsWithinLimits lim items ∧ ∃ r : RawForm, r.WithinLimits lim ∧ items = r.decode

/-- A rejected form is `HTTPException(400)` with Starlette's message. -/
def FormError400 : Prop :=
  ∀ (r : Request) (max_files max_fields max_part_size : Nat) (e : LeanMultipart.LimitError),
    formItems { maxFiles := max_files, maxFields := max_fields, maxPartSize := max_part_size }
      (r.headers.get? "content-type") r.bodyBytes = .error e →
    r.form max_files max_fields max_part_size = throw (HTTPException 400 (detail := some (formErrorMessage e)))

end LeanStarlette.Spec
