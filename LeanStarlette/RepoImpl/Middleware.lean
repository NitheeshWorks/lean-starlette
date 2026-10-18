import LeanStarlette.RepoImpl.Applications
import LeanStarlette.RepoImpl.PyRe

/-!
# RepoImpl: middleware (`starlette/middleware/`)

A middleware is an `App` around an `App` (`Middleware`); the application's
list is applied first-outermost (`middlewareStack`). Each upstream
middleware is a function with upstream's options and defaults, returning a
`Middleware`, so `Starlette (middleware := [Middleware CORSMiddleware
(allow_origins := ["*"])])` reads as upstream's
`Starlette(middleware=[Middleware(CORSMiddleware, allow_origins=["*"])])`.

The decisions are pure functions of the request (and, for CORS, of the
response's headers): `trustedHostDecision`, `httpsRedirectURL`,
`CORSConfig.preflight`, `CORSConfig.simpleHeaders`. The theorems are about
them (`Proofs/Middleware.lean`).
-/

namespace LeanStarlette

/-! ## The stack -/

/-- `BaseHTTPMiddleware(app, dispatch)`: `dispatch(request, call_next)`,
where `call_next` runs the rest of the stack. -/
def BaseHTTPMiddleware (dispatch : Request → (Request → AppM Response) → AppM Response) : Middleware :=
  fun app req => dispatch req app

/-- `MutableHeaders.add_vary_header`. -/
def addVary (h : Headers) (v : String) : Headers :=
  match h.get? "vary" with
  | some e => h.set "vary" (e ++ ", " ++ v)
  | none => h.set "vary" v

/-! ## TrustedHostMiddleware -/

/-- Upstream's assertion on a host pattern (`ENFORCE_DOMAIN_WILDCARD`): a `*`
only as the first character, and then as `*.` (or the lone `*`). -/
def ValidHostPattern (p : String) : Prop :=
  '*' ∉ p.toList.drop 1 ∧ (p.toList.head? = some '*' → p ≠ "*" → p.toList.take 2 = ['*', '.'])

instance (p : String) : Decidable (ValidHostPattern p) := by unfold ValidHostPattern; infer_instance

/-- Whether a host matches a pattern: equal, or under a `*.` wildcard (upstream's
`host == pattern or (pattern.startswith("*") and host.endswith(pattern[1:]))`). -/
def hostMatches (host pattern : String) : Bool :=
  host == pattern || (pattern.startsWith "*" && host.endsWith (pattern.drop 1).toString)

/-- What `TrustedHostMiddleware` does with a request. -/
inductive HostDecision where
  | allow
  /-- Redirect to the `www.` host (`www_redirect`). -/
  | redirect (url : String)
  | reject
  deriving DecidableEq, Repr

/-- `TrustedHostMiddleware.__call__`'s decision. -/
def trustedHostDecision (allowedHosts : List String) (wwwRedirect : Bool) (r : Request) : HostDecision :=
  if allowedHosts.contains "*" then .allow else
  match (r.headers.get? "host").bind parseHostHeader with
  | none => .reject
  | some (host, _) =>
    if allowedHosts.any (hostMatches host) then .allow
    else if wwwRedirect && allowedHosts.contains ("www." ++ host) then
      let u := r.url
      .redirect (toString { u with netloc := "www." ++ u.netloc })
    else .reject

/-- **`TrustedHostMiddleware(app, allowed_hosts=["*"], www_redirect=True)`**.
The patterns are checked when the middleware is built (`by decide +kernel` for a
literal), where upstream asserts. -/
def TrustedHostMiddleware (allowed_hosts : List String := ["*"]) (www_redirect : Bool := true)
    (_h : ∀ p ∈ allowed_hosts, ValidHostPattern p := by decide +kernel) : Middleware := fun app req =>
  match trustedHostDecision allowed_hosts www_redirect req with
  | .allow => app req
  | .redirect url => pure (RedirectResponse url)
  | .reject => pure (PlainTextResponse "Invalid host header" (status_code := 400))

/-! ## HTTPSRedirectMiddleware -/

/-- `url.port`: the port in the authority, if it has digits. -/
def URL.port (u : URL) : Option Nat :=
  let hostport := match splitFirst '@' u.netloc.toList.reverse with
    | (h, some _) => h.reverse
    | (h, none) => h.reverse
  let after := match hostport with
    | '[' :: r => match splitFirst ']' r with | (_, some rest) => rest | _ => []
    | r => r.dropWhile (· ≠ ':')
  match after with
  | ':' :: ds => if !ds.isEmpty && ds.all isDigitChar then some (ofDigits ds) else none
  | _ => none

/-- Where `HTTPSRedirectMiddleware` sends a plain-`http`/`ws` request: the
same URL with `https`/`wss`, the port dropped when it is 80 or 443; `none`
when the URL has no authority (a 400). -/
def httpsRedirectURL (r : Request) : Option URL :=
  let u := r.url
  if u.netloc.isEmpty then none else
  let scheme := if u.scheme == "ws" then "wss" else "https"
  let netloc := if u.port == some 80 || u.port == some 443 then (u.hostname.getD "") else u.netloc
  some { u with scheme, netloc }

/-- **`HTTPSRedirectMiddleware(app)`**: a `307` to the `https` URL for a plain
`http` request, else the application. -/
def HTTPSRedirectMiddleware : Middleware := fun app req =>
  if req.scheme == "http" || req.scheme == "ws" then
    match httpsRedirectURL req with
    | some u => pure (RedirectResponse (toString u) (status_code := 307))
    | none => pure (PlainTextResponse "Invalid host header" (status_code := 400))
  else app req

/-! ## CORSMiddleware -/

/-- `ALL_METHODS`. -/
def corsAllMethods : List String := ["DELETE", "GET", "HEAD", "OPTIONS", "PATCH", "POST", "PUT", "QUERY"]

/-- `SAFELISTED_HEADERS`. -/
def corsSafelisted : List String := ["Accept", "Accept-Language", "Content-Language", "Content-Type"]

/-- A sorted copy (insertion sort on strings; header lists are short). -/
def sortStrings (l : List String) : List String :=
  l.foldr (fun x acc => (acc.filter (· < x)) ++ [x] ++ (acc.filter (fun y => !(y < x)))) []

/-- `CORSMiddleware`'s state after `__init__`. -/
structure CORSConfig where
  allowOrigins : List String
  allowMethods : List String
  /-- Lower-cased: the safelisted headers and `allow_headers`, sorted. -/
  allowHeaders : List String
  allowAllOrigins : Bool
  allowAllHeaders : Bool
  allowCredentials : Bool
  /-- `allow_origin_regex`, compiled for `re.fullmatch`. -/
  allowOriginRegex : Option (Keel.Regex.Matcher PyRe.K) := none
  allowPrivateNetwork : Bool
  preflightExplicitAllowOrigin : Bool
  simpleHeaders : List (String × String)
  preflightHeaders : List (String × String)

/-- `CORSMiddleware.__init__`. -/
def corsConfig (allow_origins : List String := []) (allow_methods : List String := ["GET"])
    (allow_headers : List String := []) (allow_credentials : Bool := false)
    (allow_origin_regex : Option PyRe.Pattern := none)
    (allow_private_network : Bool := false) (expose_headers : List String := [])
    (max_age : Nat := 600) : CORSConfig :=
  let allowMethods := if allow_methods.contains "*" then corsAllMethods else allow_methods
  let allowAllOrigins := allow_origins.contains "*"
  let allowAllHeaders := allow_headers.contains "*"
  let explicit := !allowAllOrigins || allow_credentials
  let simple := (if allowAllOrigins then [("Access-Control-Allow-Origin", "*")] else []) ++
    (if allow_credentials then [("Access-Control-Allow-Credentials", "true")] else []) ++
    (if expose_headers.isEmpty then [] else [("Access-Control-Expose-Headers", ", ".intercalate expose_headers)])
  let headersSorted := sortStrings (dedupStrings (corsSafelisted ++ allow_headers))
  let preflight := [("Vary", "Origin, Access-Control-Request-Method, Access-Control-Request-Headers, Access-Control-Request-Private-Network")] ++
    (if explicit then [] else [("Access-Control-Allow-Origin", "*")]) ++
    [("Access-Control-Allow-Methods", ", ".intercalate allowMethods), ("Access-Control-Max-Age", toString max_age)] ++
    (if !headersSorted.isEmpty && !allowAllHeaders then [("Access-Control-Allow-Headers", ", ".intercalate headersSorted)] else []) ++
    (if allow_credentials then [("Access-Control-Allow-Credentials", "true")] else [])
  { allowOrigins := allow_origins, allowMethods, allowHeaders := headersSorted.map lowerAscii,
    allowAllOrigins, allowAllHeaders, allowCredentials := allow_credentials,
    allowOriginRegex := allow_origin_regex.map (·.re.compile .full),
    allowPrivateNetwork := allow_private_network, preflightExplicitAllowOrigin := explicit,
    simpleHeaders := simple, preflightHeaders := preflight }

namespace CORSConfig

/-- `is_allowed_origin`. -/
def isAllowedOrigin (c : CORSConfig) (origin : String) : Bool :=
  c.allowAllOrigins || (c.allowOriginRegex.map (·.test origin)).getD false || c.allowOrigins.contains origin

/-- Whether every requested header is allowed (`allow_headers`, any case,
spaces trimmed). -/
def headersAllowed (c : CORSConfig) (requested : String) : Bool :=
  (requested.splitOn ",").all fun h => c.allowHeaders.contains (lowerAscii (String.ofList (stripWs h.toList)))

/-- What a preflight fails on, in upstream's order. -/
def preflightFailures (c : CORSConfig) (origin method : String) (requestedHeaders privateNetwork : Option String) :
    List String :=
  (if c.isAllowedOrigin origin then [] else ["origin"]) ++
  (if c.allowMethods.contains method then [] else ["method"]) ++
  (match requestedHeaders with
    | some hs => if c.allowAllHeaders || c.headersAllowed hs then [] else ["headers"]
    | none => []) ++
  (match privateNetwork with
    | some _ => if c.allowPrivateNetwork then [] else ["private-network"]
    | none => [])

/-- `preflight_response`: `200 OK`, or `400` naming what was disallowed,
with the CORS headers. -/
def preflight (c : CORSConfig) (h : Headers) : Response :=
  let origin := (h.get? "origin").getD ""
  let method := (h.get? "access-control-request-method").getD ""
  let reqHeaders := h.get? "access-control-request-headers"
  let privateNet := h.get? "access-control-request-private-network"
  let hs := Headers.ofList c.preflightHeaders
  let hs := if c.isAllowedOrigin origin && c.preflightExplicitAllowOrigin then hs.set "Access-Control-Allow-Origin" origin else hs
  let hs := match reqHeaders with
    | some r => if c.allowAllHeaders then hs.set "Access-Control-Allow-Headers" r else hs
    | none => hs
  let hs := if privateNet.isSome && c.allowPrivateNetwork then hs.set "Access-Control-Allow-Private-Network" "true" else hs
  match c.preflightFailures origin method reqHeaders privateNet with
  | [] => PlainTextResponse "OK" (headers := hs.raw)
  | fs => PlainTextResponse ("Disallowed CORS " ++ ", ".intercalate fs) (status_code := 400) (headers := hs.raw)

/-- `allow_explicit_origin`. -/
def allowExplicitOrigin (h : Headers) (origin : String) : Headers :=
  let h := h.set "Access-Control-Allow-Origin" origin
  h.set "Vary" (", ".intercalate (h.getlist "Vary" ++ ["Origin"]))

/-- `CORSMiddleware.send`: the headers of a non-preflight response. -/
def responseHeaders (c : CORSConfig) (origin : Option String) (h : Headers) : Headers :=
  let h := match origin with
    | some _ => c.simpleHeaders.foldl (fun h (k, v) => h.set k v) h
    | none => h
  match origin with
  | some o =>
    if c.allowAllOrigins && c.allowCredentials then allowExplicitOrigin h o
    else if !c.allowAllOrigins && c.isAllowedOrigin o then allowExplicitOrigin h o
    else h.set "Vary" (", ".intercalate (h.getlist "Vary" ++ ["Origin"]))
  | none => h.set "Vary" (", ".intercalate (h.getlist "Vary" ++ ["Origin"]))

/-- Whether a request is a preflight: `OPTIONS` with `Origin` and
`Access-Control-Request-Method`. -/
def isPreflight (r : Request) : Bool :=
  (r.headers.get? "origin").isSome && r.method == "OPTIONS" && r.headers.contains "access-control-request-method"

end CORSConfig

/-- `CORSMiddleware` on a built configuration. -/
def corsMiddleware (c : CORSConfig) : Middleware := fun app req =>
  if CORSConfig.isPreflight req then pure (c.preflight req.headers)
  else do
    let resp ← app req
    return { resp with headers := c.responseHeaders (req.headers.get? "origin") resp.headers }

/-- **`CORSMiddleware(app, allow_origins=(), allow_methods=("GET",),
allow_headers=(), allow_credentials=False, allow_origin_regex=None,
allow_private_network=False, expose_headers=(), max_age=600)`**. The
configuration, and the regular expression, are built once. -/
def CORSMiddleware (allow_origins : List String := []) (allow_methods : List String := ["GET"])
    (allow_headers : List String := []) (allow_credentials : Bool := false)
    (allow_origin_regex : Option PyRe.Pattern := none)
    (allow_private_network : Bool := false) (expose_headers : List String := [])
    (max_age : Nat := 600) : Middleware :=
  corsMiddleware (corsConfig allow_origins allow_methods allow_headers allow_credentials allow_origin_regex
    allow_private_network expose_headers max_age)

end LeanStarlette
