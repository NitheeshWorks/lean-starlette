import LeanStarlette.RepoImpl.Middleware

/-!
# RepoImpl: authentication (`starlette/authentication.py`,
`starlette/middleware/authentication.py`)

A backend looks at the request and returns credentials and a user, nothing
(anonymous), or an `AuthenticationError`. `AuthenticationMiddleware` puts
the result in `request.auth` / `request.user` (`AuthCredentials()` and
`UnauthenticatedUser()` for nothing) or answers with `on_error` (by default
`400` and the error's text). `requires` wraps an endpoint: without every
scope it raises `HTTPException(status_code)` (403), or redirects (303) to
the named route with `?next=` the request URL.

Upstream's `requires` inspects the endpoint's signature for its `request`
or `websocket` parameter; here it wraps a `Request → AppM Response`, so
there is nothing to find. WebSocket endpoints are not in this port.
-/

namespace LeanStarlette

/-- `AuthenticationError(message)`. -/
structure AuthenticationError where
  message : String := ""
  deriving Inhabited, BEq, Repr

/-- `AuthenticationBackend.authenticate(conn)`. -/
abbrev AuthenticationBackend := Request → AppM (Except AuthenticationError (Option (AuthCredentials × BaseUser)))

/-- `SimpleUser(username)`. -/
def SimpleUser (username : String) : BaseUser :=
  { is_authenticated := true, display_name := username, identity := some username }

/-- `UnauthenticatedUser()`. -/
def UnauthenticatedUser : BaseUser := { is_authenticated := false, display_name := "", identity := some "" }

/-- `AuthenticationMiddleware.default_on_error`: `400` and the message. -/
def defaultOnAuthError (_ : Request) (e : AuthenticationError) : Response :=
  PlainTextResponse e.message (status_code := 400)

/-- **`AuthenticationMiddleware(app, backend, on_error=None)`**. -/
def AuthenticationMiddleware (backend : AuthenticationBackend)
    (on_error : Request → AuthenticationError → Response := defaultOnAuthError) : Middleware := fun app req => do
  match ← backend req with
  | .error e => pure (on_error req e)
  | .ok none => app { req with auth? := some {}, user? := some UnauthenticatedUser }
  | .ok (some (creds, user)) => app { req with auth? := some creds, user? := some user }

/-- `request.auth` without `AuthenticationMiddleware`: upstream's assertion. -/
def noAuth : Exception :=
  .custom "AssertionError" "AuthenticationMiddleware must be installed to access request.auth" .null

/-- `request.auth`. -/
def Request.auth (r : Request) : AppM AuthCredentials :=
  match r.auth? with
  | some a => pure a
  | none => throw noAuth

/-- `request.user`. -/
def Request.user (r : Request) : AppM BaseUser :=
  match r.user? with
  | some u => pure u
  | none => throw (.custom "AssertionError" "AuthenticationMiddleware must be installed to access request.user" .null)

/-- `has_required_scope(conn, scopes)`. -/
def hasRequiredScope (creds : AuthCredentials) (scopes : List String) : Bool :=
  scopes.all creds.scopes.contains

/-- **`@requires(scopes, status_code=403, redirect=None)`** on an endpoint:
`requires ["authenticated"] endpoint (redirect := some "login")`. -/
def requires (scopes : List String) (endpoint : Request → AppM Response) (status_code : Nat := 403)
    (redirect : Option String := none) (h : StatusCode.Valid status_code := by decide) :
    Request → AppM Response := fun req => do
  let creds ← req.auth
  if hasRequiredScope creds scopes then endpoint req else
  match redirect with
  | some name =>
    match req.urlFor name with
    | some u => pure (RedirectResponse (toString u ++ "?next=" ++ quotePlus (toString req.url)) (status_code := 303))
    | none => throw (.custom "NoMatchFound" s!"No route exists for name \"{name}\" and params \"\"." .null)
  | none => throw (HTTPException status_code (h := h))

end LeanStarlette
