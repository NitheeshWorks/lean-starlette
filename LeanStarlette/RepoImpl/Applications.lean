import LeanStarlette.RepoImpl.Routing
import LeanStarlette.RepoImpl.FileIO

/-!
# RepoImpl: exception middleware and the application stack

* `ExceptionMiddleware` renders handled exceptions: a handler by status
  code first, then by exception kind, and `HTTPException` by default.
* `ServerErrorMiddleware` is the outermost layer: anything unhandled,
  including an `IO` error, becomes a `500` (from the installed `500`
  handler, or `Internal Server Error`, or the error text when `debug`).
* `Application.app` is `build_middleware_stack`:
  `ServerErrorMiddleware(user middleware(ExceptionMiddleware(router)))`.
-/

namespace LeanStarlette

/-- A key of `exception_handlers`: a status code (`404`), the
`HTTPException` class, another exception's kind, or `Exception` itself
(which, like `500`, installs the server-error handler). -/
inductive ExceptionKey where
  | status (code : Nat)
  | httpException
  | kind (name : String)
  | exception
  deriving BEq, Repr

instance : OfNat ExceptionKey n := ⟨.status n⟩

/-- `handler(request, exc) -> response`. -/
abbrev ExceptionHandler := Request → Exception → AppM Response

/-- A middleware: an `App` wrapped around an `App` (`Middleware(cls, ...)`). -/
abbrev Middleware := App → App

/-- The default `HTTPException` handler. -/
def defaultHTTPHandler : ExceptionHandler := fun _ e =>
  match e with
  | .http s d hs h => pure (httpExceptionResponse s d hs h)
  | e => throw e

/-- `_lookup_exception_handler`, with the status handlers first. -/
def lookupHandler (handlers : List (ExceptionKey × ExceptionHandler)) : Exception → Option ExceptionHandler
  | .http s _ _ _ =>
    match handlers.lookup (.status s) with
    | some h => some h
    | none => handlers.lookup .httpException
  | .custom k _ _ => handlers.lookup (.kind k)

/-- `ExceptionMiddleware(app, handlers)`. -/
def exceptionMiddleware (handlers : List (ExceptionKey × ExceptionHandler)) (app : App) : App := fun req =>
  tryCatch (app req) fun e =>
    match lookupHandler (handlers ++ [(.httpException, defaultHTTPHandler)]) e with
    | some h => h req e
    | none => throw e

/-- `ServerErrorMiddleware.error_response`. -/
def internalServerError : Response := PlainTextResponse "Internal Server Error" (status_code := 500)

/-- HTML-escape text (`html.escape`). -/
def htmlEscape (s : String) : String :=
  String.ofList (s.toList.flatMap fun
    | '&' => "&amp;".toList | '<' => "&lt;".toList | '>' => "&gt;".toList
    | '"' => "&quot;".toList | '\'' => "&#x27;".toList | c => [c])

/-- `ServerErrorMiddleware.debug_response`: the error as HTML when the client
accepts it, else as plain text. Lean has no traceback to show, so the page
names the exception and its message. An `IO` error is reported as
`RuntimeError`, its closest Python counterpart. -/
def debugResponse (req : Request) (e : Exception) : Response :=
  let accept := (req.headers.get? "accept").getD ""
  if (accept.splitOn "text/html").length > 1 then
    HTMLResponse s!"<html><head><title>Starlette Debugger</title></head><body><h1>500 Server Error</h1><h2>{htmlEscape (toString e)}</h2></body></html>" (status_code := 500)
  else PlainTextResponse (toString e) (status_code := 500)

/-- `ServerErrorMiddleware(app, handler, debug)`. Upstream re-raises after
responding so the server logs it; here the response is returned and the
transport logs the error. -/
def serverErrorMiddleware (handler : Option ExceptionHandler) (debug : Bool) (app : App) : App := fun req => do
  let respond (e : Exception) : AppM Response :=
    if debug then pure (debugResponse req e)
    else match handler with
      | some h => tryCatch (h req e) fun _ => pure internalServerError
      | none => pure internalServerError
  tryCatchThe IO.Error
    (tryCatch (app req) respond)
    (fun e => respond (.custom "RuntimeError" (toString e) .null))

/-- An application: `Starlette(...)`'s state. Build one with `Starlette`. -/
structure Application where
  routes : List BaseRoute := []
  debug : Bool := false
  middleware : List Middleware := []
  exception_handlers : List (ExceptionKey × ExceptionHandler) := []
  /-- `max_body_size`: larger request bodies get `413`. -/
  max_body_size : Option Nat := none
  redirect_slashes : Bool := true

namespace Application

/-- `app.url_path_for(name, **path_params)`. -/
def urlPathFor (a : Application) (name : String) (params : List (String × String) := []) : Option URLPath :=
  urlPathForList a.routes name params
abbrev url_path_for := @urlPathFor

/-- `RequestBodyLimitMiddleware`: a body over the limit is a
`413 Content Too Large`. -/
def bodyLimit (limit : Option Nat) (app : App) : App := fun req =>
  match limit with
  | some n =>
    if req.bodyBytes.size > n then pure (PlainTextResponse "Content Too Large" (status_code := 413))
    else app req
  | none => app req

/-- `build_middleware_stack()`, with `request.url_for` wired to the routes. -/
def app (a : Application) : App := fun req =>
  let isServer : ExceptionKey → Bool := fun k => k == .status 500 || k == .exception
  let errorHandler := (a.exception_handlers.find? (isServer ·.1)).map (·.2)
  let handlers := a.exception_handlers.filter (!isServer ·.1)
  let router : App := fun req => do
    let r ← routerApp a.routes a.redirect_slashes req
    liftM (prepareFile req r)
  let inner := exceptionMiddleware handlers router
  let stack := a.middleware.foldr (fun m acc => m acc) inner
  let stack := serverErrorMiddleware errorHandler a.debug (bodyLimit a.max_body_size stack)
  stack { req with urlPathFor := fun n ps => (urlPathForList a.routes n ps).map fun u => (u.path, u.protocol) }

/-- Run the application on one request. Every exception has been turned
into a response by `ServerErrorMiddleware`, so this cannot fail. -/
def call (a : Application) (req : Request) : IO Response := do
  try
    match ← (a.app req).run with
    | .ok r => pure r
    | .error _ => pure internalServerError
  catch _ => pure internalServerError

end Application

end LeanStarlette
