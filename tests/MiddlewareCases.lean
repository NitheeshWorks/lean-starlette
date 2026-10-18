import LeanStarlette

/-!
# Middleware conformance: golden replay (`tests/golden/record_middleware.py`)

The applications of `tests/middleware/test_{trusted_host,https_redirect,
cors,gzip,session}.py` and `tests/test_authentication.py`, written as a
Starlette user writes them in Lean (`mwApp`, by the recorder's names). Each
golden scenario is replayed on one `LeanStarlette.TestClient` and compared
call by call: status, headers in order, decoded body, final URL.

Two normalisations, both sides alike: a gzip body's `content-length` (the
compressed size; zlib's bytes and `Deflate`'s differ, the decoded body is
compared instead), and a signed session cookie's value (it carries the
signing time; `session_sign_verify` and the signer goldens cover the value).
-/

namespace MiddlewareCases

open LeanStarlette LeanJson

def text (s : String) (headers : List (String × String) := []) : Request → AppM Response :=
  fun _ => pure (PlainTextResponse s (headers := headers))

def allMethods : List String := ["GET", "POST", "PUT", "PATCH", "DELETE", "HEAD", "OPTIONS"]

def cors (m : Middleware) : Application :=
  Starlette (routes := [Route "/" (text "Homepage") (methods := allMethods)]) (middleware := [m])

def varyApp : Request → AppM Response := fun _ =>
  let r := PlainTextResponse "Homepage" (headers := [("Vary", "Accept-Encoding")])
  pure { r with headers := r.headers.append "Vary" "Accept-Language" }

def xs (n : Nat) : String := String.ofList (List.replicate n 'x')

def stream (media_type : Option String := none) (headers : List (String × String) := []) : Request → AppM Response :=
  fun _ => pure (StreamingResponse (fun send => do for _ in [0:10] do send (xs 400).toUTF8)
    (media_type := media_type) (headers := headers))

def raw (ct : String) : Request → AppM Response :=
  fun _ => pure (Response (xs 4000) (headers := [("content-type", ct)]))

def gz (endpoint : Request → AppM Response) (m : Middleware := Middleware GZipMiddleware) : Application :=
  Starlette (routes := [Route "/" endpoint]) (middleware := [m])

/-! ## Sessions -/

def sessionJson (r : Request) : AppM Response := do
  return JSONResponse (Json.obj #[("session", .obj (← r.session))])

def viewSession (r : Request) : AppM Response := sessionJson r

def updateSession (r : Request) : AppM Response := do
  match ← r.json with
  | .obj kvs => r.sessionUpdate kvs.toList
  | _ => pure ()
  sessionJson r

def popitemSession (r : Request) : AppM Response := do
  let _ ← r.sessionPopItem
  sessionJson r

def clearSession (r : Request) : AppM Response := do
  r.sessionClear
  sessionJson r

def noSessionAccess (_ : Request) : AppM Response :=
  pure (JSONResponse (Json.obj #[("status", .str "ok")]))

def sessionRoutes : List BaseRoute := [
  Route "/view_session" viewSession,
  Route "/update_session" updateSession (methods := ["POST"]),
  Route "/inplace_update_session" updateSession (methods := ["POST"]),
  Route "/popitem_session" popitemSession (methods := ["POST"]),
  Route "/clear_session" clearSession (methods := ["POST"]),
  Route "/no_session" noSessionAccess]

def sessions (m : Middleware) : Application := Starlette (routes := sessionRoutes) (middleware := [m])

def secondApp : Application :=
  let inner := Starlette (routes := [Route "/update_session" updateSession (methods := ["POST"])])
    (middleware := [Middleware SessionMiddleware (secret_key := "example") (path := "/second_app")])
  Starlette (routes := [Mount "/second_app" (app := some inner.app)])

/-! ## Authentication -/

/-- tests/test_authentication.py's `BasicAuth`. -/
def basicAuth : AuthenticationBackend := fun req => pure <|
  match req.headers.get? "authorization" with
  | none => .ok none
  | some auth =>
    let bad : Except AuthenticationError (Option (AuthCredentials × BaseUser)) := .error ⟨"Invalid basic auth credentials"⟩
    match (auth.splitOn " ").filter (· ≠ "") with
    | [_, cred] =>
      match LeanHttpx.Base64.decode cred with
      | some b =>
        if b.data.all (· < 128) then
          let decoded := String.ofList (b.data.toList.map fun x => Char.ofNat x.toNat)
          .ok (some (⟨["authenticated"]⟩, SimpleUser (String.ofList (splitFirst ':' decoded.toList).1)))
        else bad
      | none => bad
    | _ => bad

def homepage (r : Request) : AppM Response := do
  let u ← r.user
  return JSONResponse (Json.obj #[("authenticated", .bool u.is_authenticated), ("user", .str u.display_name),
    ("identity", .str (u.identity.getD ""))])

def userJson (r : Request) : AppM Response := do
  let u ← r.user
  return JSONResponse (Json.obj #[("authenticated", .bool u.is_authenticated), ("user", .str u.display_name)])

def superuser (r : Request) : AppM Response := do
  return JSONResponse (Json.obj #[("user", .str (← r.user).display_name)])

def authRoutes : List BaseRoute := [
  Route "/" homepage (name := "homepage"),
  Route "/dashboard" (requires ["authenticated"] userJson),
  Route "/admin" (requires ["authenticated"] (redirect := some "homepage") userJson),
  Route "/superuser" (requires ["authenticated", "admin"] superuser (status_code := 401))]

def onError (_ : Request) (e : AuthenticationError) : Response :=
  JSONResponse (Json.obj #[("error", .str e.message)]) (status_code := 401)

/-! ## The applications, by the recorder's names -/

def mwApp : String → Option Application
  | "th" => some <| Starlette (routes := [Route "/" (text "OK")])
      (middleware := [Middleware TrustedHostMiddleware (allowed_hosts := ["testserver", "*.testserver"])])
  | "th6" => some <| Starlette (routes := [Route "/" (text "OK")])
      (middleware := [Middleware TrustedHostMiddleware (allowed_hosts := ["[::1]", "[v1.foo]", "api_service", "*.example.com"])])
  | "thwww" => some <| Starlette (routes := [Route "/" (text "OK")])
      (middleware := [Middleware TrustedHostMiddleware (allowed_hosts := ["www.example.com"])])
  | "https" => some <| Starlette (routes := [Route "/" (text "OK")]) (middleware := [Middleware HTTPSRedirectMiddleware])
  | "https_noserver" => some <| Application.ofApp fun req =>
      HTTPSRedirectMiddleware (fun _ => pure (PlainTextResponse "OK")) { req with server := none }
  | "cors_all" => some <| cors (Middleware CORSMiddleware (allow_origins := ["*"]) (allow_headers := ["*"])
      (allow_methods := ["*"]) (expose_headers := ["X-Status"]) (allow_credentials := true))
  | "cors_all_nocred" => some <| cors (Middleware CORSMiddleware (allow_origins := ["*"]) (allow_headers := ["*"])
      (allow_methods := ["*"]) (expose_headers := ["X-Status"]))
  | "cors_specific" => some <| cors (Middleware CORSMiddleware (allow_origins := ["https://example.org"])
      (allow_headers := ["X-Example", "Content-Type"]))
  | "cors_disallowed" => some <| cors (Middleware CORSMiddleware (allow_origins := ["https://example.org"])
      (allow_headers := ["X-Example"]))
  | "cors_wild_cred" => some <| cors (Middleware CORSMiddleware (allow_origins := ["*"]) (allow_methods := ["POST"])
      (allow_credentials := true))
  | "cors_all_methods" => some <| cors (Middleware CORSMiddleware (allow_origins := ["*"]) (allow_methods := ["*"]))
  | "cors_regex" => some <| cors (Middleware CORSMiddleware (allow_headers := ["X-Example", "Content-Type"])
      (allow_origin_regex := re!"https://.*") (allow_credentials := true))
  | "cors_regex_full" => some <| cors (Middleware CORSMiddleware (allow_headers := ["X-Example", "Content-Type"])
      (allow_origin_regex := re!"https://.*\\.example.org"))
  | "cors_vary_default" => some <| cors (Middleware CORSMiddleware (allow_origins := ["https://example.org"]))
  | "cors_vary_nocred" => some <| Starlette (routes := [Route "/" varyApp])
      (middleware := [Middleware CORSMiddleware (allow_origins := ["*"])])
  | "cors_vary_cred" => some <| Starlette (routes := [Route "/" varyApp])
      (middleware := [Middleware CORSMiddleware (allow_origins := ["*"]) (allow_credentials := true)])
  | "cors_vary_specific" => some <| Starlette (routes := [Route "/" (text "Homepage" [("Vary", "Accept-Encoding")])])
      (middleware := [Middleware CORSMiddleware (allow_origins := ["https://example.org"])])
  | "cors_pna" => some <| cors (Middleware CORSMiddleware (allow_origins := ["*"]) (allow_methods := ["*"])
      (allow_private_network := true))
  | "cors_no_pna" => some <| cors (Middleware CORSMiddleware (allow_origins := ["*"]) (allow_methods := ["*"])
      (allow_private_network := false))
  | "cors_gzip" => some <| Starlette (routes := [Route "/" (text "Homepage" [("Vary", "Accept-Language")])])
      (middleware := [Middleware GZipMiddleware (minimum_size := 0),
        Middleware CORSMiddleware (allow_origins := ["https://allowed.example"])])
  | "gz_text" => some <| gz (text (xs 4000))
  | "gz_small" => some <| gz (text "OK")
  | "gz_stream" => some <| gz (stream)
  | "gz_stream_encoded" => some <| gz (stream (headers := [("Content-Encoding", "text")]))
  | "gz_sse" => some <| gz (stream (media_type := some "text/event-stream"))
  | "gz_svg" => some <| gz (raw "image/svg+xml")
  | "gz_png" => some <| gz (raw "image/png")
  | "gz_grpc_proto" => some <| gz (raw "application/grpc+proto")
  | "gz_zip_custom" => some <| gz (raw "application/zip") (Middleware GZipMiddleware (exclude_content_types := ["application/zip"]))
  | "gz_sse_cleared" => some <| gz (raw "text/event-stream") (Middleware GZipMiddleware (exclude_content_types := []))
  | "gz_sse_normalized" => some <| gz (raw "Text/Event-Stream; charset=utf-8")
      (Middleware GZipMiddleware (exclude_content_types := ["text/event-stream"]))
  | "gz_zip_normalized" => some <| gz (raw "application/zip")
      (Middleware GZipMiddleware (exclude_content_types := ["Application/ZIP; charset=utf-8"]))
  | "gz_image_wildcard" => some <| gz (raw "image/png") (Middleware GZipMiddleware (exclude_content_types := ["image/*"]))
  | "gz_big" => some <| gz (text (xs (128 * 1024)))
  | "sessions" => some <| sessions (Middleware SessionMiddleware (secret_key := "example"))
  | "sessions_secure" => some <| sessions (Middleware SessionMiddleware (secret_key := "example") (https_only := true))
  | "sessions_partitioned" => some <| sessions (Middleware SessionMiddleware (secret_key := "example")
      (https_only := true) (same_site := .none) (partitioned := true))
  | "sessions_expired" => some <| sessions (Middleware SessionMiddleware (secret_key := "example") (max_age := some (-1)))
  | "sessions_no_max_age" => some <| sessions (Middleware SessionMiddleware (secret_key := "example") (max_age := none))
  | "sessions_zero" => some <| sessions (Middleware SessionMiddleware (secret_key := "example") (max_age := some 0))
  | "sessions_domain" => some <| sessions (Middleware SessionMiddleware (secret_key := "example")
      (domain := some ".example.com"))
  | "sessions_subpath" => some secondApp
  | "auth" => some <| Starlette (routes := authRoutes) (middleware := [Middleware AuthenticationMiddleware (backend := basicAuth)])
  | "auth_on_error" => some <| Starlette (routes := authRoutes)
      (middleware := [Middleware AuthenticationMiddleware (backend := basicAuth) (on_error := onError)])
  | _ => none

/-! ## Replay -/

def pairs (j : Option Json) : List (String × String) :=
  match j with
  | some (.obj kvs) => kvs.toList.filterMap fun (k, v) => v.getStr?.map (k, ·)
  | _ => []

/-- Bytes as Latin-1 text. -/
def latin1 (b : ByteArray) : String := String.ofList (b.data.toList.map fun x => Char.ofNat x.toNat)

/-- A signed session cookie's value, masked. -/
def maskSession (v : String) : String :=
  if v.startsWith "session=" && !v.startsWith "session=null;" then
    "session=<signed>" ++ String.ofList ((v.toList.dropWhile (· ≠ ';')))
  else v

/-- The normalised result of one call. -/
def normalise (status : Nat) (headers : List (String × String)) (text url : String) : Json :=
  let gzipped := headers.any fun (k, v) => k == "content-encoding" && v == "gzip"
  let hs := headers.filter (fun (k, _) => !(gzipped && k == "content-length"))
  let hs := hs.map fun (k, v) => if k == "set-cookie" then (k, maskSession v) else (k, v)
  Json.obj #[("status", .num (.int status)), ("headers", .arr (hs.map fun (k, v) => Json.arr #[.str k, .str v]).toArray),
    ("text", .str text), ("url", .str url)]

def normaliseWant (w : Json) : Json :=
  let status := ((w.getObjVal? "status").bind Json.getInt?).getD 0
  let hs := match (w.getObjVal? "headers").bind Json.getArr? with
    | some a => a.toList.filterMap fun p => match p.getArr? with
      | some #[a, b] => do pure ((← a.getStr?), (← b.getStr?))
      | _ => none
    | none => []
  normalise status.toNat hs (((w.getObjVal? "text").bind Json.getStr?).getD "") (((w.getObjVal? "url").bind Json.getStr?).getD "")

/-- The session cookie of a `set-cookie` header. -/
def sessionValue (hs : List (String × String)) : Option String := do
  let (_, v) ← hs.find? (·.1 == "set-cookie")
  let rest ← (v.splitOn "session=")[1]?
  pure (String.ofList (rest.toList.takeWhile (· ≠ ';')))

def newClient (app : Application) (opts : Json) (cookies : List (String × String)) : IO LeanHttpx.Client :=
  LeanStarlette.TestClient app (base_url := ((opts.getObjVal? "base_url").bind Json.getStr?).getD "http://testserver")
    (raise_server_exceptions := false) (cookies := ((cookies ++ pairs (opts.getObjVal? "cookies")) : LeanHttpx.Cookies))

def goldenCaseOn (app : Application) (line : Json) : Option (String × String × IO Bool) := do
  let name ← (line.getObjVal? "name").bind Json.getStr?
  let opts := (line.getObjVal? "client").getD (.obj #[])
  let calls ← (line.getObjVal? "calls").bind Json.getArr?
  let want ← (line.getObjVal? "results").bind Json.getArr?
  pure (s!"{name} (golden, Starlette 1.8.0)", s!"middleware: {(name.splitOn "::").getLastD name}", do
    let mut client ← newClient app opts []
    let mut prev : List (String × String) := []
    let mut good := true
    for (call, w) in calls.toList.zip want.toList do
      if let some c := (call.getObjVal? "delete_cookie").bind Json.getStr? then
        let jar ← client.cookies
        client.setCookies (jar.delete c)
      if ((call.getObjVal? "carry_session").bind Json.getBool?).getD false then
        client ← newClient app opts ((sessionValue prev).toList.map ("session", ·))
      let method := ((call.getObjVal? "method").bind Json.getStr?).getD "GET"
      let url := ((call.getObjVal? "url").bind Json.getStr?).getD "/"
      let r ← client.request method url (json := call.getObjVal? "json")
        (headers := (pairs (call.getObjVal? "headers") : LeanHttpx.Headers))
        (followRedirects := (call.getObjVal? "follow").bind Json.getBool?)
      let u := match r.request? with | some q => toString q.url | none => url
      let got := normalise r.statusCode r.headers.raw (latin1 r.content) u
      let w := normaliseWant w
      prev := r.headers.raw
      unless toString got == toString w do
        good := false
        IO.println s!"      {method} {url}"
        IO.println s!"      got  {(String.ofList ((toString got).toList.take 900))}"
        IO.println s!"      want {(String.ofList ((toString w).toList.take 900))}"
    pure good)

/-- Replay one golden line: `(upstream test, case name, run)`. -/
def goldenCase (line : Json) : Option (String × String × IO Bool) :=
  match (line.getObjVal? "app").bind Json.getStr? |>.bind mwApp with
  | none => none
  | some app => goldenCaseOn app line

def goldenCases : IO (List (String × String × IO Bool)) := do
  let lines ← IO.FS.lines "tests/golden/middleware-starlette-1.8.0.jsonl"
  return lines.toList.filterMap fun l => (from_json l).toOption.bind fun j => goldenCase j.val

/-! ## Unit goldens (`tests/golden/record_m5_units.py`) -/

/-- Patterns Python compiles and this dialect refuses at construction (the
documented `Unsupported` list). -/
def regexUnsupported : List String :=
  ["(?=a)", "(?<!a)", "(?i)a", "a*+", "(?>a)", "\\N{DIGIT ONE}", "a{1001}", "(?x)"]

def strs (j : Option Json) : List String :=
  match j with
  | some (.arr xs) => xs.toList.filterMap Json.getStr?
  | _ => []

def strPairs (j : Option Json) : List (String × String) :=
  match j with
  | some (.arr xs) => xs.toList.filterMap fun p => match p.getArr? with
    | some #[a, b] => do pure ((← a.getStr?), (← b.getStr?))
    | _ => none
  | _ => []

def unitCase (line : Json) : Option (String × String × IO Bool) := do
  let kind ← (line.getObjVal? "kind").bind Json.getStr?
  let str (k : String) : Option String := (line.getObjVal? k).bind Json.getStr?
  match kind with
  | "regex" =>
    let p ← str "pattern"
    pure ("starlette CORSMiddleware(allow_origin_regex=...): re.compile + fullmatch (golden, Python 3.13)",
      s!"regex: {p.quote}", do
      match PyRe.compile p, line.getObjVal? "error" with
      | .error _, some _ => pure true
      | .error (.unsupported _), none => pure (regexUnsupported.contains p)
      | .error e, none => IO.println s!"      refused: {e}"; pure false
      | .ok _, some e => IO.println s!"      accepted; Python: {e}"; pure false
      | .ok m, none =>
        let texts := strs (line.getObjVal? "texts")
        let want := match (line.getObjVal? "match").bind Json.getArr? with
          | some a => a.toList.filterMap Json.getBool?
          | none => []
        let bad := (texts.zip want).filter fun (t, w) =>
          -- `$` is `\Z` (documented): it differs only where Python matches before a final newline
          m.test t != w && !(p == "a$\\n" && t == "a\n")
        unless bad.isEmpty do IO.println s!"      differs on {bad.map (·.1.quote)}"
        pure bad.isEmpty)
  | "cookie_parser" =>
    let i ← str "input"
    pure ("tests/test_requests.py::test_cookies_edge_cases / test_cookies_invalid (golden, Starlette 1.8.0)",
      s!"cookie_parser {i.quote}", do
      let got := cookieParser i
      let want := strPairs (line.getObjVal? "output")
      unless got == want do IO.println s!"      got {got}"
      pure (got == want))
  | "quote" =>
    let v ← str "value"
    let q ← str "quoted"
    pure ("http.cookies._quote (golden, Python 3.13)", s!"cookie quote {v.quote}", do
      let got := cookieQuote v
      unless got == q do IO.println s!"      got {got.quote}"
      -- and _unquote reads it back (cookieUnquote_quote)
      pure (got == q && String.ofList (cookieUnquoteChars got.toList) == v))
  | "set_cookie" =>
    let args ← line.getObjVal? "args"
    let a (k : String) : Option Json := args.getObjVal? k
    let key := ((a "key").bind Json.getStr?).getD ""
    let value := ((a "value").bind Json.getStr?).getD ""
    let maxAge : Option Int := (a "max_age").bind Json.getInt?
    let expires := ((a "expires").bind Json.getStr?).map CookieExpires.text
    let path : Option String := match a "path" with | some .null => none | some (.str p) => some p | _ => some "/"
    let domain := (a "domain").bind Json.getStr?
    let flag (k : String) := ((a k).bind Json.getBool?).getD false
    let samesite : Option SameSite := match a "samesite" with
      | some .null => none
      | some (.str "strict") => some .strict
      | some (.str "none") => some .none
      | _ => some .lax
    pure ("tests/test_responses.py::test_set_cookie (golden, Starlette 1.8.0)", s!"set_cookie {toString args}", do
      match str "ok" with
      | some want =>
        let got := setCookieLine key value maxAge expires path domain (flag "secure") (flag "httponly") samesite false
        unless got == want do IO.println s!"      got {got.quote}"
        pure (isCookieKey key && got == want)
      | none => pure (!isCookieKey key))
  | "session_sign" =>
    let ts ← (line.getObjVal? "timestamp").bind Json.getInt?
    let want ← str "cookie"
    let d ← match line.getObjVal? "data" with | some (.obj kvs) => some kvs | _ => none
    pure ("starlette/middleware/sessions.py: the signed session cookie (golden, Starlette 1.8.0)",
      s!"session cookie at {ts}", do
      let t := LeanItsdangerous.TimestampSigner.new "example"
      let got := encodeSession t d ts.toNat.toUInt64
      unless got == want do IO.println s!"      got {got}"
      pure (got == want && decodeSession t none ts.toNat.toUInt64 got matches .loaded _))
  | _ => none

def unitGoldenCases : IO (List (String × String × IO Bool)) := do
  let lines ← IO.FS.lines "tests/golden/m5-units-starlette-1.8.0.jsonl"
  return lines.toList.filterMap fun l => (from_json l).toOption.bind fun j => unitCase j.val

/-! ## Documented deviations, checked here (no upstream golden: upstream fails) -/

def deviationCases : List (String × String × IO Bool) := [
  ("starlette/middleware/gzip.py:send_with_compression (UP-063; deviation gzip.no-body-status)",
    "gzip: a 204 passes through untouched with minimum_size=0", do
    let app := gz (fun _ => pure (Response (status_code := 204))) (Middleware GZipMiddleware (minimum_size := 0))
    let r ← app.call { headers := Headers.ofList [("host", "testserver"), ("accept-encoding", "gzip")] }
    pure (r.status_code == 204 && r.body.size == 0 && (r.headers.get? "content-encoding").isNone)),
  ("starlette/responses.py:set_cookie (UP-064; deviation cookies.non-latin1)",
    "set_cookie: a value above U+00FF is sent as is (quoted, as http.cookies prints it)", do
    let r := (PlainTextResponse "ok").set_cookie "name" "\u0101"
    pure (r.headers.get? "set-cookie" == some "name=\"\u0101\"; Path=/; SameSite=lax"))]

end MiddlewareCases
