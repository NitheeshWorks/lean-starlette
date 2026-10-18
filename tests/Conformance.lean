import LeanStarlette

/-!
# Conformance cases

Each case re-expresses one upstream test (https://github.com/Kludex/starlette,
`tests/`) in Lean and names it, so `docs/traceability.toml` can point at
both. The upstream suite is the behavioural specification; no upstream code
is copied. Expected values were confirmed against Starlette 1.8.0.

`TestClient` below is a small in-process client with the conventions of
`starlette.testclient.TestClient` (base URL `http://testserver`, httpx's
default headers, redirects followed); the full client over lean-httpx is a
later card. Cases tagged `[std.http]` go through the real transport,
`Std.Http`'s parser and writer over its in-memory connection.

Run with `lake exe conformance`.
-/

open LeanStarlette LeanJson

structure Case where
  /-- Upstream test this mirrors, e.g. `tests/test_routing.py::test_router`. -/
  upstream : String
  name : String
  run : IO Bool

/-! ## A test client -/

structure TestResponse where
  status_code : Nat
  headers : Headers
  content : ByteArray
  url : String

def TestResponse.text (r : TestResponse) : String := (String.fromUTF8? r.content).getD ""
def TestResponse.json (r : TestResponse) : Option Json :=
  match from_json r.content with
  | .ok v => some v.val
  | .error _ => none

/-- Split `http://host:port/path?query` (or a bare path) against a base. -/
def resolveURL (base : URL) (url : String) : URL :=
  let u := URL.parse url
  if u.scheme.isEmpty then { u with scheme := base.scheme, netloc := base.netloc } else u

def defaultHeaders (netloc : String) : List (String × String) :=
  [("host", netloc), ("accept", "*/*"), ("accept-encoding", "gzip, deflate, zstd"),
   ("connection", "keep-alive"), ("user-agent", "testclient")]

/-- Build the request Starlette's test client would send. -/
def mkRequest (method : String) (u : URL) (headers : List (String × String)) (content : ByteArray) : Request :=
  let port := match splitFirst ':' u.netloc.toList with
    | (_, some p) => ofDigits p
    | _ => if u.scheme == "https" then 443 else 80
  let host := String.ofList (splitFirst ':' u.netloc.toList).1
  let given := Headers.ofList headers
  let hs := (defaultHeaders u.netloc).filter (fun p => !given.contains p.1) ++ headers
  let hs := if content.size > 0 then hs ++ [("content-length", toString content.size)] else hs
  { method, scheme := u.scheme, server := some (host, port), client := some ("testclient", 50000),
    path := unquote u.path, query_string := u.query, headers := Headers.ofList hs, bodyBytes := content }

/-- Send, then follow up to `fuel` redirects. -/
def sendFollow (app : Application) (headers : List (String × String)) (follow : Bool) :
    Nat → String → URL → ByteArray → IO TestResponse
  | fuel, method, u, content => do
    let r ← app.call (mkRequest method u headers content)
    let full ← r.readBody
    r.background.run
    let body := if method == "HEAD" then ByteArray.empty else full
    let resp : TestResponse := ⟨r.status_code, r.headers, body, toString u⟩
    match fuel with
    | 0 => pure resp
    | n + 1 =>
      match r.headers.get? "location" with
      | some loc =>
        if follow && [301, 302, 303, 307, 308].contains r.status_code then
          let (m, c) := if r.status_code == 303 then ("GET", ByteArray.empty) else (method, content)
          sendFollow app headers follow n m (resolveURL u loc) c
        else pure resp
      | none => pure resp

def TestClient.request (app : Application) (method url : String)
    (headers : List (String × String) := []) (content : ByteArray := .empty)
    (follow : Bool := true) (base : String := "http://testserver") : IO TestResponse :=
  sendFollow app headers follow 20 method (resolveURL (URL.parse base) url) content

def TestClient.get (app : Application) (url : String) (headers : List (String × String) := [])
    (follow := true) (base := "http://testserver") : IO TestResponse :=
  TestClient.request app "GET" url headers .empty follow base

def TestClient.post (app : Application) (url : String) (content : String := "")
    (headers : List (String × String) := []) : IO TestResponse :=
  TestClient.request app "POST" url headers content.toUTF8

def TestClient.call (app : Application) (method url : String) : IO TestResponse :=
  TestClient.request app method url

def ok (b : Bool) : IO Bool := pure b

/-- Compare JSON by value. -/
def jsonEq (a : Option Json) (b : Json) : Bool := match a with
  | some a => toString a == toString b
  | none => false

/-! ## tests/test_routing.py -/

def homepage (_ : Request) : Response := Response "Hello, world" (media_type := "text/plain")
def users (_ : Request) : Response := Response "All users" (media_type := "text/plain")
def user (r : Request) : Response :=
  Response ("User " ++ toString r.pathParams["username"]!) (media_type := "text/plain")
def userMe (_ : Request) : Response := Response "User fixed me" (media_type := "text/plain")
def disableUser (r : Request) : Response :=
  Response ("User " ++ toString r.pathParams["username"]! ++ " disabled") (media_type := "text/plain")
def userNoMatch (_ : Request) : Response := Response "User fixed no match" (media_type := "text/plain")
def funcHomepage (_ : Request) : Response := Response "Hello, world!" (media_type := "text/plain")
def contact (_ : Request) : Response := Response "Hello, POST!" (media_type := "text/plain")
def search (_ : Request) : Response := Response "Hello, QUERY!" (media_type := "text/plain")
def intConvertor (r : Request) : Response := JSONResponse (json% {"int": (r.pathParams["param"]!)})
def floatConvertor (r : Request) : Response := JSONResponse (json% {"float": (r.pathParams["param"]!)})
def pathConvertor (r : Request) : Response := JSONResponse (json% {"path": (r.pathParams["param"]!)})
def uuidConvertor (r : Request) : Response := JSONResponse (json% {"uuid": (r.pathParams["param"]!)})
def staticApp : App := ToApp.toApp (Response "xxxxx" (media_type := "image/png"))

def routingApp : Application := Router [
  Route "/" homepage (methods := ["GET"]) (name := "homepage"),
  Mount "/users" (routes := [
    Route "/" users (name := "users"),
    Route "/me" userMe (name := "user_me"),
    Route "/{username}" user (name := "user"),
    Route "/{username}:disable" disableUser (methods := ["PUT"]) (name := "disable_user"),
    Route "/nomatch" userNoMatch (name := "user_no_match")]),
  Mount "/static" (app := staticApp),
  Route "/func" funcHomepage (methods := ["GET"]) (name := "func_homepage"),
  Route "/func" contact (methods := ["POST"]) (name := "contact"),
  Route "/search" search (methods := ["QUERY"]) (name := "search"),
  Route "/int/{param:int}" intConvertor (name := "int-convertor"),
  Route "/float/{param:float}" floatConvertor (name := "float-convertor"),
  Route "/path/{param:path}" pathConvertor (name := "path-convertor"),
  Route "/uuid/{param:uuid}" uuidConvertor (name := "uuid-convertor"),
  Route "/path-with-parentheses({param:int})" intConvertor (name := "path-with-parentheses")]

def urlPath (a : Application) (name : String) (ps : List (String × String) := []) : Option String :=
  (a.urlPathFor name ps).map toString

def routingCases : List Case := [
  ⟨"tests/test_routing.py::test_router", "GET / is the homepage", do
    let r ← TestClient.get routingApp "/"
    ok (r.status_code == 200 && r.text == "Hello, world")⟩,
  ⟨"tests/test_routing.py::test_router", "POST / is 405 with Allow GET, HEAD", do
    let r ← TestClient.post routingApp "/"
    let allow := ((r.headers.get? "allow").getD "").splitOn ", "
    ok (r.status_code == 405 && r.text == "Method Not Allowed" && allow.length == 2 &&
      allow.contains "GET" && allow.contains "HEAD")⟩,
  ⟨"fastapi.routing.APIRoute (measured: HEAD on @app.get is 405, allow: GET)", "RouteExact: HEAD on a GET route is 405 with Allow GET", do
    let app := Starlette (routes := [RouteExact "/items" (fun (_ : Request) => PlainTextResponse "ok") (methods := ["get"])])
    let r ← TestClient.request app "HEAD" "/items"
    let r2 ← TestClient.get app "/items"
    ok (r.status_code == 405 && r.headers.get? "allow" == some "GET" && r2.status_code == 200 && r2.text == "ok")⟩,
  ⟨"tests/test_routing.py::test_router", "GET /foo is 404", do
    let r ← TestClient.get routingApp "/foo"
    ok (r.status_code == 404 && r.text == "Not Found")⟩,
  ⟨"tests/test_routing.py::test_router", "GET /users redirects to the mount", do
    let r ← TestClient.get routingApp "/users"
    ok (r.status_code == 200 && r.text == "All users" && r.url == "http://testserver/users/")⟩,
  ⟨"tests/test_routing.py::test_router", "a mounted parameter route", do
    let r ← TestClient.get routingApp "/users/tomchristie"
    ok (r.status_code == 200 && r.text == "User tomchristie")⟩,
  ⟨"tests/test_routing.py::test_router", "a mounted literal route", do
    let r ← TestClient.get routingApp "/users/me"
    ok (r.status_code == 200 && r.text == "User fixed me")⟩,
  ⟨"tests/test_routing.py::test_router", "a trailing slash redirects away", do
    let r ← TestClient.get routingApp "/users/tomchristie/"
    ok (r.status_code == 200 && r.url == "http://testserver/users/tomchristie" && r.text == "User tomchristie")⟩,
  ⟨"tests/test_routing.py::test_router", "a literal after a parameter", do
    let r ← TestClient.call routingApp "PUT" "/users/tomchristie:disable"
    ok (r.status_code == 200 && r.url == "http://testserver/users/tomchristie:disable" &&
      r.text == "User tomchristie disabled")⟩,
  ⟨"tests/test_routing.py::test_router", "first match wins over a later literal", do
    let r ← TestClient.get routingApp "/users/nomatch"
    ok (r.status_code == 200 && r.text == "User nomatch")⟩,
  ⟨"tests/test_routing.py::test_router", "a mounted app", do
    let r ← TestClient.get routingApp "/static/123"
    ok (r.status_code == 200 && r.text == "xxxxx")⟩,
  ⟨"tests/test_routing.py::test_route_converters", "int convertor and url_path_for", do
    let r ← TestClient.get routingApp "/int/5"
    ok (r.status_code == 200 && jsonEq r.json (json% {"int": 5}) &&
      urlPath routingApp "int-convertor" [("param", "5")] == some "/int/5")⟩,
  ⟨"tests/test_routing.py::test_route_converters", "path with parentheses", do
    let r ← TestClient.get routingApp "/path-with-parentheses(7)"
    ok (r.status_code == 200 && jsonEq r.json (json% {"int": 7}) &&
      urlPath routingApp "path-with-parentheses" [("param", "7")] == some "/path-with-parentheses(7)")⟩,
  ⟨"tests/test_routing.py::test_route_converters", "float convertor", do
    let r ← TestClient.get routingApp "/float/25.5"
    ok (r.status_code == 200 && r.text == "{\"float\":25.5}" &&
      urlPath routingApp "float-convertor" [("param", "25.5")] == some "/float/25.5")⟩,
  ⟨"tests/test_routing.py::test_route_converters", "path convertor", do
    let r ← TestClient.get routingApp "/path/some/example"
    ok (r.status_code == 200 && jsonEq r.json (json% {"path": "some/example"}) &&
      urlPath routingApp "path-convertor" [("param", "some/example")] == some "/path/some/example")⟩,
  ⟨"tests/test_routing.py::test_route_converters", "uuid convertor", do
    let r ← TestClient.get routingApp "/uuid/ec38df32-ceda-4cfa-9b4a-1aeb94ad551a"
    ok (r.status_code == 200 && jsonEq r.json (json% {"uuid": "ec38df32-ceda-4cfa-9b4a-1aeb94ad551a"}) &&
      urlPath routingApp "uuid-convertor" [("param", "ec38df32-ceda-4cfa-9b4a-1aeb94ad551a")] ==
        some "/uuid/ec38df32-ceda-4cfa-9b4a-1aeb94ad551a")⟩,
  ⟨"tests/test_routing.py::test_url_path_for", "url_path_for through routes and mounts", do
    ok (urlPath routingApp "homepage" == some "/" &&
      urlPath routingApp "user" [("username", "tomchristie")] == some "/users/tomchristie" &&
      urlPath routingApp "broken" == none &&
      urlPath routingApp "broken" [("key", "value"), ("key2", "value2")] == none &&
      urlPath routingApp "user" [("username", "tom/christie")] == none &&
      urlPath routingApp "user" [("username", "")] == none)⟩,
  ⟨"tests/test_routing.py::test_url_path_for_with_double_slash_path", "a leading // is escaped", do
    let a := Router [Route "/{path:path}" homepage (name := "catchall")]
    ok (urlPath a "catchall" [("path", "/example.org/a")] == some "/%2Fexample.org/a" &&
      urlPath a "catchall" [("path", "\\example.org/a")] == some "/%5Cexample.org/a")⟩,
  ⟨"tests/test_routing.py::test_url_for", "make_absolute_url", do
    let abs (n : String) (ps : List (String × String)) (b : String) :=
      ((routingApp.urlPathFor n ps).map fun p => toString (p.makeAbsoluteURL (URL.parse b)))
    ok (abs "homepage" [] "https://example.org" == some "https://example.org/" &&
      abs "homepage" [] "https://example.org/root_path/" == some "https://example.org/root_path/" &&
      abs "user" [("username", "tomchristie")] "https://example.org" == some "https://example.org/users/tomchristie" &&
      abs "user" [("username", "tomchristie")] "https://example.org/root_path/" ==
        some "https://example.org/root_path/users/tomchristie")⟩,
  ⟨"tests/test_routing.py::test_router_add_route", "GET /func", do
    let r ← TestClient.get routingApp "/func"
    ok (r.status_code == 200 && r.text == "Hello, world!")⟩,
  ⟨"tests/test_routing.py::test_router_duplicate_path", "POST /func goes to the second route", do
    let r ← TestClient.post routingApp "/func"
    ok (r.status_code == 200 && r.text == "Hello, POST!")⟩,
  ⟨"tests/test_routing.py::test_router_query_method", "the QUERY method", do
    let r ← TestClient.call routingApp "QUERY" "/search"
    let r2 ← TestClient.get routingApp "/search"
    ok (r.status_code == 200 && r.text == "Hello, QUERY!" && r2.status_code == 405 &&
      r2.text == "Method Not Allowed" && r2.headers.get? "allow" == some "QUERY")⟩,
  ⟨"tests/test_routing.py::test_mount_urls", "a mount of a mount", do
    let a := Router [Mount "/users" (routes := [Route "/" users, Route "/{username}" user])]
    let r1 ← TestClient.get a "/users"
    let r2 ← TestClient.get a "/users/tomchristie"
    let r3 ← TestClient.get a "/users/tomchristie/"
    ok (r1.status_code == 200 && r1.url == "http://testserver/users/" && r2.text == "User tomchristie" &&
      r3.status_code == 200 && r3.url == "http://testserver/users/tomchristie")⟩,
  ⟨"tests/test_routing.py::test_reverse_mount_urls", "named mounts in url_path_for", do
    let mounted := Router [Mount "/users" (name := "users") (routes := [Route "/{username}" user (name := "user")])]
    let nested := Router [Mount "/{subpath}" (name := "mount") (routes := [Route "/{username}" user (name := "user")])]
    ok (urlPath mounted "users:user" [("username", "tomchristie")] == some "/users/tomchristie" &&
      urlPath mounted "users" [("path", "/a")] == some "/users/a" &&
      urlPath nested "mount:user" [("subpath", "test"), ("username", "tomchristie")] == some "/test/tomchristie" &&
      urlPath nested "mount" [("subpath", "test"), ("path", "/a")] == some "/test/a")⟩,
  ⟨"tests/test_routing.py::test_mount_at_root", "a mount at the root", do
    let a := Router [Mount "/" (app := ToApp.toApp (Response "x" (media_type := "text/plain")))]
    let r ← TestClient.get a "/"
    ok (r.status_code == 200 && r.text == "x")⟩,
  ⟨"tests/test_routing.py::test_duplicated_param_names", "duplicated parameters are rejected", do
    let a := Router [Route "/{id}/{id}" homepage, Route "/{id}/{name}/{id}/{name}" homepage]
    ok (a.checkRoutes.map (·.2) ==
      ["Duplicated param name id at path /{id}/{id}", "Duplicated param names id, name at path /{id}/{name}/{id}/{name}"])⟩,
  ⟨"tests/test_routing.py::test_standalone_route_matches", "a route matches its path", do
    let r := Route "/" homepage
    ok (match r.matches { path := "/" } with | .full _ => true | _ => false)⟩,
  ⟨"tests/test_routing.py::test_standalone_route_does_not_match", "a route does not match another path", do
    let r := Route "/" homepage
    ok (match r.matches { path := "/invalid" } with | .none => true | _ => false)⟩,
  ⟨"tests/test_routing.py::test_route_name", "a route's name", do
    let a := Router [Route "/" homepage (name := "homepage")]
    ok (urlPath a "homepage" == some "/")⟩
]

/-! ## tests/test_convertors.py -/

def floatApp : Application := Router [Route "/{param:float}" floatConvertor]
def uuidApp : Application := Router [Route "/{param:uuid}" (fun (_ : Request) => JSONResponse "ok")]

def convertorCases : List Case := [
  ⟨"tests/test_convertors.py::test_default_float_convertor", "1.0 matches a float", do
    ok ((← TestClient.get floatApp "/1.0").status_code == 200)⟩,
  ⟨"tests/test_convertors.py::test_default_float_convertor", "1-0 does not", do
    ok ((← TestClient.get floatApp "/1-0").status_code == 404)⟩,
  ⟨"tests/test_convertors.py::test_default_uuid_convertor", "uuid case and hyphens", do
    let codes ← ["00000000-aaaa-ffff-9999-000000000000", "00000000aaaaffff9999000000000000",
      "00000000-AAAA-FFFF-9999-000000000000", "00000000AAAAFFFF9999000000000000", "not-a-uuid"].mapM
        fun p => do return (← TestClient.get uuidApp ("/" ++ p)).status_code
    ok (codes == [200, 200, 200, 200, 404])⟩
]

/-! ## tests/test_responses.py -/

def respApp (r : Response) : Application := .ofApp (ToApp.toApp r)

def redirectApp (target : String) : Application := .ofApp fun req =>
  pure (if req.path == target then Response "hello, world" (media_type := "text/plain") else RedirectResponse target)

def responseCases : List Case := [
  ⟨"tests/test_responses.py::test_text_response", "text", do
    ok ((← TestClient.get (respApp (Response "hello, world" (media_type := "text/plain"))) "/").text == "hello, world")⟩,
  ⟨"tests/test_responses.py::test_bytes_response", "bytes", do
    ok ((← TestClient.get (respApp (Response "xxxxx".toUTF8 (media_type := "image/png"))) "/").content == "xxxxx".toUTF8)⟩,
  ⟨"tests/test_responses.py::test_json_none_response", "JSON null", do
    ok ((← TestClient.get (respApp (JSONResponse Json.null)) "/").content == "null".toUTF8)⟩,
  ⟨"tests/test_responses.py::test_redirect_response", "a redirect is followed", do
    let r ← TestClient.get (redirectApp "/") "/redirect"
    ok (r.text == "hello, world" && r.url == "http://testserver/")⟩,
  ⟨"tests/test_responses.py::test_quoting_redirect_response", "the location is quoted", do
    let r ← TestClient.get (redirectApp "/I ♥ Starlette/") "/redirect"
    ok (r.text == "hello, world" && r.url == "http://testserver/I%20%E2%99%A5%20Starlette/")⟩,
  ⟨"tests/test_responses.py::test_redirect_response_content_length_header", "a redirect has content-length 0", do
    let r ← TestClient.get (redirectApp "/") "/redirect" (follow := false)
    ok (r.url == "http://testserver/redirect" && r.headers.get? "content-length" == some "0")⟩,
  ⟨"tests/test_responses.py::test_response_headers", "headers can be replaced", do
    let resp := (Response "hello, world" (media_type := "text/plain")
      (headers := [("x-header-1", "123"), ("x-header-2", "456")])).setHeader "x-header-2" "789"
    let r ← TestClient.get (respApp resp) "/"
    ok (r.headers.get? "x-header-1" == some "123" && r.headers.get? "x-header-2" == some "789")⟩,
  ⟨"tests/test_responses.py::test_response_phrase", "reason phrases", do
    ok (reasonPhrase 204 == "No Content" && reasonPhrase 123 == "" &&
      (Response "".toUTF8 (status_code := 123)).status_code == 123)⟩,
  ⟨"tests/test_responses.py::test_populate_headers", "content-length and content-type", do
    let r ← TestClient.get (respApp (Response "hi" (headers := []) (media_type := "text/html"))) "/"
    ok (r.text == "hi" && r.headers.get? "content-length" == some "2" &&
      r.headers.get? "content-type" == some "text/html; charset=utf-8")⟩,
  ⟨"tests/test_responses.py::test_head_method", "HEAD has no body", do
    let r ← TestClient.call (respApp (Response "hello, world" (media_type := "text/plain"))) "HEAD" "/"
    ok (r.text == "")⟩,
  ⟨"tests/test_responses.py::test_empty_response", "an empty response", do
    let r ← TestClient.get (respApp (Response)) "/"
    ok (r.content.size == 0 && r.headers.get? "content-length" == some "0" && !r.headers.contains "content-type")⟩,
  ⟨"tests/test_responses.py::test_empty_204_response", "204 has no content-length", do
    let r ← TestClient.get (respApp (Response (status_code := 204))) "/"
    ok (!r.headers.contains "content-length")⟩,
  ⟨"tests/test_responses.py::test_non_empty_response", "content-length of a body", do
    let r ← TestClient.get (respApp (Response "hi")) "/"
    ok (r.headers.get? "content-length" == some "2")⟩,
  ⟨"tests/test_responses.py::test_response_do_not_add_redundant_charset", "no second charset", do
    let r ← TestClient.get (respApp (Response (media_type := "text/plain; charset=utf-8"))) "/"
    ok (r.headers.get? "content-type" == some "text/plain; charset=utf-8")⟩,
  ⟨"starlette/responses.py:JSONResponse.render (json.dumps allow_nan=False)", "NaN is refused with a 500", do
    -- Starlette 1.8.0: JSONResponse({"x": float("nan")}) raises ValueError
    -- ("Out of range float values are not JSON compliant"), so the request is a 500.
    let r ← TestClient.get (respApp (JSONResponse (json% {"x": (Json.num .nan)}))) "/"
    ok (r.status_code == 500 && r.text == "Internal Server Error" &&
      (match Responses.jsonRender (json% {"x": (Json.num .inf)}) with
        | .error m => m == "Out of range float values are not JSON compliant" | .ok _ => false))⟩,
  ⟨"starlette/responses.py:Response.init_headers (UP-028)", "a 204 sends no body", do
    let r ← TestClient.get (respApp (Response "hello" (status_code := 204))) "/"
    ok (r.status_code == 204 && r.content.size == 0)⟩
]

/-! ## tests/test_requests.py -/

def echoApp (f : Request → AppM Json) : Application := .ofApp fun req => do
  return JSONResponse (← f req)

def requestCases : List Case := [
  ⟨"tests/test_requests.py::test_request_url", "request.url", do
    let a := echoApp fun r => pure (json% {"method": (r.method), "url": (toString r.url)})
    let r1 ← TestClient.get a "/123?a=abc"
    let r2 ← TestClient.get a "https://example.org:123/"
    ok (jsonEq r1.json (json% {"method": "GET", "url": "http://testserver/123?a=abc"}) &&
      jsonEq r2.json (json% {"method": "GET", "url": "https://example.org:123/"}))⟩,
  ⟨"tests/test_requests.py::test_request_query_params", "request.query_params", do
    let a := echoApp fun r => pure (Json.obj #[("params", Json.obj (r.queryParams.dictItems.map fun (k, v) => (k, Json.str v)).toArray)])
    let r ← TestClient.get a "/?a=123&b=456"
    ok (jsonEq r.json (json% {"params": {"a": "123", "b": "456"}}))⟩,
  ⟨"tests/test_requests.py::test_request_headers", "request.headers", do
    let a := echoApp fun r => pure (Json.obj #[("headers", Json.obj (r.headers.dict.map fun (k, v) => (k, Json.str v)).toArray)])
    let r ← TestClient.get a "/" (headers := [("host", "example.org")])
    ok (jsonEq r.json (json% {"headers": {"accept": "*/*", "accept-encoding": "gzip, deflate, zstd",
      "connection": "keep-alive", "user-agent": "testclient", "host": "example.org"}}))⟩,
  ⟨"tests/test_requests.py::test_request_client", "request.client", do
    ok ((({ client := some ("client", 42) } : Request).clientOf == some ("client", 42)) &&
      (({} : Request).clientOf == none))⟩,
  ⟨"tests/test_requests.py::test_request_body", "request.body()", do
    let a := echoApp fun r => do return json% {"body": (String.fromUTF8? (← r.body) |>.getD "")}
    let r1 ← TestClient.get a "/"
    let r2 ← TestClient.post a "/" "{\"a\":\"123\"}"
    let r3 ← TestClient.post a "/" "abc"
    ok (jsonEq r1.json (json% {"body": ""}) && jsonEq r2.json (json% {"body": "{\"a\":\"123\"}"}) &&
      jsonEq r3.json (json% {"body": "abc"}))⟩,
  ⟨"tests/test_requests.py::test_request_json", "request.json()", do
    let a := echoApp fun r => do return json% {"json": (← r.json)}
    let r ← TestClient.post a "/" "{\"a\":\"123\"}"
    ok (jsonEq r.json (json% {"json": {"a": "123"}}))⟩,
  ⟨"starlette/requests.py:Request.json (deviation: 400, not 500)", "invalid and too-deep JSON bodies are a 400", do
    let a := echoApp fun r => do return json% {"json": (← r.json)}
    let r1 ← TestClient.post a "/" "{"
    let deep := String.ofList (List.replicate 100000 '[') ++ String.ofList (List.replicate 100000 ']')
    let r2 ← TestClient.post a "/" deep
    ok (r1.status_code == 400 && r2.status_code == 400)⟩,
  ⟨"tests/test_requests.py::test_request_url (percent-decoded path)", "the path is percent-decoded", do
    let a := echoApp fun r => pure (json% {"path": (r.path)})
    let r ← TestClient.get a "/a%20b%E2%82%AC"
    ok (jsonEq r.json (json% {"path": "/a b€"}))⟩
]

/-! ## tests/test_datastructures.py -/

def datastructureCases : List Case := [
  ⟨"tests/test_datastructures.py::test_url", "URL components", do
    let u := URL.parse "https://example.org:123/path/to/somewhere?abc=123#anchor"
    ok (u.scheme == "https" && u.hostname == some "example.org" && u.netloc == "example.org:123" &&
      u.path == "/path/to/somewhere" && u.query == "abc=123" && u.fragment == "anchor" &&
      toString { u with scheme := "http" } == "http://example.org:123/path/to/somewhere?abc=123#anchor")⟩,
  ⟨"tests/test_datastructures.py::test_url_query_params", "include/replace/remove query params", do
    let u := URL.parse "https://example.org/path/?page=3"
    ok (u.query == "page=3" &&
      toString (u.includeQueryParams [("page", "4")]) == "https://example.org/path/?page=4" &&
      toString (u.includeQueryParams [("search", "testing")]) == "https://example.org/path/?page=3&search=testing" &&
      toString (u.replaceQueryParams [("order", "name")]) == "https://example.org/path/?order=name" &&
      toString (u.removeQueryParams ["page"]) == "https://example.org/path/")⟩,
  ⟨"tests/test_datastructures.py::test_headers", "case-insensitive multidict", do
    let h := Headers.ofList [("a", "123"), ("a", "456"), ("b", "789")]
    ok (h.contains "a" && h.contains "A" && h.contains "b" && h.contains "B" && !h.contains "c" &&
      h["a"]? == some "123" && h.get? "nope" == none && h.getlist "a" == ["123", "456"] &&
      h.keys == ["a", "a", "b"] && h.values == ["123", "456", "789"] &&
      h.dict == [("a", "123"), ("b", "789")] &&
      (Headers.ofList [("a", "123"), ("b", "789")])["A"]? == some "123")⟩,
  ⟨"tests/test_datastructures.py::test_mutable_headers", "set, setdefault, delete", do
    let h := Headers.empty.set "a" "1"
    let h2 := h.set "a" "2"
    let h3 := (h2.setdefault "a" "3").setdefault "b" "4"
    let h4 := h3.delete "a"
    ok (h.dict == [("a", "1")] && h2.dict == [("a", "2")] && h3.dict == [("a", "2"), ("b", "4")] &&
      h4.raw == [("b", "4")])⟩,
  ⟨"tests/test_datastructures.py::test_mutable_headers_update", "update", do
    let h := Headers.empty.update [("a", "1"), ("b", "2")]
    ok (h.dict == [("a", "1"), ("b", "2")])⟩,
  ⟨"tests/test_datastructures.py::test_url_blank_params", "blank query values", do
    let q := QueryParams.parse "a=123&abc&def&b=456"
    ok (q.contains "a" && q.contains "abc" && q.contains "def" && q.contains "b" &&
      q.get? "abc" == some "" && (q["a"]?.map String.length) == some 3 && q.keys == ["a", "abc", "def", "b"])⟩,
  ⟨"tests/test_datastructures.py::test_queryparams", "query multidict", do
    let q := QueryParams.parse "a=123&a=456&b=789"
    ok (q.contains "a" && !q.contains "A" && !q.contains "c" && q["a"]? == some "456" &&
      q.get? "nope" == none && q.getlist "a" == ["123", "456"] && q.keys == ["a", "b"] &&
      q.values == ["456", "789"] && q.dictItems == [("a", "456"), ("b", "789")] &&
      toString q == "a=123&a=456&b=789")⟩
]

/-! ## tests/test_exceptions.py -/

def raiseHTTP (e : Exception) : App := fun _ => throw e

def badBodyHandler : ExceptionHandler := fun req _ => do
  return JSONResponse (json% {"body": (String.fromUTF8? (← req.body) |>.getD "")}) (status_code := 422)

def exceptionsApp : Application := Starlette (routes := [
    Route "/runtime_error" (fun (_ : Request) => (throw (IO.userError "Yikes") : IO Response)),
    Route "/not_acceptable" (raiseHTTP (HTTPException 406)),
    Route "/no_content" (raiseHTTP (HTTPException 204)),
    Route "/not_modified" (raiseHTTP (HTTPException 304)),
    Route "/with_headers" (raiseHTTP (HTTPException 200 (headers := [("x-potato", "always")]))),
    Route "/non_standard_status_code" (raiseHTTP (HTTPException 499)),
    Route "/consume_body_in_endpoint_and_handler" (methods := ["POST"])
      (fun (req : Request) => do let _ ← req.body; (throw (Exception.custom "BadBodyException" "" .null) : AppM Response))])
  (exception_handlers := [(.kind "BadBodyException", badBodyHandler)])

def exceptionCases : List Case := [
  ⟨"tests/test_exceptions.py::test_not_acceptable", "406", do
    let r ← TestClient.get exceptionsApp "/not_acceptable"
    ok (r.status_code == 406 && r.text == "Not Acceptable")⟩,
  ⟨"tests/test_exceptions.py::test_no_content", "204", do
    let r ← TestClient.get exceptionsApp "/no_content"
    ok (r.status_code == 204 && !r.headers.contains "content-length")⟩,
  ⟨"tests/test_exceptions.py::test_not_modified", "304", do
    let r ← TestClient.get exceptionsApp "/not_modified"
    ok (r.status_code == 304 && r.text == "")⟩,
  ⟨"tests/test_exceptions.py::test_with_headers", "headers of an HTTPException", do
    let r ← TestClient.get exceptionsApp "/with_headers"
    ok (r.status_code == 200 && r.headers.get? "x-potato" == some "always")⟩,
  ⟨"tests/test_exceptions.py::test_non_standard_status_code", "499", do
    let r ← TestClient.get exceptionsApp "/non_standard_status_code"
    ok (r.status_code == 499 && r.text == "")⟩,
  ⟨"tests/test_exceptions.py::test_consume_request_body_in_endpoint_and_handler", "a handler reads the body", do
    let r ← TestClient.post exceptionsApp "/consume_body_in_endpoint_and_handler" "foobar"
    ok (r.status_code == 422 && jsonEq r.json (json% {"body": "foobar"}))⟩,
  ⟨"tests/test_exceptions.py::test_http_str", "str(HTTPException)", do
    ok (toString (HTTPException 404) == "404: Not Found" &&
      toString (HTTPException 404 "Not Found: foo") == "404: Not Found: foo" &&
      toString (HTTPException 404 (headers := [("key", "value")])) == "404: Not Found")⟩
]

/-! ## tests/test_applications.py and tests/middleware/test_errors.py -/

def userPage (r : Request) : Response := PlainTextResponse s!"Hello, {r.pathParams["username"]!}!"

def appApp : Application := Starlette
  (routes := [
    Route "/func" (fun (_ : Request) => PlainTextResponse "Hello, world!") (name := "func_homepage"),
    Route "/500" (fun (_ : Request) => (throw (IO.userError "Runtime error") : IO Response)),
    Mount "/users" (routes := [Route "/" (fun (_ : Request) => PlainTextResponse "Hello, everyone!"),
      Route "/{username}" userPage])])
  (exception_handlers := [
    (500, fun _ _ => pure (JSONResponse (json% {"detail": "Server Error"}) (status_code := 500))),
    (405, fun _ _ => pure (JSONResponse (json% {"detail": "Custom message"}) (status_code := 405))),
    (.httpException, fun _ e => match e with
      | .http s d _ h => pure (JSONResponse (json% {"detail": (d)}) s (h := h))
      | e => throw e)])

def error500 : ExceptionHandler := fun _ _ =>
  pure (JSONResponse (json% {"detail": "Server Error"}) (status_code := 500))

def failing : App := fun _ => (throw (IO.userError "Something went wrong") : IO Response)

def applicationCases : List Case := [
  ⟨"tests/test_applications.py::test_url_path_for", "app.url_path_for", do
    ok (urlPath appApp "func_homepage" == some "/func")⟩,
  ⟨"tests/test_applications.py::test_func_route", "GET and HEAD", do
    let r ← TestClient.get appApp "/func"
    let h ← TestClient.call appApp "HEAD" "/func"
    ok (r.status_code == 200 && r.text == "Hello, world!" && h.status_code == 200 && h.text == "")⟩,
  ⟨"tests/test_applications.py::test_mounted_route", "a mounted router", do
    let r ← TestClient.get appApp "/users/"
    ok (r.status_code == 200 && r.text == "Hello, everyone!")⟩,
  ⟨"tests/test_applications.py::test_mounted_route_path_params", "mounted path params", do
    let r ← TestClient.get appApp "/users/tomchristie"
    ok (r.status_code == 200 && r.text == "Hello, tomchristie!")⟩,
  ⟨"tests/test_applications.py::test_400", "a custom HTTPException handler on 404", do
    let r ← TestClient.get appApp "/404"
    ok (r.status_code == 404 && jsonEq r.json (json% {"detail": "Not Found"}))⟩,
  ⟨"tests/test_applications.py::test_405", "a status handler on 405", do
    let r ← TestClient.post appApp "/func"
    ok (r.status_code == 405 && jsonEq r.json (json% {"detail": "Custom message"}))⟩,
  ⟨"tests/test_applications.py::test_500", "the 500 handler", do
    let r ← TestClient.get appApp "/500"
    ok (r.status_code == 500 && jsonEq r.json (json% {"detail": "Server Error"}))⟩,
  ⟨"tests/middleware/test_errors.py::test_handler", "ServerErrorMiddleware with a handler", do
    let a : Application := { Application.ofApp failing with exception_handlers := [(.exception, error500)] }
    let r ← TestClient.get a "/"
    ok (r.status_code == 500 && jsonEq r.json (json% {"detail": "Server Error"}))⟩,
  ⟨"tests/middleware/test_errors.py::test_debug_text", "debug as text", do
    let a : Application := { Application.ofApp failing with debug := true }
    let r ← TestClient.get a "/"
    ok (r.status_code == 500 && ((r.headers.get? "content-type").getD "").startsWith "text/plain" &&
      (r.text.splitOn "RuntimeError: Something went wrong").length > 1)⟩,
  ⟨"tests/middleware/test_errors.py::test_debug_html", "debug as HTML", do
    let a : Application := { Application.ofApp failing with debug := true }
    let r ← TestClient.get a "/" (headers := [("Accept", "text/html, */*")])
    ok (r.status_code == 500 && ((r.headers.get? "content-type").getD "").startsWith "text/html" &&
      (r.text.splitOn "RuntimeError").length > 1)⟩,
  ⟨"starlette/middleware/body_limit.py (max_body_size)", "a body over max_body_size is 413", do
    let a := Starlette (routes := [Route "/" (fun (_ : Request) => PlainTextResponse "ok") (methods := ["POST"])])
      (max_body_size := some 4)
    let r1 ← TestClient.post a "/" "abcd"
    let r2 ← TestClient.post a "/" "abcde"
    ok (r1.status_code == 200 && r2.status_code == 413)⟩
]

/-! ## Through `Std.Http` -/

def raw (a : Application) (s : String) : IO String := do
  return (String.fromUTF8? (← a.exchange s.toUTF8)).getD ""

def contains (s t : String) : Bool := (s.splitOn t).length > 1

def transportCases : List Case := [
  ⟨"tests/test_routing.py::test_router [std.http]", "GET over HTTP/1.1", do
    let out ← raw routingApp "GET /users/tom HTTP/1.1\r\nHost: testserver\r\nConnection: close\r\n\r\n"
    ok (out.startsWith "HTTP/1.1 200 OK" && contains out "Content-Length: 8" && out.endsWith "User tom")⟩,
  ⟨"tests/test_routing.py::test_router [std.http]", "405 with Allow over HTTP/1.1", do
    let out ← raw routingApp "POST / HTTP/1.1\r\nHost: testserver\r\nContent-Length: 3\r\nConnection: close\r\n\r\nabc"
    ok (out.startsWith "HTTP/1.1 405" && contains out "Allow: GET, HEAD" && out.endsWith "Method Not Allowed")⟩,
  ⟨"tests/test_responses.py::test_head_method [std.http]", "HEAD keeps the length, drops the body", do
    let out ← raw routingApp "HEAD / HTTP/1.1\r\nHost: testserver\r\nConnection: close\r\n\r\n"
    ok (out.startsWith "HTTP/1.1 200 OK" && contains out "Content-Length: 12" && out.endsWith "\r\n\r\n")⟩,
  ⟨"tests/test_requests.py::test_request_json [std.http]", "a JSON body over HTTP/1.1", do
    let a := echoApp fun r => do return json% {"json": (← r.json)}
    let out ← raw a "POST / HTTP/1.1\r\nHost: x\r\nContent-Length: 11\r\nConnection: close\r\n\r\n{\"a\":\"123\"}"
    ok (out.startsWith "HTTP/1.1 200 OK" && out.endsWith "{\"json\":{\"a\":\"123\"}}")⟩,
  ⟨"UP-030 [std.http]", "a trailing %0A is not the same path", do
    let out ← raw routingApp "GET /func%0A HTTP/1.1\r\nHost: testserver\r\nConnection: close\r\n\r\n"
    ok (out.startsWith "HTTP/1.1 404")⟩
]

/-! ## Over a real socket

`Application.run` on a local port, driven with raw bytes. Expected values
were measured against uvicorn 0.54 (httptools) serving the same app under
Starlette 1.8.0; where lean-starlette answers differently it is a recorded
deviation (`docs/traceability.toml`, `transport.limits`). -/

open Std.Async Std.Async.TCP in
/-- Send raw bytes to `127.0.0.1:port` and read the response until the
server closes the connection. -/
def sendRaw (port : Nat) (raw : ByteArray) : IO String := do
  let res ← Async.block do
    let c ← (Socket.Client.mk : IO Socket.Client)
    c.connect (.v4 ⟨(Std.Net.IPv4Addr.ofString "127.0.0.1").get!, port.toUInt16⟩)
    -- send concurrently: a server may answer and close before reading it all
    background (try c.sendAll #[raw] catch _ => pure ())
    let rec loop (acc : ByteArray) : Nat → Async ByteArray
      | 0 => pure acc
      | n + 1 => do
        match ← (try c.recv? 65536 catch _ => pure none) with
        | some d => if d.size == 0 then pure acc else loop (acc ++ d) n
        | none => pure acc
    loop .empty 100000
  return (String.fromUTF8? res).getD ""

def echoParts (r : Request) : Response :=
  JSONResponse (json% {"n_query": (r.queryParams.multiItems.length), "n_headers": (r.headers.raw.length),
    "q": (String.ofList ((toString r.queryParams).toList.take 20))})

def socketApp : Application := Starlette (routes := [Route "/{p:path}" echoParts (methods := ["GET", "POST"])])

def socketPort : Nat := 18731

def getRaw (target : String) (headers : List String := []) : ByteArray :=
  (s!"GET {target} HTTP/1.1\r\nHost: x\r\nConnection: close\r\n" ++
    String.join (headers.map (· ++ "\r\n")) ++ "\r\n").toUTF8

def manyHeaders (n : Nat) : List String := (List.range n).map fun i => s!"x-h{i}: v"

def statusIs (out : String) (code : String) : Bool := out.startsWith s!"HTTP/1.1 {code}"
def has (out t : String) : Bool := (out.splitOn t).length > 1

def socketCases : List Case := [
  ⟨"uvicorn+starlette: 101 query parameters are 200 [socket]", "101 query parameters", do
    let q := "&".intercalate ((List.range 101).map fun i => s!"k{i}=1")
    let out ← sendRaw socketPort (getRaw s!"/a?{q}")
    ok (statusIs out "200" && has out "\"n_query\":101")⟩,
  ⟨"uvicorn+starlette (fastapi review): 150 query parameters are 200 [socket]", "150 query parameters", do
    let q := "&".intercalate ((List.range 150).map fun i => s!"k{i}=1")
    let out ← sendRaw socketPort (getRaw s!"/a?{q}")
    ok (statusIs out "200" && has out "\"n_query\":150")⟩,
  ⟨"uvicorn+starlette: 1000 query parameters are 200 [socket]", "1000 query parameters", do
    let q := "&".intercalate ((List.range 1000).map fun i => s!"k{i}=1")
    let out ← sendRaw socketPort (getRaw s!"/a?{q}")
    ok (statusIs out "200" && has out "\"n_query\":1000")⟩,
  ⟨"uvicorn+starlette: ?a=%ZZ is 200, kept as text [socket]", "an invalid escape", do
    let out ← sendRaw socketPort (getRaw "/a?a=%ZZ")
    ok (statusIs out "200" && has out "\"q\":\"a=%25ZZ\"")⟩,
  ⟨"uvicorn+starlette: 60 headers are 200 [socket]", "60 headers", do
    let out ← sendRaw socketPort (getRaw "/a" (manyHeaders 60))
    ok (statusIs out "200" && has out "\"n_headers\":62")⟩,
  ⟨"uvicorn+starlette: 2000 headers are 200 [socket]", "2000 headers", do
    let out ← sendRaw socketPort (getRaw "/a" (manyHeaders 2000))
    ok (statusIs out "200" && has out "\"n_headers\":2002")⟩,
  ⟨"uvicorn+starlette: a 70 KB header value is 200 [socket]", "a 70 KB header value", do
    let out ← sendRaw socketPort (getRaw "/a" [s!"x: {String.ofList (List.replicate 70000 'v')}"])
    ok (statusIs out "200")⟩,
  ⟨"uvicorn+starlette: a 65535-byte target is 200 [socket]", "the longest target", do
    let out ← sendRaw socketPort (getRaw ("/" ++ String.ofList (List.replicate 65534 'a')))
    ok (statusIs out "200")⟩,
  ⟨"transport.limits (uvicorn: 400): a 65536-byte target is 414 [socket]", "one byte longer is 414", do
    let out ← sendRaw socketPort (getRaw ("/" ++ String.ofList (List.replicate 65535 'a')))
    ok (statusIs out "414" && out.endsWith "URI Too Long")⟩,
  ⟨"uvicorn (httptools: 200; h11 0.16: 200) a head of 16 KiB - 1 is 200 [socket]", "just under h11's 16 KiB", do
    let raw := getRaw "/a" [s!"x: {String.ofList (List.replicate (16 * 1024 - 1 - (getRaw "/a" ["x: "]).size) 'v')}"]
    let out ← sendRaw socketPort raw
    ok (raw.size == 16 * 1024 - 1 && statusIs out "200")⟩,
  ⟨"transport.limits (httptools: 200; h11 0.16: 431) a head of 16 KiB + 1 is 200 [socket]", "just over h11's 16 KiB", do
    let raw := getRaw "/a" [s!"x: {String.ofList (List.replicate (16 * 1024 + 1 - (getRaw "/a" ["x: "]).size) 'v')}"]
    let out ← sendRaw socketPort raw
    ok (raw.size == 16 * 1024 + 1 && statusIs out "200")⟩,
  ⟨"transport.limits (httptools: 200) a head of exactly 1 MiB is 200 [socket]", "the largest head", do
    let raw := getRaw "/a" [s!"x: {String.ofList (List.replicate (1024 * 1024 - (getRaw "/a" ["x: "]).size) 'v')}"]
    let out ← sendRaw socketPort raw
    ok (raw.size == 1024 * 1024 && statusIs out "200")⟩,
  ⟨"transport.limits (httptools: 200; h11 0.16: 431) a head of 1 MiB + 1 is 431 [socket]", "one byte over 1 MiB", do
    let raw := getRaw "/a" [s!"x: {String.ofList (List.replicate (1024 * 1024 + 1 - (getRaw "/a" ["x: "]).size) 'v')}"]
    let out ← sendRaw socketPort raw
    ok (raw.size == 1024 * 1024 + 1 && statusIs out "431" && out.endsWith "Request Header Fields Too Large")⟩,
  ⟨"transport.limits (uvicorn: 200): a 2 MiB head is 431 [socket]", "a head over 1 MiB is 431", do
    let out ← sendRaw socketPort (getRaw "/a" [s!"x: {String.ofList (List.replicate (2 * 1024 * 1024) 'v')}"])
    ok (statusIs out "431" && out.endsWith "Request Header Fields Too Large")⟩,
  ⟨"uvicorn+starlette: raw non-ASCII in the target is 400 [socket]", "raw non-ASCII", do
    let out ← sendRaw socketPort ("GET /é HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n".toUTF8)
    ok (statusIs out "400" && out.endsWith "Invalid HTTP request received.")⟩,
  ⟨"uvicorn+starlette: duplicate content-length is 400 [socket]", "duplicate content-length", do
    let out ← sendRaw socketPort ("POST /a HTTP/1.1\r\nHost: x\r\nContent-Length: 1\r\nContent-Length: 2\r\nConnection: close\r\n\r\nab".toUTF8)
    ok (statusIs out "400" && out.endsWith "Invalid HTTP request received.")⟩,
  ⟨"transport.limits (uvicorn: 200): no Host header is 400, as RFC 9112 requires [socket]", "no Host header", do
    let out ← sendRaw socketPort ("GET /a HTTP/1.1\r\nConnection: close\r\n\r\n".toUTF8)
    ok (statusIs out "400" && out.endsWith "Invalid HTTP request received.")⟩
]

/-! ## Golden responses recorded from Starlette 1.8.0 (`tests/golden/`) -/

def gUser (r : Request) : Response := Response ("User " ++ toString r.pathParams["username"]!) (media_type := "text/plain")
def gItem (r : Request) : Response :=
  JSONResponse (json% {"item_id": (r.pathParams["item_id"]!), "q": (r.queryParams["q"]?)})
def gEcho (r : Request) : Response :=
  JSONResponse (Json.obj #[("query", Json.arr (r.queryParams.multiItems.map fun (k, v) =>
    Json.arr #[.str k, .str v]).toArray), ("path", .str r.url.path)])
def gCreate (r : Request) : AppM Response := do
  return JSONResponse (← r.json) (status_code := 201)

/-- The app `tests/golden/record.py` records, in Lean. -/
def goldenApp : Application := Starlette (routes := [
  Route "/" homepage (methods := ["GET"]),
  Mount "/users" (routes := [Route "/" users, Route "/{username}" gUser]),
  Route "/items/{item_id:int}" gItem,
  Route "/echo/{rest:path}" gEcho,
  Route "/create" gCreate (methods := ["POST"]),
  Route "/teapot" (raiseHTTP (HTTPException 418 "I'm a teapot" [("X-Tea", "earl grey")])),
  Route "/nobody" (fun (_ : Request) => Response (status_code := 204)),
  Route "/html" (fun (_ : Request) => HTMLResponse "<h1>Hi</h1>"),
  Route "/old" (fun (_ : Request) => RedirectResponse "/new place")])

/-- Documented deviations from the recorded responses: the expected status
here instead of upstream's. -/
def goldenDeviations : List ((String × String × Option String) × Nat) :=
  [(("POST", "/create", some "{"), 400)]   -- Request.json: 400, not 500 (CONTRIBUTING.md)

def sameAllow (a b : String) : Bool :=
  let xs := a.splitOn ", "; let ys := b.splitOn ", "
  xs.length == ys.length && xs.all ys.contains

def goldenCase (line : Json) : Option Case := do
  let method ← (line.getObjVal? "method").bind Json.getStr?
  let url ← (line.getObjVal? "url").bind Json.getStr?
  let body := (line.getObjVal? "body").bind Json.getStr?
  let status ← (line.getObjVal? "status").bind Json.getInt?
  let headers := match line.getObjVal? "headers" with
    | some (.obj kvs) => kvs.toList.filterMap fun (p : String × Json) => p.2.getStr?.map (p.1, ·)
    | _ => []
  let content ← (line.getObjVal? "content").bind Json.getStr?
  pure ⟨"tests/golden/starlette-1.8.0.jsonl", s!"golden {method} {url}{if body.isSome then " (body)" else ""}", do
    let r ← TestClient.request goldenApp method url [] ((body.getD "").toUTF8) (follow := false)
    match goldenDeviations.lookup (method, url, body) with
    | some st => ok (r.status_code == st)
    | none =>
      let hs := headers.all fun (k, v) =>
        match r.headers.get? k with
        | some v' => if k == "allow" then sameAllow v v' else v == v'
        | none => false
      let extra := ["content-type", "content-length", "location", "allow", "x-tea"].all fun k =>
        headers.any (·.1 == k) || !r.headers.contains k
      unless r.status_code == status.toNat && hs && extra && r.text == content do
        IO.println s!"      got {r.status_code} {repr r.headers} {r.text.quote}"
      ok (r.status_code == status.toNat && hs && extra && r.text == content)⟩

def goldenCases : IO (List Case) := do
  let lines ← IO.FS.lines "tests/golden/starlette-1.8.0.jsonl"
  return lines.toList.filterMap fun l => (from_json l).toOption.bind fun j => goldenCase j.val

/-! ## Forms: golden from Starlette 1.8.0 (`tests/golden/record_forms.py`)

The apps are `tests/test_formparsers.py`'s, mounted in an application; each
case replays the recorded body (or rebuilds it from its recipe) and compares
the status and the response bytes. Each case is also bounded in time: at most
3x upstream's recorded time, and never under 20 ms. -/

/-- The JSON a test app returns for one form value. -/
def formValueJson (kind : String) (v : FormValue) : IO Json := do
  match v with
  | .text s => return .str s
  | .file f =>
    let content ← f.read
    let opt (o : Option String) : Json := match o with | some x => .str x | none => .null
    let mut kvs : Array (String × Json) := #[
      ("filename", opt f.filename),
      ("size", match ← f.size with | some n => .num (.int n) | none => .null),
      ("content", if kind == "sizes" then .num (.int content.size) else .str (String.fromUTF8! content)),
      ("content_type", opt f.content_type)]
    if kind == "headers" then
      kvs := kvs.push ("headers", .arr (f.headers.items.map fun (k, v) => Json.arr #[.str k, .str v]).toArray)
    return .obj kvs

/-- `make_app_max_parts(...)` with the output of `app`, `multi_items_app`,
`app_with_headers`, or `sizes`. -/
def formApp (kind : String) (lim : LeanMultipart.FormLimits) : Application :=
  Starlette (routes := [Route "/" (fun (r : Request) => do
    let data ← r.form (max_files := lim.maxFiles) (max_fields := lim.maxFields) (max_part_size := lim.maxPartSize)
    let mut out : Array (String × Json) := #[]
    if kind == "multi" then
      for k in data.keys do
        let vs ← (data.getlist k).mapM fun v => (formValueJson kind v : IO Json)
        out := out.push (k, .arr vs.toArray)
    else
      for (k, v) in data.items do
        out := out.push (k, ← (formValueJson kind v : IO Json))
    (data.close : IO Unit)
    return JSONResponse (Json.obj out) : Request → AppM Response) (methods := ["POST"])])

def formPart (name : String) (value : ByteArray) (filename : Option String := none) : ByteArray :=
  let disp := s!"form-data; name=\"{name}\"" ++ (filename.map (s!"; filename=\"{·}\"")).getD ""
  s!"--B\r\nContent-Disposition: {disp}\r\n\r\n".toUTF8 ++ value ++ "\r\n".toUTF8

def repeatBytes (b : ByteArray) (n : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (b.size * n)
  for _ in [0:n] do out := out ++ b
  return out

def xs (n : Nat) : ByteArray := ByteArray.mk (Array.replicate n 120)

/-- `recipe(r)` in `record_forms.py`, byte for byte. -/
def recipeBody (kind : String) (n : Nat) : ByteArray :=
  let close := "--B--\r\n".toUTF8
  match kind with
  | "urlFields" => if n == 0 then .empty else "a=1".toUTF8 ++ repeatBytes "&a=1".toUTF8 (n - 1)
  | "urlValue" => "a=".toUTF8 ++ xs n
  | "urlName" => xs n ++ "=1".toUTF8
  | "mpFields" => repeatBytes (formPart "f" "v".toUTF8) n ++ close
  | "mpFiles" => repeatBytes (formPart "f" "v".toUTF8 (some "f.txt")) n ++ close
  | "mpValue" => formPart "f" (xs n) ++ close
  | "mpFile" => formPart "f" (xs n) (some "big.txt") ++ close
  | _ => .empty

/-- Latin-1 text back to bytes. -/
def latin1Bytes (s : String) : ByteArray := ByteArray.mk (s.toList.map (fun c => c.toNat.toUInt8)).toArray

def formDataCases : List Case := [
  ⟨"tests/test_datastructures.py::test_upload_file_file_input", "UploadFile read, write, seek, size", do
    let f ← UploadFile.new "data".toUTF8 (filename := some "file") (size := some 4)
    let a ← f.read
    let s1 ← f.size
    f.write " and more data!".toUTF8
    let b ← f.read
    let s2 ← f.size
    f.seek 0
    let c ← f.read
    ok (a == "data".toUTF8 && s1 == some 4 && b.isEmpty && s2 == some 19 && c == "data and more data!".toUTF8)⟩,
  ⟨"tests/test_datastructures.py::test_upload_file_without_size", "UploadFile without a size keeps None", do
    let f ← UploadFile.new "data".toUTF8 (filename := some "file")
    let a ← f.read
    f.write " and more data!".toUTF8
    let s ← f.size
    f.seek 0
    let c ← f.read
    ok (a == "data".toUTF8 && s == none && c == "data and more data!".toUTF8)⟩,
  ⟨"tests/test_datastructures.py::test_upload_file_repr", "repr(UploadFile)", do
    let f ← UploadFile.new "data".toUTF8 (filename := some "file") (size := some 4)
    ok ((← f.repr) == "UploadFile(filename='file', size=4, headers=Headers({}))")⟩,
  ⟨"tests/test_datastructures.py::test_upload_file_repr_headers", "repr(UploadFile) with headers", do
    let f ← UploadFile.new "data".toUTF8 (filename := some "file") (headers := Headers.ofList [("foo", "bar")])
    ok ((← f.repr) == "UploadFile(filename='file', size=None, headers=Headers({'foo': 'bar'}))")⟩,
  ⟨"tests/test_datastructures.py::test_formdata", "FormData multi-dict", do
    let upload ← UploadFile.new "data".toUTF8 (filename := some "file") (size := some 4)
    let form : FormData := { multiItems := [("a", .text "123"), ("a", .text "456"), ("b", .file upload)] }
    let texts (vs : List FormValue) := vs.map fun v => v.text?
    let up ← upload.repr
    ok (form.contains "a" && !form.contains "A" && !form.contains "c" &&
      (form["a"]?.bind (·.text?)) == some "456" && (form.get? "nope").isNone &&
      texts (form.getlist "a") == [some "123", some "456"] && form.keys == ["a", "b"] &&
      texts form.values == [some "456", none] && (form.items.map (·.1)) == ["a", "b"] &&
      form.length == 2 &&
      (← form.repr) == "FormData([('a', '123'), ('a', '456'), ('b', " ++ up ++ ")])")⟩,
  ⟨"starlette FormData.close / UploadFile.close", "closing a form closes its uploads; a closed upload raises", do
    let f1 ← UploadFile.new "x".toUTF8
    let f2 ← UploadFile.new "y".toUTF8
    let form : FormData := { multiItems := [("a", .file f1), ("t", .text "v"), ("b", .file f2)] }
    form.close
    let raised ← try discard f1.read; pure false catch _ => pure true
    ok ((← f1.isClosed) && (← f2.isClosed) && raised)⟩,
  ⟨"tests/test_formparsers.py (form cleanup)", "a form over a limit opens no upload and is a 400", do
    let body := recipeBody "mpFiles" 1001
    let r ← TestClient.request (formApp "plain" {}) "POST" "/" [("content-type", "multipart/form-data; boundary=B")] body
    ok (r.status_code == 400 && r.text == "Too many files. Maximum number of files is 1000.")⟩
]

/-! ### Slow uploads over TCP -/

open Std.Async Std.Async.TCP in
/-- Send `pieces` to `127.0.0.1:port`, pausing `pauseMs` after each, and read
the response until the server closes; with `hold`, keep the connection open
after the last piece (a stalled client). Returns the response and the time
from connecting to the close. -/
def sendSlow (port : Nat) (pieces : List ByteArray) (pauseMs : UInt32) (hold : Bool := false) :
    IO (String × Nat) := do
  let t0 ← IO.monoMsNow
  let res ← Async.block do
    let c ← (Socket.Client.mk : IO Socket.Client)
    c.connect (.v4 ⟨(Std.Net.IPv4Addr.ofString "127.0.0.1").get!, port.toUInt16⟩)
    background do
      for p in pieces do
        try c.sendAll #[p] catch _ => pure ()
        (IO.sleep pauseMs : IO Unit)
      if hold then (IO.sleep 20000 : IO Unit)
    let rec loop (acc : ByteArray) : Nat → Async ByteArray
      | 0 => pure acc
      | n + 1 => do
        match ← (try c.recv? 65536 catch _ => pure none) with
        | some d => if d.size == 0 then pure acc else loop (acc ++ d) n
        | none => pure acc
    loop .empty 100000
  return ((String.fromUTF8? res).getD "", (← IO.monoMsNow) - t0)

def formPort : Nat := 18732
def stallPort : Nat := 18733

def postHead (ct : String) (len : Nat) : ByteArray :=
  s!"POST / HTTP/1.1\r\nHost: x\r\nConnection: close\r\nContent-Type: {ct}\r\nContent-Length: {len}\r\n\r\n".toUTF8

def slowUploadCases : List Case := [
  ⟨"uvicorn+starlette: a slow multipart upload (3 pieces, 300 ms apart) is served [socket]", "slow upload", do
    let body := formPart "a" "1".toUTF8 ++ formPart "f" "<file content>".toUTF8 (some "f.txt") ++ "--B--\r\n".toUTF8
    let third := body.size / 3
    let pieces := [postHead "multipart/form-data; boundary=B" body.size ++ body.extract 0 third,
      body.extract third (2 * third), body.extract (2 * third) body.size]
    let (out, ms) ← sendSlow formPort pieces 300
    ok (statusIs out "200" && out.endsWith
      "{\"a\":\"1\",\"f\":{\"filename\":\"f.txt\",\"size\":14,\"content\":\"<file content>\",\"content_type\":null}}" &&
      ms ≥ 600 && ms ≤ 5000)⟩,
  ⟨"transport.limits (uvicorn: waits): a body that stalls past lingeringTimeout closes the connection [socket]", "stalled upload", do
    let (out, ms) ← sendSlow stallPort [postHead "application/x-www-form-urlencoded" 100 ++ "a=1&b=".toUTF8] 50 (hold := true)
    IO.println s!"      closed after {ms} ms: {(out.splitOn "\r\n").headD ""}"
    ok (ms ≤ 4000 && !statusIs out "200")⟩
]

/-- Cases whose time is lean-multipart's urlencoded machine stepping byte by
byte through a field over 1 MiB (about 65 ms; Starlette 3 to 9 ms). Requested
from lean-multipart (note on 2z9q5ypdqzv5); until it lands they are bounded at
150 ms, and the 3x bound applies to every other case. -/
def formSlowCases : List String := [
  "test_urlencoded_field_exceeds_max_part_size_raise",
  "test_urlencoded_field_name_exceeds_max_part_size_raise",
  "hostile: a 20 MB urlencoded value"]

def formGoldenCase (line : Json) : Option Case := do
  let name ← (line.getObjVal? "name").bind Json.getStr?
  let kind ← (line.getObjVal? "kind").bind Json.getStr?
  let lim : LeanMultipart.FormLimits := match line.getObjVal? "limits" with
    | some l => {
        maxFiles := ((l.getObjVal? "max_files").bind Json.getInt?).map Int.toNat |>.getD 1000,
        maxFields := ((l.getObjVal? "max_fields").bind Json.getInt?).map Int.toNat |>.getD 1000,
        maxPartSize := ((l.getObjVal? "max_part_size").bind Json.getInt?).map Int.toNat |>.getD (1024 * 1024) }
    | none => {}
  let ct := (line.getObjVal? "content_type").bind Json.getStr?
  let body := match line.getObjVal? "body" with
    | some (.str s) => latin1Bytes s
    | some r => recipeBody (((r.getObjVal? "kind").bind Json.getStr?).getD "")
        ((((r.getObjVal? "n").bind Json.getInt?).map Int.toNat).getD 0)
    | none => .empty
  let status ← (line.getObjVal? "status").bind Json.getInt?
  let content ← (line.getObjVal? "content").bind Json.getStr?
  let bound := if formSlowCases.contains name then 150 else match line.getObjVal? "upstream_ms" with
    | some j => match (LeanJson.to_json j).val.toList.takeWhile (· != 46) with
      | ds => max 20 (3 * (String.fromUTF8! (ByteArray.mk ds.toArray)).toNat! + 3)
    | none => 20
  pure ⟨s!"tests/test_formparsers.py (golden, Starlette 1.8.0)", s!"form: {name}", do
    let headers := match ct with | some c => [("content-type", c)] | none => []
    let t0 ← IO.monoMsNow
    let r ← TestClient.request (formApp kind lim) "POST" "/" headers body
    let ms := (← IO.monoMsNow) - t0
    let good := r.status_code == status.toNat && r.text == content && ms ≤ bound
    unless good do
      IO.println s!"      got {r.status_code} in {ms} ms (bound {bound}) {(String.ofList (r.text.toList.take 300)).quote}"
      IO.println s!"      want {status} {(String.ofList (content.toList.take 300)).quote}"
    ok good⟩

def formGoldenCases : IO (List Case) := do
  let lines ← IO.FS.lines "tests/golden/forms-starlette-1.8.0.jsonl"
  return lines.toList.filterMap fun l => (from_json l).toOption.bind fun j => formGoldenCase j.val

/-! ## Bench bounds (CI), at about twice upstream's time

Upstream times measured on Starlette 1.8.0 / CPython 3.13 by the critic. -/

/-- `{"key000000": 0, ...}`: `n` keys, about 14 bytes each. -/
def wideObject (n : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (n * 16 + 2)
  out := out.push 123
  for i in [0:n] do
    if i > 0 then out := out.push 44
    let k := toString i
    out := out ++ s!"\"key{String.ofList (List.replicate (6 - k.length) '0')}{k}\":{i % 10}".toUTF8
  out.push 125

/-- Routes for the long-path bounds: an int capture, a capture before a
literal, a path capture before a literal. -/
def benchRoutes : Application := Starlette (routes := [
  Route "/items/{item_id:int}" (fun (_ : Request) => PlainTextResponse "item"),
  Route "/users/{name}/posts" (fun (_ : Request) => PlainTextResponse "posts"),
  Route "/files/{rest:path}/end" (fun (_ : Request) => PlainTextResponse "file")])

def benchCases : List Case := [
  ⟨"bench: request.json() on a 100k-key object (upstream 0.11 s; bound 0.25 s)", "100k-key 1.4 MB JSON body", do
    let body := wideObject 100000
    let app := Starlette (routes := [Route "/" (fun (r : Request) => do
      let j ← r.json
      let n := match j with | .obj kvs => kvs.size | _ => 0
      return PlainTextResponse (toString n) : Request → AppM Response) (methods := ["POST"])])
    let t0 ← IO.monoMsNow
    let r ← TestClient.request app "POST" "/" [("content-type", "application/json")] body
    let ms := (← IO.monoMsNow) - t0
    IO.println s!"      {body.size} bytes, {r.text} keys in {ms} ms"
    ok (body.size ≥ 1400000 && r.status_code == 200 && r.text == "100000" && ms ≤ 250)⟩,
  ⟨"bench: 65000-char non-matching paths (upstream 404 in 20 ms; bound 50 ms)", "long non-matching paths", do
    let a := String.ofList (List.replicate 64990 'a')
    let mut good := true
    for path in [s!"/items/{a}", s!"/users/{a}", s!"/users/{a}/post", s!"/files/{a}/end/x"] do
      let t0 ← IO.monoMsNow
      let r ← benchRoutes.call { path := path }
      let ms := (← IO.monoMsNow) - t0
      IO.println s!"      {path.length} chars: {r.status_code} in {ms} ms"
      good := good && r.status_code == 404 && ms ≤ 50
    ok good⟩,
  ⟨"bench + deviation UP-052: a 65000-digit int segment is 404 (upstream 500; bound 50 ms)", "65000-digit int segment", do
    let t0 ← IO.monoMsNow
    let r ← benchRoutes.call { path := s!"/items/{String.ofList (List.replicate 65000 '7')}" }
    let ms := (← IO.monoMsNow) - t0
    let r2 ← benchRoutes.call { path := s!"/items/{String.ofList (List.replicate 4300 '7')}" }
    IO.println s!"      {r.status_code} in {ms} ms; 4300 digits: {r2.status_code}"
    ok (r.status_code == 404 && ms ≤ 50 && r2.status_code == 200)⟩
]

/-! ## Files, static files, streaming, background tasks: golden from Starlette 1.8.0

`tests/golden/record_files.py` records `tests/golden/files-starlette-1.8.0.jsonl`
over the fixture below (every mtime 1700000000 s, frac.txt 1700000000.123456789 s).
The ETag is compared byte for byte; a multipart boundary is compared as `*`. -/

def filesFixture : List (String × String) := [
  ("static/example.txt", "0123456789abcdefghij"),
  ("static/index.html", "<h1>Index</h1>"),
  ("static/sub/index.html", "<h1>Sub</h1>"),
  ("static/404.html", "<h1>Custom 404</h1>"),
  ("secret.txt", "secret"),
  ("static/frac.txt", "fractional mtime"),
  ("static/x\\y.txt", "backslash name")]

/-- The mtime `touch -d` sets for a fixture file. -/
def fixtureMtime (rel : String) : String :=
  if rel == "static/frac.txt" then "@1700000000.123456789" else "@1700000000"

/-- Write the fixture under a fresh temporary directory; returns its path. -/
def makeFixture : IO String := do
  let root ← IO.FS.createTempDir
  for (rel, text) in filesFixture do
    let p := root / rel
    if let some d := p.parent then IO.FS.createDirAll d
    IO.FS.writeFile p text
    let _ ← IO.Process.output { cmd := "touch", args := #["-d", fixtureMtime rel, p.toString] }
  return root.toString

/-- The app `tests/golden/record_files.py` records, in Lean. -/
def filesApp (root : String) (log : IO.Ref (List Nat)) : Application :=
  let static := root ++ "/static"
  Starlette (routes := [
    Mount "/static" (app := StaticFiles static),
    Mount "/site" (app := StaticFiles static (html := true)),
    Route "/file" (fun (_ : Request) => FileResponse (static ++ "/example.txt")),
    Route "/stream" (fun (_ : Request) =>
      StreamingResponse (ContentStream.ofStrings ["a", "bb", "ccc"]) (media_type := some "text/plain")),
    Route "/bg" (fun (_ : Request) => do
      log.set []
      let tasks := [1, 2, 3].foldl (fun (t : BackgroundTasks) (i : Nat) => t.add_task (log.modify (· ++ [i])))
        (BackgroundTasks.new)
      return PlainTextResponse "ok" (background := tasks) : Request → AppM Response),
    Route "/bglog" (fun (_ : Request) => do
      return PlainTextResponse (",".intercalate ((← log.get).map toString)) : Request → AppM Response)])

def normHeader (k v : String) : String :=
  if k == "content-type" && v.startsWith "multipart/byteranges; boundary=" then
    "multipart/byteranges; boundary=*"
  else v

def filesKeep : List String :=
  ["content-type", "content-length", "content-range", "accept-ranges", "last-modified", "etag", "location", "allow"]

def filesGoldenCase (app : Application) (line : Json) : Option Case := do
  let method ← (line.getObjVal? "method").bind Json.getStr?
  let url ← (line.getObjVal? "url").bind Json.getStr?
  let strPairs (j : Option Json) : List (String × String) := match j with
    | some (.obj kvs) => kvs.toList.filterMap fun (p : String × Json) => p.2.getStr?.map (p.1, ·)
    | _ => []
  let hin := strPairs (line.getObjVal? "headers_in")
  let status ← (line.getObjVal? "status").bind Json.getInt?
  let headers := strPairs (line.getObjVal? "headers")
  let content := (line.getObjVal? "content").bind Json.getStr?
  pure ⟨"tests/golden/files-starlette-1.8.0.jsonl",
    s!"golden {method} {url}{if hin.isEmpty then "" else s!" {hin.map (·.1)}"}", do
    let r ← TestClient.request app method url hin (follow := false)
    let hs := headers.all fun (k, v) => (r.headers.get? k).map (normHeader k) == some v
    let extra := filesKeep.all fun k => headers.any (·.1 == k) || !r.headers.contains k
    let body := content.all (r.text == ·)
    let good := r.status_code == status.toNat && hs && extra && body
    unless good do
      IO.println s!"      got {r.status_code} {repr r.headers} {r.text.quote}"
    ok good⟩

def filesGoldenCases : IO (List Case) := do
  let root ← makeFixture
  let log ← IO.mkRef ([] : List Nat)
  let app := filesApp root log
  let lines ← IO.FS.lines "tests/golden/files-starlette-1.8.0.jsonl"
  return lines.toList.filterMap fun l => (from_json l).toOption.bind fun j => filesGoldenCase app j.val

def filesBehaviourCases (root : String) : List Case := [
  ⟨"tests/test_staticfiles.py::test_staticfiles_304_with_etag_match", "the file's own ETag is 304, weak or strong", do
    let app := Starlette (routes := [Mount "/static" (app := StaticFiles (root ++ "/static"))])
    let r ← TestClient.get app "/static/example.txt"
    let some etag := r.headers.get? "etag" | ok false
    let r2 ← TestClient.get app "/static/example.txt" (headers := [("if-none-match", etag)])
    let r3 ← TestClient.get app "/static/example.txt" (headers := [("if-none-match", s!"\"x\", W/{etag}")])
    ok (r.status_code == 200 && r2.status_code == 304 && r3.status_code == 304 && r2.text == "" &&
      r2.headers.get? "etag" == some etag && !r2.headers.contains "content-length")⟩,
  ⟨"tests/test_background.py::test_multi_tasks_failure_avoids_next_execution", "a failing task skips the rest", do
    let log ← IO.mkRef ([] : List Nat)
    let tasks := BackgroundTasks.new [log.modify (· ++ [1]), throw (IO.userError "boom"), log.modify (· ++ [3])]
    let r ← try tasks.run; pure true catch _ => pure false
    ok (!r && (← log.get) == [1])⟩
]

/-! ## Numbers from request input: Python's `int()` digit limit, linear time

Expected values measured on Starlette 1.8.0 / CPython 3.13
(`FileResponse._parse_range_header(h, 1000)`, `email.utils.parsedate`). Each
case also bounds the time, so a quadratic conversion fails here. -/

def rangesOf {n : Nat} : RangeDecision n → Option (List (Nat × Nat))
  | .ranges rs => some rs.ranges
  | _ => none

def isMalformed {n : Nat} : RangeDecision n → Bool
  | .malformed m => m == "Range header: range must be requested"
  | _ => false

def zeroText (n : Nat) : String := String.ofList (List.replicate n '0')

/-- Run `act`, failing it when it takes longer than `ms` milliseconds. -/
def within (ms : Nat) (act : Unit → Bool) : IO Bool := do
  let t0 ← IO.monoMsNow
  let b := act ()
  let t1 ← IO.monoMsNow
  pure (b && t1 - t0 ≤ ms)

def numericCases : List Case := [
  ⟨"starlette FileResponse._parse_range_header (int(), 4300 digits)", "a 4300-digit start is read", do
    within 50 fun _ => rangesOf (parseRangeHeader s!"bytes={zeroText 4299}5-" 1000) == some [(5, 1000)]⟩,
  ⟨"starlette FileResponse._parse_range_header (int(), 4300 digits)", "a 4300-digit end is read", do
    within 50 fun _ => rangesOf (parseRangeHeader s!"bytes=0-{zeroText 4299}5" 1000) == some [(0, 6)]⟩,
  ⟨"starlette FileResponse._parse_range_header (int() ValueError)", "a 4301-digit start is ignored: malformed", do
    within 50 fun _ => isMalformed (parseRangeHeader s!"bytes={zeroText 4300}5-" 1000)⟩,
  ⟨"starlette FileResponse._parse_range_header (int() ValueError)", "a 4301-digit end is ignored: malformed", do
    within 50 fun _ => isMalformed (parseRangeHeader s!"bytes=0-{zeroText 4300}5" 1000)⟩,
  ⟨"starlette FileResponse._parse_range_header (int() ValueError)", "a 1 MiB digit run is malformed, in linear time", do
    within 1000 fun _ => isMalformed (parseRangeHeader s!"bytes={String.ofList (List.replicate (1024 * 1024) '7')}-" 1000)⟩,
  ⟨"email.utils.parsedate (int(), 4300 digits)", "a 4300-digit year is read", do
    within 50 fun _ => (parseHttpDate s!"Sun, 06 Nov {zeroText 4296}1994 08:49:37 GMT").map (·.year) == some 1994⟩,
  ⟨"email.utils.parsedate (int() ValueError)", "a 4301-digit year is None", do
    within 50 fun _ => (parseHttpDate s!"Sun, 06 Nov {zeroText 4297}1994 08:49:37 GMT").isNone⟩,
  ⟨"email.utils.parsedate (int() ValueError)", "a 1 MiB year is None, in linear time", do
    within 1000 fun _ => (parseHttpDate s!"Sun, 06 Nov {String.ofList (List.replicate (1024 * 1024) '7')} 08:49:37 GMT").isNone⟩,
  ⟨"Host header port (uvicorn: any port text)", "a 1 MiB port is refused, in linear time", do
    within 1000 fun _ => !isValidPort (some (String.ofList (List.replicate (1024 * 1024) '7')))⟩
]

def cases : List Case :=
  routingCases ++ convertorCases ++ responseCases ++ requestCases ++ datastructureCases ++
    exceptionCases ++ applicationCases ++ transportCases ++ numericCases ++ benchCases

def main : IO UInt32 := do
  let mut failures := 0
  let golden ← goldenCases
  let filesGolden ← filesGoldenCases
  let filesBehaviour := filesBehaviourCases (← makeFixture)
  let formGolden ← formGoldenCases
  let _ ← IO.asTask (socketApp.run (port := socketPort)) .dedicated
  let _ ← IO.asTask ((formApp "plain" {}).run (port := formPort)) .dedicated
  let _ ← IO.asTask ((formApp "plain" {}).run (port := stallPort) (config := { lingeringTimeout := 1000 })) .dedicated
  IO.sleep 1500
  let cases := cases ++ golden ++ filesGolden ++ filesBehaviour ++ formGolden ++ formDataCases ++ socketCases ++ slowUploadCases
  for c in cases do
    let ok ← try c.run catch e => do IO.println s!"      {e}"; pure false
    IO.println s!"{if ok then "ok  " else "FAIL"}  {c.name}  [{c.upstream}]"
    (← IO.getStdout).flush
    unless ok do failures := failures + 1
  IO.println s!"{cases.length} cases, {failures} failing"
  -- the socket server task never ends; exit explicitly
  IO.Process.exit (if failures == 0 then 0 else 1)
