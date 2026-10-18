import LeanStarlette.RepoImpl.TestClient
import LeanHttpx.RepoImpl.Client

/-!
# `TestClient` (effectful)

`TestClient app` is an `httpx.Client` (lean-httpx's `Client`) over a
transport that calls the application in process, as Starlette's
`TestClient` is: `let client ← TestClient app; let r ← client.get "/"`, then
`r.statusCode`, `r.text`, `r.json`, `r.headers`, `client.cookies`. The
client part (URL merging, default headers, cookies, redirects, auth,
`Content-Encoding`) is lean-httpx's; what the transport computes is the pure
`scopeRequest` / `testResponse` (`RepoImpl/TestClient.lean`).
-/

namespace LeanStarlette

/-- `_TestClientTransport(app, raise_server_exceptions, root_path, client)`:
run the application on the request, read the whole response, run its
background tasks. With `raise_server_exceptions`, an exception that reached
`ServerErrorMiddleware` is re-raised after the response, as upstream. -/
def testClientTransport (app : Application) (raise_server_exceptions : Bool := true)
    (root_path : String := "") (client : String × Nat := ("testclient", 50000)) : LeanHttpx.Transport where
  handleRequest r := do
    let raised ← IO.mkRef (none : Option Exception)
    let resp ← app.call (scopeRequest root_path client r) (fun e => raised.set (some e))
    let body ← resp.readBody
    resp.background.run
    if raise_server_exceptions then
      if let some e ← raised.get then throw (IO.userError (toString e))
    return testResponse r.method resp.status_code resp.headers body

/-- **`TestClient(app, base_url="http://testserver", raise_server_exceptions=True,
root_path="", cookies=None, headers=None, follow_redirects=True,
client=("testclient", 50000))`**: an httpx client over the application.
Its `User-Agent` is `testclient` unless `headers` sets one. -/
def TestClient (app : Application) (base_url : String := "http://testserver")
    (raise_server_exceptions : Bool := true) (root_path : String := "")
    (cookies : LeanHttpx.Cookies := {}) (headers : List (String × String) := [])
    (follow_redirects : Bool := true) (client : String × Nat := ("testclient", 50000)) :
    IO LeanHttpx.Client :=
  LeanHttpx.Client.new (baseUrl := base_url) (cookies := cookies)
    (headers := (LeanHttpx.Headers.ofList [("user-agent", "testclient")]).update headers)
    (followRedirects := follow_redirects)
    (transport := some (testClientTransport app raise_server_exceptions root_path client))

end LeanStarlette
