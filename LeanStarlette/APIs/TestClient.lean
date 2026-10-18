import LeanStarlette.Proofs.TestClient

/-!
# APIs: the test client's scope

`TestClient app` (`LeanStarlette/TestClient.lean`) is what tests call, as in
Starlette: `let client ← TestClient app; let r ← client.get "/"`. It is
lean-httpx's `Client`, so `r.statusCode`, `r.text`, `r.json`, `r.headers` and
`client.cookies` are httpx's. `testScope` is the request the application
sees for an httpx request, refined by what the transport guarantees.
-/

namespace LeanStarlette

/-- The request the application sees for an httpx request: every request
header present (name lower-cased), a `host` header, and the method, query
and body unchanged. -/
def testScope (rootPath : String) (client : String × Nat) (r : LeanHttpx.Request) :
    {q : Request // (∀ k v, (k, v) ∈ r.headers.raw → (lowerAscii k, v) ∈ q.headers.raw) ∧
      (∃ v, ("host", v) ∈ q.headers.raw) ∧
      q.method = r.method ∧ q.query_string = r.url.query ∧ q.bodyBytes = r.content} :=
  ⟨scopeRequest rootPath client r, fun _ _ h => scope_headers_complete rootPath client r h,
    scope_has_host rootPath client r, rfl, rfl, rfl⟩

end LeanStarlette
