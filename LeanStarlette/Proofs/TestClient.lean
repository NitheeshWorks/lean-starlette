import LeanStarlette.RepoImpl.TestClient

/-!
# Proofs: the `TestClient` transport

What the application sees of a test request (`scopeRequest`) and what the
client gets back (`testResponse`): every request header reaches the
application with its name lower-cased; it always has a `host` header (the
request's own, else the URL's netloc); method, query and body pass through
unchanged; `server` falls back to the scheme's default port; a `HEAD`
response has no body and every other carries the application's.
-/

namespace LeanStarlette

theorem lowerAscii_lowerAscii (s : String) : lowerAscii (lowerAscii s) = lowerAscii s := by
  simp [lowerAscii, List.map_map, Function.comp_def, asciiLower_idem]

/-- Every request header reaches the application, its name lower-cased. -/
theorem scope_headers_complete (rootPath : String) (client : String × Nat) (r : LeanHttpx.Request)
    {k v : String} (h : (k, v) ∈ r.headers.raw) :
    (lowerAscii k, v) ∈ (scopeRequest rootPath client r).headers.raw := by
  simp only [scopeRequest, Headers.ofList, scopeHeaders, List.map_append, List.mem_append, List.mem_map]
  refine Or.inr ⟨(lowerAscii k, v), ⟨(k, v), h, rfl⟩, ?_⟩
  simp [lowerAscii, List.map_map, Function.comp_def, asciiLower_idem]

/-- The application always sees a `host` header: the request's own, or the
URL's netloc when it has none. -/
theorem scope_has_host (rootPath : String) (client : String × Nat) (r : LeanHttpx.Request) :
    ∃ v, ("host", v) ∈ (scopeRequest rootPath client r).headers.raw := by
  simp only [scopeRequest, Headers.ofList, scopeHeaders]
  by_cases hh : r.headers.raw.any (fun p => lowerAscii p.1 == "host") = true
  · obtain ⟨p, hp, he⟩ := List.any_eq_true.mp hh
    have he : lowerAscii p.1 = "host" := by simpa using he
    refine ⟨p.2, ?_⟩
    simp only [hh, ite_true, List.nil_append, List.map_map, List.mem_map]
    exact ⟨p, hp, by simp only [Function.comp_apply, he]; rfl⟩
  · refine ⟨r.url.netloc, ?_⟩
    simp only [hh, ite_false, Bool.false_eq_true]
    simp [lowerAscii, asciiLower]

/-- Method, query string, body, root path and client pass through; the
server is the URL's host and port, or the scheme's default port. -/
theorem scope_passthrough (rootPath : String) (client : String × Nat) (r : LeanHttpx.Request) :
    let q := scopeRequest rootPath client r
    q.method = r.method ∧ q.query_string = r.url.query ∧ q.bodyBytes = r.content ∧
      q.root_path = rootPath ∧ q.client = some client ∧
      q.server = some (r.url.host, r.url.port.getD (schemeDefaultPort r.url.scheme)) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A `HEAD` response has no body; any other carries the application's,
with its status and headers. -/
theorem test_response_body (method : String) (status : Nat) (headers : Headers) (body : ByteArray) :
    let r := testResponse method status headers body
    r.statusCode = status ∧ r.headers.raw = headers.raw ∧
      r.stream = some (if method == "HEAD" then .empty else body) :=
  ⟨rfl, rfl, rfl⟩

end LeanStarlette
