import LeanStarlette.Specifications.Starlette

/-!
# Proofs: middleware

The stack order, `TrustedHostMiddleware`'s rejection, `HTTPSRedirect`'s
target and CORS preflights. The origin regex inherits Keel's laws: the
compiled pattern decides `Accepts` (`compile_test_iff`), which in
`Mode.full` is `Matches` on the whole origin (`accepts_full_iff`).
-/

namespace LeanStarlette

open Keel

theorem middleware_stack_order : Spec.MiddlewareStackOrder := fun _ _ _ => ⟨rfl, rfl⟩

theorem trusted_host_reject : Spec.TrustedHostReject := by
  intro hosts www r
  unfold trustedHostDecision
  by_cases hstar : hosts.contains "*" = true
  · have : "*" ∈ hosts := List.contains_iff_mem.mp hstar
    simp [this]
  · have hstar' : "*" ∉ hosts := fun h => hstar (List.contains_iff_mem.mpr h)
    simp only [hstar, Bool.false_eq_true, ite_false]
    cases hh : (r.headers.get? "host").bind parseHostHeader with
    | none => simp [hstar']
    | some hp =>
      obtain ⟨h, p⟩ := hp
      by_cases hany : hosts.any (hostMatches h) = true
      · simp only [hany, ite_true, reduceCtorEq, false_iff]
        obtain ⟨q, hq, hm⟩ := List.any_eq_true.mp hany
        rintro ⟨_, hcon⟩
        have := (hcon h p rfl).1 q hq
        simp [this] at hm
      · have hall : ∀ q ∈ hosts, hostMatches h q = false := by
          intro q hq; simpa using (List.any_eq_false.mp (by simpa using hany)) q hq
        simp only [hany, Bool.false_eq_true, ite_false]
        by_cases hw : (www && hosts.contains ("www." ++ h)) = true
        · simp only [hw, ite_true, reduceCtorEq, false_iff]
          rintro ⟨_, hcon⟩
          simp only [Bool.and_eq_true, List.contains_iff_mem] at hw
          exact (hcon h p rfl).2 hw
        · simp only [hw, Bool.false_eq_true, ite_false, true_iff]
          refine ⟨hstar', fun h' p' heq => ?_⟩
          cases heq
          refine ⟨hall, fun ⟨hw1, hw2⟩ => hw ?_⟩
          simp [hw1]
          exact hw2

theorem trusted_host_reject_400 : Spec.TrustedHostReject400 := by
  intro hosts www hv app r h
  simp only [TrustedHostMiddleware, h]

theorem https_redirect : Spec.HttpsRedirect := by
  intro app r
  refine ⟨fun hs hn => ?_, fun h1 h2 => ?_⟩
  · have hsch : (r.scheme == "http" || r.scheme == "ws") = true := by
      rcases hs with h | h <;> simp [h]
    simp only [HTTPSRedirectMiddleware, hsch, ite_true, httpsRedirectURL]
    have : r.url.netloc.isEmpty = false := by simpa [String.isEmpty_iff] using hn
    simp only [this, Bool.false_eq_true, ite_false]
  · have hsch : (r.scheme == "http" || r.scheme == "ws") = false := by simp [h1, h2]
    simp only [HTTPSRedirectMiddleware, hsch, Bool.false_eq_true, ite_false]

theorem preflight_status (c : CORSConfig) (h : Headers) :
    (c.preflight h).status_code = 200 ↔
      c.preflightFailures ((h.get? "origin").getD "") ((h.get? "access-control-request-method").getD "")
        (h.get? "access-control-request-headers") (h.get? "access-control-request-private-network") = [] := by
  rcases hf : c.preflightFailures ((h.get? "origin").getD "") ((h.get? "access-control-request-method").getD "")
    (h.get? "access-control-request-headers") (h.get? "access-control-request-private-network") with _ | ⟨f, fs⟩ <;>
    simp [CORSConfig.preflight, hf, PlainTextResponse, Response.make]

theorem preflightFailures_nil (c : CORSConfig) (o m : String) (rh pn : Option String) :
    c.preflightFailures o m rh pn = [] ↔
      c.isAllowedOrigin o = true ∧ m ∈ c.allowMethods ∧
      (∀ hs, rh = some hs → c.allowAllHeaders = true ∨ c.headersAllowed hs = true) ∧
      (pn.isSome → c.allowPrivateNetwork = true) := by
  unfold CORSConfig.preflightFailures
  cases rh <;> cases pn <;> cases c.allowAllHeaders <;> simp [List.append_eq_nil_iff]

theorem cors_preflight : Spec.CorsPreflight := by
  intro c app r hp
  refine ⟨by simp [corsMiddleware, hp], ?_⟩
  rw [preflight_status, preflightFailures_nil]

theorem cors_allowed_origin : Spec.CorsAllowedOrigin := by
  intro origins methods headers cred rx pn expose maxAge o
  cases rx with
  | none => simp [corsConfig, CORSConfig.isAllowedOrigin]
  | some p =>
    have h := Regex.compile_test_iff p.re .full o
    rw [← Regex.accepts_iff, Regex.accepts_full_iff] at h
    simp [corsConfig, CORSConfig.isAllowedOrigin, Regex.Matcher.test] at h ⊢
    simp [h, or_assoc]

end LeanStarlette
