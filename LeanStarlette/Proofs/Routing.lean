import LeanStarlette.APIs.Starlette

/-!
# Proofs: the router

Starlette's routing laws, as instances of `Keel.Route`'s general ones:

* `route_first_match`: the router hands over to the first route that matches
  fully (from `Keel.dispatch_found_iff`).
* `partial_iff_405`: it answers `405` exactly when no route matches fully and
  some route matches the path but not the method, and `Allow` is then
  `allowOf`, the union of those routes' methods (`mem_allowOf`).
* `no_match_404` and `redirect_slashes_307`: when nothing matches, a
  `redirect_slashes` redirect happens exactly when the path with its
  trailing slash toggled would match; otherwise `404`.
* `head_implies_get`: a route that allows `GET` treats `HEAD` exactly as
  `GET`.
* `compile_match_url_path_for` / `urlPathFor_match`: the URL of a route's
  captures routes back to them, and a canonical path is the URL of what it
  matched (from `Keel.match_urlFor` and `Keel.urlFor_match`).
-/

namespace LeanStarlette

open Keel

/-! ## First match, 405, 404 and the slash redirect -/

/-- **First match.** -/
theorem route_first_match (rs : List BaseRoute) (b : Bool) (req : Request) (c : Child) :
    Router.resolve rs b req = .found c ↔
      ∃ pre r post, rs = pre ++ r :: post ∧ r.matches req = .full c ∧
        ∀ r' ∈ pre, ¬ (r'.matches req).IsFull := by
  have hf := dispatch_found_iff (β := fun _ => Child) (BaseRoute.matches req) rs
  unfold Router.resolve
  cases hd : dispatch (β := fun _ => Child) (BaseRoute.matches req) rs with
  | found r c' =>
    simp only [Resolution.found.injEq]
    constructor
    · rintro rfl
      obtain ⟨pre, post, h1, h2, h3⟩ := (hf r c').mp hd
      exact ⟨pre, r, post, h1, h2, h3⟩
    · rintro ⟨pre, r', post, h1, h2, h3⟩
      have := (hf r' c).mpr ⟨pre, post, h1, h2, h3⟩
      rw [hd] at this; cases this; rfl
  | «partial» r =>
    simp only [reduceCtorEq, false_iff, not_exists, not_and]
    intro pre r' post h1 h2 h3
    have := (hf r' c).mpr ⟨pre, post, h1, h2, h3⟩
    rw [hd] at this; cases this
  | none =>
    constructor
    · simp only; split <;> intro h <;> cases h
    · rintro ⟨pre, r', post, h1, h2, h3⟩
      have := (hf r' c).mpr ⟨pre, post, h1, h2, h3⟩
      rw [hd] at this; cases this

/-- **405 iff partial match, with `Allow`.** The router answers
`Method Not Allowed` exactly when no route matches fully and some route
matches the path but not the method; `Allow` is then `allowOf`. -/
theorem partial_iff_405 (rs : List BaseRoute) (b : Bool) (req : Request) (allow : List String) :
    Router.resolve rs b req = .methodNotAllowed allow ↔
      (∀ r ∈ rs, ¬ (r.matches req).IsFull) ∧ (∃ r ∈ rs, r.matches req = .partial) ∧
        allow = allowOf rs req := by
  have hp := dispatch_partial_iff (β := fun _ => Child) (BaseRoute.matches req) rs
  unfold Router.resolve
  cases hd : dispatch (β := fun _ => Child) (BaseRoute.matches req) rs with
  | found r c =>
    simp only [reduceCtorEq, false_iff]
    rintro ⟨h1, h2, _⟩
    obtain ⟨r', hr'⟩ := hp.mpr ⟨h1, h2⟩
    rw [hd] at hr'; cases hr'
  | «partial» r =>
    simp only [Resolution.methodNotAllowed.injEq]
    have := hp.mp ⟨r, hd⟩
    constructor
    · rintro rfl; exact ⟨this.1, this.2, rfl⟩
    · rintro ⟨_, _, rfl⟩; rfl
  | none =>
    constructor
    · simp only; split <;> intro h <;> cases h
    · rintro ⟨h1, h2, _⟩
      obtain ⟨r', hr'⟩ := hp.mpr ⟨h1, h2⟩
      rw [hd] at hr'; cases hr'

theorem mem_dedup [BEq α] [LawfulBEq α] (xs : List α) (x : α) : x ∈ dedup xs ↔ x ∈ xs := by
  unfold dedup
  suffices ∀ acc, x ∈ xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) acc ↔
      x ∈ acc ∨ x ∈ xs by simpa using this []
  induction xs with
  | nil => simp
  | cons y ys ih =>
    intro acc
    simp only [List.foldl_cons, List.mem_cons]
    rw [ih]
    by_cases hc : acc.contains y = true
    · rw [ite_eq_left hc]
      have := List.contains_iff_mem.mp hc
      constructor
      · rintro (h | h) <;> simp_all
      · rintro (h | rfl | h) <;> simp_all
    · rw [ite_eq_right hc]
      simp only [List.mem_append, List.mem_singleton]
      constructor
      · rintro ((h | rfl) | h) <;> simp_all
      · rintro (h | rfl | h) <;> simp_all

/-- **What `Allow` lists**: every method of every partially matching route. -/
theorem mem_allowOf (rs : List BaseRoute) (req : Request) (m : String) :
    m ∈ allowOf rs req ↔ ∃ r ∈ rs, (r.matches req).isPartial = true ∧ m ∈ r.methodsOf := by
  unfold allowOf
  rw [mem_dedup]
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨r, hr, hm⟩
    split at hm
    · exact ⟨r, hr, ‹_›, hm⟩
    · simp at hm
  · rintro ⟨r, hr, hp, hm⟩
    exact ⟨r, hr, by simp [hp, hm]⟩

/-- **`redirect_slashes`**: with no match, the router redirects exactly when
the path with its trailing slash toggled would match, to that URL. -/
theorem redirect_slashes_307 (rs : List BaseRoute) (b : Bool) (req : Request) (url : String) :
    Router.resolve rs b req = .redirect url ↔
      (∀ r ∈ rs, r.matches req = .none) ∧ b = true ∧ req.routePath ≠ "/" ∧
        (∃ r ∈ rs, (r.matches (toggleSlash req)).isNone = false) ∧
        url = toString (toggleSlash req).url := by
  have hn := dispatch_none_iff (β := fun _ => Child) (BaseRoute.matches req) rs
  unfold Router.resolve
  constructor
  · intro h
    split at h
    · cases h
    · cases h
    · rename_i hd
      split at h
      · rename_i hc
        cases h
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, List.any_eq_true, Bool.not_eq_true'] at hc
        exact ⟨hn.mp hd, hc.1.1, hc.1.2, hc.2, rfl⟩
      · cases h
  · rintro ⟨h1, h2, h3, h4, rfl⟩
    rw [hn.mpr h1]
    simp only
    rw [ite_eq_left]
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, List.any_eq_true, Bool.not_eq_true']
    exact ⟨⟨h2, h3⟩, h4⟩

/-- **No match is a 404**, unless the slash redirect applies. -/
theorem no_match_404 (rs : List BaseRoute) (b : Bool) (req : Request) :
    Router.resolve rs b req = .notFound ↔
      (∀ r ∈ rs, r.matches req = .none) ∧
        ¬ (b = true ∧ req.routePath ≠ "/" ∧ ∃ r ∈ rs, (r.matches (toggleSlash req)).isNone = false) := by
  have hn := dispatch_none_iff (β := fun _ => Child) (BaseRoute.matches req) rs
  unfold Router.resolve
  constructor
  · intro h
    split at h
    · cases h
    · cases h
    · rename_i hd
      split at h
      · cases h
      · rename_i hc
        refine ⟨hn.mp hd, fun ⟨h2, h3, h4⟩ => hc ?_⟩
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, List.any_eq_true, Bool.not_eq_true']
        exact ⟨⟨h2, h3⟩, h4⟩
  · rintro ⟨h1, h2⟩
    rw [hn.mpr h1]
    simp only
    rw [ite_eq_right]
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, List.any_eq_true, Bool.not_eq_true']
    exact fun ⟨⟨a, b⟩, c⟩ => h2 ⟨a, b, c⟩

/-! ## HEAD implies GET -/

/-- **HEAD implies GET**: a route that allows `GET` matches a `HEAD`
request exactly as the same request with `GET`. -/
theorem head_implies_get (r : BaseRoute) (req : Request) (hg : r.allows "GET" = true) :
    r.matches { req with method := "HEAD" } = r.matches { req with method := "GET" } := by
  cases r with
  | route p rt n err hh =>
    have hh' : rt.allows "HEAD" = true := by
      simp only [BaseRoute.allows, Keel.Route.allows] at hg ⊢
      split at hg
      · rfl
      · rename_i ms hms
        simp only [List.contains_iff_mem] at hg ⊢; exact hh ms hms hg
    simp only [BaseRoute.allows] at hg
    simp only [BaseRoute.matches, Keel.Route.matches, Request.routePath, hg, hh']
  | mount => simp [BaseRoute.matches, Request.routePath]

/-- `Route` adds `HEAD` to `GET`, so every route it builds satisfies the
hypothesis of `head_implies_get` with `HEAD` allowed. -/
theorem route_allows_head {α : Type} [ToApp α] (p : String) (e : α) (ms : List String) (n : String)
    (hg : (Route p e ms n).allows "GET" = true) : (Route p e ms n).allows "HEAD" = true := by
  simp only [Route, BaseRoute.allows, Keel.Route.allows] at hg ⊢
  split at hg
  · rename_i h; split at h
    · simp
    · cases h
  · rename_i xs hxs
    split at hxs
    · cases hxs
    · cases hxs
      simp only [List.contains_iff_mem] at hg ⊢
      exact head_mem_normaliseMethods ms hg

/-! ## Templates: `url_path_for` and matching -/

theorem compileOr_ok {p : String} {t : PathTemplate} (h : PathTemplate.compile p = .ok t) :
    compileOr p = (t, none) := by
  simp [compileOr, h]

/-- **`url_path_for` then routing gives the captures back** (Starlette's
`test_url_path_for` round trip): for a route whose path compiles to a
segment-aligned template, the route matches the URL of any valid captures,
with those captures as its path parameters. -/
theorem compile_match_url_path_for {α : Type} [ToApp α] (p : String) (e : α) (ms : List String)
    (n : String) {t : PathTemplate} (hc : PathTemplate.compile p = .ok t) (hs : p.startsWith "/" = true)
    (ha : t.Aligned) (v : Args t.pieces) (hv : PathTemplate.ArgsValid t.pieces v)
    (req : Request) (hr : req.root_path = "") (hm : (Route p e ms n).allows req.method = true)
    (hp : req.path = t.urlFor v) :
    ∃ c, (Route p e ms n).matches req = .full c ∧
      c.params.items = req.path_params.items ++ namedParams t.pieces v := by
  have hroute : req.routePath = t.urlFor v := by simp [Request.routePath, hr, hp]
  simp only [Route, compileOr_ok hc, hs, ite_true] at hm ⊢
  simp only [BaseRoute.allows] at hm
  simp only [BaseRoute.matches, Option.isSome_none, Bool.false_eq_true, ite_false, Keel.Route.matches,
    hroute, PathTemplate.match_urlFor t ha v hv, hm, ite_true]
  exact ⟨_, rfl, rfl⟩

/-- **A canonical path is the URL of its match**: the captures a route
matches render back to the path itself when the path is in canonical form
(`7`, not `007`). -/
theorem urlPathFor_match (t : PathTemplate) {path : String} {v : Args t.pieces}
    (h : t.match path = some v) (hc : t.Canonical path) : t.urlFor v = path :=
  PathTemplate.urlFor_match t h hc

end LeanStarlette
