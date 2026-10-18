import LeanStarlette.Proofs.Convertors

/-!
# Proofs: `url_path_for` and routing are inverse

`Template.match_urlFor`: routing the path `url_path_for` builds gives back the
parameters it was built from (as a dict). `Template.urlFor_match`: the
parameters a path routes to can be rendered, and render to a path that
routes to the same parameters. Both are proved once, for any template of
lawful convertors whose parameters are delimited (`Template.Separated`).
-/

namespace LeanStarlette

/-! ## Association-list facts -/

theorem lookup_mem {k : String} {v : PathValue} :
    ∀ {r : PathParams}, r.lookup k = some v → (k, v) ∈ r
  | [], h => by simp [List.lookup] at h
  | (k', v') :: r, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i hk; simp at hk h; subst hk; subst h; simp
    · exact List.mem_cons_of_mem _ (lookup_mem h)

theorem lookup_none {k : String} : ∀ {r : PathParams}, k ∉ r.map Prod.fst → r.lookup k = none
  | [], _ => rfl
  | (k', v') :: r, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [List.lookup]
    have : (k == k') = false := by simpa using h.1
    simp [this, lookup_none h.2]

theorem lookup_some_of_mem {k : String} : ∀ {r : PathParams}, k ∈ r.map Prod.fst →
    ∃ v, r.lookup k = some v
  | [], h => by simp at h
  | (k', v') :: r, h => by
    simp only [List.lookup]
    split
    · exact ⟨_, rfl⟩
    · rename_i hk
      simp only [List.map_cons, List.mem_cons] at h
      rcases h with rfl | h
      · simp at hk
      · exact lookup_some_of_mem h

theorem lookup_self {r : PathParams} (hn : (r.map Prod.fst).Nodup) :
    ∀ p ∈ r, r.lookup p.1 = some p.2 := by
  induction r with
  | nil => simp
  | cons q r ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    intro p hp
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · simp [List.lookup]
    · have hne : p.1 ≠ q.1 := fun e => hn.1 (e ▸ List.mem_map_of_mem hp)
      simp only [List.lookup]
      have : (p.1 == q.1) = false := by simpa using hne
      simp [this, ih hn.2 p hp]

/-- Two parameter lists with the same keys, in the same order and without
repeats, are equal when one's entries are found in the other. -/
theorem eq_of_keys {r ps : PathParams} (hk : r.map Prod.fst = ps.map Prod.fst)
    (hn : (ps.map Prod.fst).Nodup) (hl : ∀ p ∈ r, ps.lookup p.1 = some p.2) : r = ps := by
  induction r generalizing ps with
  | nil => cases ps <;> simp_all
  | cons q r ih =>
    cases ps with
    | nil => simp at hk
    | cons q' ps =>
      simp only [List.map_cons, List.cons.injEq] at hk
      simp only [List.map_cons, List.nodup_cons] at hn
      have h1 := hl q (by simp)
      simp only [List.lookup, hk.1, beq_self_eq_true, Option.some.injEq] at h1
      have hq : q = q' := Prod.ext hk.1 h1.symm
      subst hq
      congr 1
      apply ih hk.2 hn.2
      intro p hp
      have := hl p (List.mem_cons_of_mem _ hp)
      have hne : p.1 ≠ q.1 := fun e => hn.1 (by rw [← hk.2, ← e]; exact List.mem_map_of_mem hp)
      simp only [List.lookup] at this
      have hb : (p.1 == q.1) = false := by simpa using hne
      simpa [hb] using this

/-! ## Matching a rendered path -/

theorem isPrefixOf_append (l s : List Char) : l.isPrefixOf (l ++ s) = true :=
  List.isPrefixOf_iff_prefix.mpr (List.prefix_append l s)

/-- The core lemma: a delimited template of lawful convertors matches its own
rendering, and finds every parameter the rendering used. -/
theorem matchPieces_render {env : PathParams} :
    ∀ (ps : List Piece) (s : List Char), separatedPieces ps = true →
    (∀ n c, Piece.param n c ∈ ps → c.Lawful) → renderPieces env ps = some s →
    ∃ r, matchPieces ps s = some r ∧ r.map Prod.fst = ps.filterMap Piece.paramName? ∧
      ∀ p ∈ r, env.lookup p.1 = some p.2
  | [], s, _, _, h => by
    simp only [renderPieces, Option.some.injEq] at h; subst h
    exact ⟨[], by simp [matchPieces], by simp, by simp⟩
  | .lit l :: rest, s, hsep, hlaw, h => by
    simp only [renderPieces, Option.map_eq_some_iff] at h
    obtain ⟨s', hs', rfl⟩ := h
    obtain ⟨r, hr, hk, hl⟩ := matchPieces_render rest s' (by simpa [separatedPieces] using hsep)
      (fun n c hm => hlaw n c (List.mem_cons_of_mem _ hm)) hs'
    refine ⟨r, ?_, by simp only [List.filterMap_cons, Piece.paramName?]; exact hk, hl⟩
    simp [matchPieces, isPrefixOf_append, hr]
  | .param n c :: rest, s, hsep, hlaw, h => by
    simp only [renderPieces, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨v, hv, a, ha, b, hb, rfl⟩ := h
    have hc : c.Lawful := hlaw n c (by simp)
    simp only [separatedPieces, Bool.and_eq_true] at hsep
    obtain ⟨hnext, hsep⟩ := hsep
    obtain ⟨r, hr, hk, hl⟩ := matchPieces_render rest b hsep
      (fun n c hm => hlaw n c (List.mem_cons_of_mem _ hm)) hb
    refine ⟨(n, v) :: r, ?_, by simp [Piece.paramName?, hk], ?_⟩
    · simp only [matchPieces]
      apply findSome_splits_greedy
      · intro pq hpq hne
        have hcat := mem_splits hpq
        have hacc : c.accepts (a ++ pq.1) = false := by
          cases rest with
          | nil =>
            simp only [renderPieces, Option.some.injEq] at hb; subst hb
            simp [splits] at hpq; subst hpq; exact absurd rfl hne
          | cons q rest' =>
            cases q with
            | param _ _ => simp at hnext
            | lit l =>
              cases l with
              | nil => simp at hnext
              | cons ch l' =>
                simp only [Bool.not_eq_true'] at hnext
                simp only [renderPieces, Option.map_eq_some_iff] at hb
                obtain ⟨b', _, rfl⟩ := hb
                obtain ⟨p1, p2⟩ := pq
                cases p1 with
                | nil => exact absurd rfl hne
                | cons x xs =>
                  simp only [List.cons_append, List.cons.injEq] at hcat
                  rw [Bool.eq_false_iff]
                  intro hacc
                  have := hc.allowed_of_accepts _ hacc ch (by simp [hcat.1])
                  rw [hnext] at this; cases this
        simp [hacc]
      · simp [hc.accepts_render v a ha, hr, hc.convert_render v a ha]
    · intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact hv
      · exact hl p hp

/-- What a successful match returns: one entry per template parameter, in order. -/
theorem matchPieces_keys : ∀ (ps : List Piece) (s : List Char) (r : PathParams),
    matchPieces ps s = some r → r.map Prod.fst = ps.filterMap Piece.paramName?
  | [], s, r, h => by
    simp only [matchPieces] at h; split at h <;> simp_all
  | .lit l :: rest, s, r, h => by
    simp only [matchPieces] at h; split at h
    · simp only [List.filterMap_cons, Piece.paramName?]; exact matchPieces_keys rest _ r h
    · cases h
  | .param n c :: rest, s, r, h => by
    simp only [matchPieces, List.findSome?_eq_some_iff] at h
    obtain ⟨_, pq, _, _, hf, _⟩ := h
    split at hf
    · simp only [Option.map_eq_some_iff] at hf
      obtain ⟨r', hr', rfl⟩ := hf
      simp [Piece.paramName?, matchPieces_keys rest _ r' hr']
    · cases hf

/-- Every parameter a match finds renders again. -/
theorem matchPieces_renderable {env : PathParams} : ∀ (ps : List Piece) (s : List Char) (r : PathParams),
    (∀ n c, Piece.param n c ∈ ps → c.Lawful) → matchPieces ps s = some r →
    (∀ p ∈ r, env.lookup p.1 = some p.2) → ∃ s', renderPieces env ps = some s'
  | [], _, _, _, _, _ => ⟨[], rfl⟩
  | .lit l :: rest, s, r, hlaw, h, hl => by
    simp only [matchPieces] at h; split at h
    · obtain ⟨s', hs'⟩ := matchPieces_renderable rest _ r
        (fun n c hm => hlaw n c (List.mem_cons_of_mem _ hm)) h hl
      exact ⟨l ++ s', by simp [renderPieces, hs']⟩
    · cases h
  | .param n c :: rest, s, r, hlaw, h, hl => by
    simp only [matchPieces, List.findSome?_eq_some_iff] at h
    obtain ⟨_, pq, _, _, hf, _⟩ := h
    split at hf
    · rename_i hacc
      simp only [Option.map_eq_some_iff] at hf
      obtain ⟨r', hr', rfl⟩ := hf
      obtain ⟨s', hs'⟩ := matchPieces_renderable rest _ r'
        (fun n c hm => hlaw n c (List.mem_cons_of_mem _ hm)) hr'
        (fun p hp => hl p (List.mem_cons_of_mem _ hp))
      have hv := hl _ (List.mem_cons_self ..)
      have hsome := (hlaw n c (by simp)).render_convert _ hacc
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hsome
      exact ⟨a ++ s', by simp [renderPieces, hv, ha, hs']⟩
    · cases hf

/-! ## The two headline theorems -/

/-- **`url_path_for` then routing gives the parameters back.** For a
delimited template of lawful convertors, the path `urlFor` renders from
`ps` matches the template, with parameters equal to `ps` as a dict. -/
theorem Template.match_urlFor (t : Template) (hsep : t.Separated) (hlaw : t.Lawful)
    {ps : PathParams} {p : String} (h : t.urlFor ps = some p) :
    ∃ ps', t.match p = some ps' ∧ ps'.Equiv ps := by
  unfold Template.urlFor at h
  split at h
  · rename_i hacc
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨s, hs, rfl⟩ := h
    obtain ⟨r, hr, hk, hl⟩ := matchPieces_render t.pieces s hsep hlaw hs
    refine ⟨r, by simp [Template.match, String.toList_ofList, hr], ?_⟩
    intro k
    simp only [Template.acceptsParams, Bool.and_eq_true, List.all_eq_true] at hacc
    by_cases hk' : k ∈ r.map Prod.fst
    · obtain ⟨v, hv⟩ := lookup_some_of_mem hk'
      rw [hv, hl _ (lookup_mem hv)]
    · rw [lookup_none hk']
      symm
      cases hlk : ps.lookup k with
      | none => rfl
      | some v =>
        have := hacc.1 _ (lookup_mem hlk)
        simp only [List.contains_iff_mem] at this
        exact absurd (hk ▸ this) hk'
  · cases h

/-- **Routing then `url_path_for` gives the path back, up to normal form.**
The parameters a path matches render to a path (no `NoMatchFound`, no
assertion), and that path routes to exactly the same parameters. -/
theorem Template.urlFor_match (t : Template) (hsep : t.Separated) (hlaw : t.Lawful)
    {p : String} {ps : PathParams} (h : t.match p = some ps) :
    ∃ p', t.urlFor ps = some p' ∧ t.match p' = some ps := by
  have hk := matchPieces_keys _ _ _ h
  have hn : (ps.map Prod.fst).Nodup := hk ▸ t.h_nodup
  obtain ⟨s', hs'⟩ := matchPieces_renderable (env := ps) t.pieces _ ps hlaw h (lookup_self hn)
  have hacc : t.acceptsParams ps = true := by
    simp only [Template.acceptsParams, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem]
    refine ⟨fun q hq => ?_, fun n hn' => ?_⟩
    · unfold Template.paramNames; rw [← hk]; exact List.mem_map_of_mem hq
    · unfold Template.paramNames at hn'; rw [← hk] at hn'
      obtain ⟨v, hv⟩ := lookup_some_of_mem hn'; simp [hv]
  refine ⟨String.ofList s', by simp [Template.urlFor, hacc, hs'], ?_⟩
  obtain ⟨r, hr, hk', hl⟩ := matchPieces_render t.pieces s' hsep hlaw hs'
  simp only [Template.match, String.toList_ofList, hr, Option.some.injEq]
  exact eq_of_keys (hk'.trans hk.symm) hn hl

/-- **Canonical paths come back unchanged.** When every convertor of the
template is canonical (`str` and `path` are; `int` maps `007` to `7`), the
path rendered from a match is the path itself. -/
def Convertor.Canonical (c : Convertor) : Prop :=
  ∀ s, c.accepts s = true → c.render (c.convert s) = some s

theorem strConvertor_canonical : strConvertor.Canonical := by
  intro s h
  simp only [strConvertor, Bool.and_eq_true] at h
  simp only [strConvertor, String.toList_ofList]
  simp only [h.1, h.2, Bool.and_self, ↓reduceIte]

theorem pathConvertor_canonical : pathConvertor.Canonical := by
  intro s _; simp [pathConvertor, String.toList_ofList]

/-- The match-then-render direction for canonical convertors. -/
theorem renderPieces_of_match_canonical {env : PathParams} : ∀ (ps : List Piece) (s : List Char) (r : PathParams),
    (∀ n c, Piece.param n c ∈ ps → c.Canonical) → matchPieces ps s = some r →
    (∀ p ∈ r, env.lookup p.1 = some p.2) → renderPieces env ps = some s
  | [], s, r, _, h, _ => by
    simp only [matchPieces] at h; split at h
    · rename_i he; simp at he; subst he; rfl
    · cases h
  | .lit l :: rest, s, r, hc, h, hl => by
    simp only [matchPieces] at h; split at h
    · rename_i hp
      have := renderPieces_of_match_canonical rest _ r
        (fun n c hm => hc n c (List.mem_cons_of_mem _ hm)) h hl
      have hpre := List.isPrefixOf_iff_prefix.mp hp
      obtain ⟨u, rfl⟩ := hpre
      simp only [List.drop_left] at this
      simp [renderPieces, this]
    · cases h
  | .param n c :: rest, s, r, hc, h, hl => by
    simp only [matchPieces, List.findSome?_eq_some_iff] at h
    obtain ⟨_, pq, _, hpq, hf, _⟩ := h
    split at hf
    · rename_i hacc
      simp only [Option.map_eq_some_iff] at hf
      obtain ⟨r', hr', rfl⟩ := hf
      have hs := renderPieces_of_match_canonical rest _ r'
        (fun n c hm => hc n c (List.mem_cons_of_mem _ hm)) hr'
        (fun p hp => hl p (List.mem_cons_of_mem _ hp))
      have hv := hl _ (List.mem_cons_self ..)
      have hcat := mem_splits (s := s) (pq := pq) (by rw [hpq]; simp)
      have hr := hc n c (by simp) _ hacc
      simp only at hv
      simp [renderPieces, hv, hr, hs, hcat]
    · cases hf

theorem Template.urlFor_match_canonical (t : Template) (hc : ∀ n c, Piece.param n c ∈ t.pieces → c.Canonical)
    {p : String} {ps : PathParams} (h : t.match p = some ps) : (renderPieces ps t.pieces).map String.ofList = some p := by
  have hk := matchPieces_keys _ _ _ h
  have hn : (ps.map Prod.fst).Nodup := hk ▸ t.h_nodup
  rw [renderPieces_of_match_canonical t.pieces _ ps hc h (lookup_self hn)]
  simp [String.ofList_toList]

end LeanStarlette
