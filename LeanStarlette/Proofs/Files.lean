import LeanStarlette.RepoImpl.Files

/-!
# Proofs: conditional requests for static files

`StaticFiles` answers `304 Not Modified` exactly when the request's
validators match the file: an `If-None-Match` naming the file's ETag (or
`*`), or, without one, an `If-Modified-Since` no earlier than the file's
modification time.
-/

namespace LeanStarlette

theorem fileResponse_status (path : String) (st : Option (Nat × Int)) :
    (FileResponse path (stat_result := st)).status_code = 200 := rfl

theorem notModifiedResponse_status (h : Headers) : (notModifiedResponse h).status_code = 304 := rfl

/-- A static file response is `304` exactly when the validators match. -/
theorem static_304_iff (path : String) (size : Nat) (mtimeNs : Int) (req : Headers) :
    (staticFileResponse path size mtimeNs req).status_code = 304 ↔
      isNotModified (fileETag size mtimeNs) (formatHttpDate (mtimeNs / 1000000000)) req = true := by
  unfold staticFileResponse
  split
  · simp_all [notModifiedResponse_status]
  · rename_i hn
    simp only [hn, Bool.false_eq_true, iff_false]
    show (FileResponse path (stat_result := some (size, mtimeNs))).status_code ≠ 304
    rw [fileResponse_status]; decide

/-- **`etag_304_iff`**: with a non-empty `If-None-Match`, a static file is
`304` exactly when the header is `*` or lists the file's ETag (weak or
strong); `If-Modified-Since` is then ignored, as RFC 9110 13.2.2 says. -/
theorem etag_304_iff (path : String) (size : Nat) (mtimeNs : Int) (req : Headers) (inm : String)
    (h : req.get? "if-none-match" = some inm) (hne : inm ≠ "") :
    (staticFileResponse path size mtimeNs req).status_code = 304 ↔
      (String.ofList (stripWs inm.toList) = "*" ∨ fileETag size mtimeNs ∈ ifNoneMatchTags inm) := by
  rw [static_304_iff]
  unfold isNotModified
  have he : inm.isEmpty = false := by simpa using hne
  simp [h, he]

/-- Without `If-None-Match`, a static file is `304` exactly when
`If-Modified-Since` parses and is no earlier than the file's
`Last-Modified`. -/
theorem date_304_iff (path : String) (size : Nat) (mtimeNs : Int) (req : Headers)
    (h : req.get? "if-none-match" = none) :
    (staticFileResponse path size mtimeNs req).status_code = 304 ↔
      ∃ ims lm, (req.get? "if-modified-since").bind parseHttpDate = some ims ∧
        parseHttpDate (formatHttpDate (mtimeNs / 1000000000)) = some lm ∧ ims.ge lm = true := by
  rw [static_304_iff]
  unfold isNotModified isNotModified.byDate
  simp only [h]
  split
  · rename_i ims lm h1 h2; simp [h1, h2]
  · rename_i hno
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro ims lm h1 h2 _
    exact hno ims lm h1 h2

/-! ## A served path stays inside the static directory -/

theorem staticSegments_go_normal : ∀ (l acc r : List String), (∀ s ∈ acc, isNormalName s = true) →
    staticSegments.go acc l = some r → ∀ s ∈ r, isNormalName s = true
  | [], acc, r, hacc, h => by
    simp only [staticSegments.go, Option.some.injEq] at h
    subst h; simpa using hacc
  | x :: rest, acc, r, hacc, h => by
    unfold staticSegments.go at h
    split at h
    · exact staticSegments_go_normal rest acc r hacc h
    · split at h
      · split at h
        · cases h
        · rename_i _ hd tl
          exact staticSegments_go_normal rest tl r (fun s hs => hacc s (by simp [hs])) h
      · split at h
        · rename_i hn
          exact staticSegments_go_normal rest (x :: acc) r
            (fun s hs => by simp only [List.mem_cons] at hs; rcases hs with rfl | hs; exact hn; exact hacc s hs) h
        · cases h

/-- Every segment of a resolved static path names a directory entry: not
empty, not `.` or `..`, with no `/`, `\` or NUL. -/
theorem staticSegments_normal (p : String) (segs : List String) (h : staticSegments p = some segs) :
    ∀ s ∈ segs, isNormalName s = true :=
  staticSegments_go_normal _ [] segs (by simp) h

theorem joinUnder_eq (dir : String) (segs : List String) :
    joinUnder dir segs = dir ++ String.join (segs.map ("/" ++ ·)) := by
  unfold joinUnder
  induction segs generalizing dir with
  | nil => simp
  | cons s segs ih =>
    simp only [List.foldl_cons, List.map_cons, String.join_cons]
    rw [ih]; simp [String.append_assoc]

/-- **A served path is inside the static directory**: the path `StaticFiles`
opens for a request is the directory followed by `/name` components, each a
plain entry name, so no component leaves the directory: no `/`, `.`, `..` or
NUL, and on Windows no `\` (on POSIX a backslash is an ordinary file-name
character, as upstream serves it). Symbolic links are checked at run time
with `realPath`, unless `follow_symlink`. -/
theorem served_path_inside (dir p : String) (segs : List String) (h : staticSegments p = some segs) :
    joinUnder dir segs = dir ++ String.join (segs.map ("/" ++ ·)) ∧
      ∀ s ∈ segs, s.isEmpty = false ∧ s ≠ "." ∧ s ≠ ".." ∧
        s.contains '/' = false ∧ (System.Platform.isWindows && s.contains '\\') = false ∧
        s.contains '\x00' = false := by
  refine ⟨joinUnder_eq dir segs, fun s hs => ?_⟩
  have hn := staticSegments_normal p segs h s hs
  simp only [isNormalName, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hn
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hn
  exact ⟨h1, h2, h3, h4, h5, h6⟩

end LeanStarlette
