import LeanStarlette.RepoImpl.GZip

/-!
# Proofs: `GZipMiddleware`

`gzip_minimum_size`: a response whose body is in memory and shorter than
`minimum_size` comes back exactly as it was, whether or not the client
accepts gzip, for every exclusion list and method.
-/

namespace LeanStarlette

theorem gzipWhole_small (minimum_size : Nat) (gzip : Bool) (r : Response) (hb : bodyAllowed r.status_code = true)
    (h : r.body.size < minimum_size) : gzipWhole minimum_size gzip r hb = r := by
  simp [gzipWhole, h]

theorem gzip_minimum_size (minimum_size : Nat) (exclude : List String) (gzip headOnly : Bool) (r : Response)
    (hs : r.stream = none) (h : r.body.size < minimum_size) :
    gzipResponse minimum_size exclude gzip headOnly r = pure r := by
  unfold gzipResponse
  by_cases hp : gzipPassThrough exclude r = true
  · simp [hp]
  · simp only [hp, Bool.false_eq_true, ite_false]
    by_cases hb : bodyAllowed r.status_code = true
    · simp [hb, hs, gzipWhole_small minimum_size gzip r hb h]
    · simp [hb]

end LeanStarlette
