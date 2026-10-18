import LeanStarlette.APIs
import LeanStarlette.Proofs

/-!
# LeanStarlette

A clean-room port of Starlette to Lean 4: routing, requests, responses and middleware as pure functions with proved matching, header and body invariants; one transport module over Lean core's Std.Http.

Layering, bottom to top (each layer imports only the ones below it):

* `DataTypes/`      structures and inductives; invariants are fields
* `RepoImpl/`       the executable definitions; total, structural recursion
* `Specifications/` the properties, stated in `Prop`
* `Proofs/`         the theorems; `Proofs/Verified.lean` bundles them
* `APIs/`           what users call; returns refinements `{r // Post r}`
-/
