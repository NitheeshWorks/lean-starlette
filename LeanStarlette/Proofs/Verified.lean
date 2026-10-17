import LeanStarlette.Proofs.Basic

/-!
# The harness: one `Verified<Layer>` structure per layer

Each `Verified<Layer>` bundles a layer's implementation with a proof term for
every `Specifications/<Layer>.lean` property it claims. A specification with
no proof is a compile error the moment it needs a field here: you cannot
construct a `Verified<Layer>` value without every proof in hand. If a stated
specification turns out false, its slot's type flips to a refutation rather
than being dropped, so this file stays an honest map of what is verified.
-/

namespace LeanStarlette

end LeanStarlette
