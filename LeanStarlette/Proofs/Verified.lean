import LeanStarlette.Specifications.Starlette
import LeanStarlette.Proofs.Routing
import LeanStarlette.Proofs.Http

/-!
# The harness: one `Verified<Layer>` structure per layer

Each `Verified<Layer>` bundles a proof term for every headline property of
`Specifications/Starlette.lean` that layer claims. A property with no proof
is a compile error the moment it needs a field here: a `Verified<Layer>`
value cannot be built without every proof in hand. Properties that are
tested rather than proved have no slot; they are listed in
`CONTRIBUTING.md` and `docs/traceability.toml`.

The template laws themselves (convertor `accepts_render`/`parse_render`,
`match_urlFor`, `urlFor_match`, first-match dispatch) are `Keel.Route`'s and
are checked in lean-keel's own harness; the slots here are their Starlette
instances.
-/

namespace LeanStarlette

/-- Routing: `Route`, `Mount`, `Router`. -/
structure VerifiedRouting where
  routeFirstMatch : Spec.RouteFirstMatch
  partialIff405 : Spec.PartialIff405
  allowUnion : Spec.AllowUnion
  noMatch404 : Spec.NoMatch404
  redirectSlashes : Spec.RedirectSlashes
  headImpliesGet : Spec.HeadImpliesGet
  compileMatchUrlPathFor : Spec.CompileMatchUrlPathFor
  urlPathForMatch : Spec.UrlPathForMatch

def theVerifiedRouting : VerifiedRouting where
  routeFirstMatch := route_first_match
  partialIff405 := partial_iff_405
  allowUnion := mem_allowOf
  noMatch404 := no_match_404
  redirectSlashes := redirect_slashes_307
  headImpliesGet := head_implies_get
  compileMatchUrlPathFor := fun p e ms n _ hc hs ha v hv req hr hm hp =>
    compile_match_url_path_for p e ms n hc hs ha v hv req hr hm hp
  urlPathForMatch := fun t _ _ h hc => urlPathFor_match t h hc

/-- Headers and responses. -/
structure VerifiedHttp where
  headersGetCI : Spec.HeadersGetCI
  contentLengthEqBody : Spec.ContentLengthEqBody
  noBody204304 : Spec.NoBody204304
  redirect307 : Spec.Redirect307
  jsonResponseBody : Spec.JsonResponseBody

def theVerifiedHttp : VerifiedHttp where
  headersGetCI := headers_get_ci
  contentLengthEqBody := content_length_eq_body
  noBody204304 := no_body_204_304
  redirect307 := redirect_307
  jsonResponseBody := json_response_body

end LeanStarlette
