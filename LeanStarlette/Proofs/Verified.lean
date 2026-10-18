import LeanStarlette.Specifications.Starlette
import LeanStarlette.Proofs.Routing
import LeanStarlette.Proofs.Http
import LeanStarlette.Proofs.Background
import LeanStarlette.Proofs.Range
import LeanStarlette.Proofs.Files
import LeanStarlette.Proofs.Forms

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

theorem theVerifiedRouting : VerifiedRouting where
  routeFirstMatch := route_first_match
  partialIff405 := partial_iff_405
  allowUnion := mem_allowOf
  noMatch404 := no_match_404
  redirectSlashes := redirect_slashes_307
  headImpliesGet := route_head_implies_get
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

theorem theVerifiedHttp : VerifiedHttp where
  headersGetCI := headers_get_ci
  contentLengthEqBody := content_length_eq_body
  noBody204304 := no_body_204_304
  redirect307 := redirect_307
  jsonResponseBody := json_response_body

/-- Streaming, background tasks, files and static files (m6). -/
structure VerifiedFiles where
  backgroundRunOrder : Spec.BackgroundRunOrder
  backgroundRunOrderIO : Spec.BackgroundRunOrderIO
  rangeParsePrint : Spec.RangeParsePrint
  rangeWithin : Spec.RangeWithin
  etag304Iff : Spec.Etag304Iff
  servedPathInside : Spec.ServedPathInside

theorem theVerifiedFiles : VerifiedFiles where
  backgroundRunOrder := BackgroundTasks.background_run_order
  backgroundRunOrderIO := BackgroundTasks.background_run_order_io
  rangeParsePrint := range_parse_print
  rangeWithin := range_within
  etag304Iff := etag_304_iff
  servedPathInside := served_path_inside

/-- Forms (m4): `request.form()` over lean-multipart. -/
structure VerifiedForms where
  formParseAgrees : Spec.FormParseAgrees
  formLimitsEnforced : Spec.FormLimitsEnforced
  formError400 : Spec.FormError400

theorem theVerifiedForms : VerifiedForms where
  formParseAgrees := fun _ _ _ _ h => form_parse_agrees h
  formLimitsEnforced := fun _ _ _ _ h => form_limits_enforced h
  formError400 := form_error_400

end LeanStarlette
