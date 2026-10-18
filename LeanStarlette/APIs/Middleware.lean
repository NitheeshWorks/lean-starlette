import Lean
import LeanStarlette.RepoImpl.Middleware
import LeanStarlette.RepoImpl.Sessions

/-!
# APIs: middleware

The spelling is upstream's:

```
Starlette (routes := routes) (middleware := [
  Middleware CORSMiddleware (allow_origins := ["https://example.org"]) (allow_origin_regex := re!"https://.*\.example\.org"),
  Middleware TrustedHostMiddleware (allowed_hosts := ["example.org", "*.example.org"])])
```

`Middleware f args…` is `f args…` (a `Middleware` is an `App → App`, so the
class and its options are the function and its arguments). `re!"…"` parses
a Python regular expression when the file is elaborated: an invalid or
unsupported pattern is a compile error, where upstream's `re.compile`
raises when the middleware is built.
-/

namespace LeanStarlette

open Lean Elab Term Keel

deriving instance ToExpr for Regex.Assertion
deriving instance ToExpr for PyRe.Atom
deriving instance ToExpr for Regex.Cls
deriving instance ToExpr for Regex

/-- **`re!"pattern"`**: a Python regular expression, parsed now. -/
elab "re!" s:str : term => do
  let src := s.getString
  match PyRe.parse src with
  | .ok r => return mkApp2 (mkConst ``PyRe.Pattern.mk) (toExpr src) (toExpr r)
  | .error e => throwErrorAt s "re.error: {e}"

/-- `Middleware(cls, **options)`: the middleware function applied to its
options. -/
macro_rules
  | `(Middleware $f:ident $args*) => `($f $args*)

end LeanStarlette
