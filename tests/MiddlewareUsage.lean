import LeanStarlette

/-!
# Middleware, spelled as upstream

An application with every middleware of m5, configured as a Starlette user
would: a realistic `allow_origin_regex` (parsed by `re!` at elaboration)
and a `TrustedHostMiddleware` host list (checked by `decide +kernel`).
Elaborating this module under `stack-tools/capped` (4G) peaks at the
import's footprint plus about 45 MB (CONTRIBUTING, "Elaboration cost").
-/

namespace MiddlewareUsage

open LeanStarlette

def homepage : Request → AppM Response := fun _ =>
  pure ((PlainTextResponse "hi").set_cookie "session_id" "abc" (httponly := true))

def app : Application := Starlette (routes := [Route "/" homepage]) (middleware := [
  Middleware TrustedHostMiddleware (allowed_hosts := ["example.org", "*.example.org", "api.example.com", "localhost",
    "127.0.0.1", "*.internal.example.net"]),
  Middleware HTTPSRedirectMiddleware,
  Middleware CORSMiddleware (allow_origins := ["https://example.org", "https://app.example.org"])
    (allow_origin_regex := re!"https://(?:[a-z0-9-]+\\.)*example\\.(?:com|org)(?::\\d{2,5})?")
    (allow_methods := ["*"]) (allow_headers := ["*"]) (allow_credentials := true),
  Middleware SessionMiddleware (secret_key := "a-long-random-secret-key"),
  Middleware BaseHTTPMiddleware (dispatch := fun req call_next => call_next req)])

end MiddlewareUsage
