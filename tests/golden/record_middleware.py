"""Record golden exchanges of Starlette 1.8.0's middleware, for
tests/Conformance.lean (`middlewareGoldenCases`).

Run from the workspace with the upstream-spec venv (not in CI):
  upstream-spec/.venv/bin/python -I lean-starlette/tests/golden/record_middleware.py \
    > lean-starlette/tests/golden/middleware-starlette-1.8.0.jsonl

Each line is one scenario from tests/middleware/test_{trusted_host,
https_redirect,cors,gzip,session}.py or tests/test_authentication.py: an
application (by name; the same applications are written in Lean in
tests/Conformance.lean, `mwApp`), TestClient options, and calls made in
order on one client. A call records status, headers, the decoded body and
the final URL. A call may first delete a client cookie (`delete_cookie`) or
start a new client carrying the session cookie of the previous response
(`carry_session`), as the upstream tests do.
"""
import base64
import binascii
import json
import re
import warnings

warnings.simplefilter("ignore")

from starlette.applications import Starlette
from starlette.authentication import AuthCredentials, AuthenticationBackend, AuthenticationError, SimpleUser, requires
from starlette.middleware import Middleware
from starlette.middleware.authentication import AuthenticationMiddleware
from starlette.middleware.cors import CORSMiddleware
from starlette.middleware.gzip import GZipMiddleware
from starlette.middleware.httpsredirect import HTTPSRedirectMiddleware
from starlette.middleware.sessions import SessionMiddleware
from starlette.middleware.trustedhost import TrustedHostMiddleware
from starlette.requests import Request
from starlette.responses import FileResponse, JSONResponse, PlainTextResponse, Response, StreamingResponse
from starlette.routing import Mount, Route
from starlette.testclient import TestClient


def text(s, **kw):
    return lambda request: PlainTextResponse(s, **kw)


def vary_app(request):
    response = PlainTextResponse("Homepage", headers={"Vary": "Accept-Encoding"})
    response.headers.append("Vary", "Accept-Language")
    return response


def stream(media_type=None, headers=None):
    def endpoint(request):
        async def gen():
            for _ in range(10):
                yield b"x" * 400
        return StreamingResponse(gen(), media_type=media_type, headers=headers)
    return endpoint


def raw(content_type, body=b"x" * 4000):
    def endpoint(request):
        return Response(body, headers={"content-type": content_type} if content_type else None)
    return endpoint


def cors(**kw):
    return Starlette(routes=[Route("/", text("Homepage"), methods=["GET", "POST", "PUT", "PATCH", "DELETE", "HEAD", "OPTIONS"])],
                     middleware=[Middleware(CORSMiddleware, **kw)])


def gz(endpoint, **kw):
    return Starlette(routes=[Route("/", endpoint)], middleware=[Middleware(GZipMiddleware, **kw)])


# sessions (tests/middleware/test_session.py)
def view_session(request):
    return JSONResponse({"session": request.session})


async def update_session(request):
    request.session.update(await request.json())
    return JSONResponse({"session": request.session})


async def inplace_update_session(request):
    session = request.session
    session |= await request.json()
    return JSONResponse({"session": request.session})


def popitem_session(request):
    request.session.popitem()
    return JSONResponse({"session": request.session})


def clear_session(request):
    request.session.clear()
    return JSONResponse({"session": request.session})


def no_session_access(request):
    return JSONResponse({"status": "ok"})


def sessions(**kw):
    return Starlette(routes=[
        Route("/view_session", view_session),
        Route("/update_session", update_session, methods=["POST"]),
        Route("/inplace_update_session", inplace_update_session, methods=["POST"]),
        Route("/popitem_session", popitem_session, methods=["POST"]),
        Route("/clear_session", clear_session, methods=["POST"]),
        Route("/no_session", no_session_access),
    ], middleware=[Middleware(SessionMiddleware, secret_key="example", **kw)])


# authentication (tests/test_authentication.py)
class BasicAuth(AuthenticationBackend):
    async def authenticate(self, request):
        if "Authorization" not in request.headers:
            return None
        auth = request.headers["Authorization"]
        try:
            scheme, credentials = auth.split()
            decoded = base64.b64decode(credentials).decode("ascii")
        except (ValueError, UnicodeDecodeError, binascii.Error):
            raise AuthenticationError("Invalid basic auth credentials")
        username, _, password = decoded.partition(":")
        return AuthCredentials(["authenticated"]), SimpleUser(username)


def homepage(request):
    return JSONResponse({"authenticated": request.user.is_authenticated, "user": request.user.display_name,
                         "identity": request.user.identity})


@requires("authenticated")
async def dashboard(request):
    return JSONResponse({"authenticated": request.user.is_authenticated, "user": request.user.display_name})


@requires("authenticated", redirect="homepage")
async def admin(request):
    return JSONResponse({"authenticated": request.user.is_authenticated, "user": request.user.display_name})


@requires(["authenticated", "admin"], status_code=401)
async def superuser(request):
    return JSONResponse({"user": request.user.display_name})


def on_error(conn, exc):
    return JSONResponse({"error": str(exc)}, status_code=401)


auth_routes = [Route("/", homepage), Route("/dashboard", dashboard), Route("/admin", admin),
               Route("/superuser", superuser)]


def second_app():
    inner = Starlette(routes=[Route("/update_session", update_session, methods=["POST"])],
                      middleware=[Middleware(SessionMiddleware, secret_key="example", path="/second_app")])
    return Starlette(routes=[Mount("/second_app", app=inner)])


def no_server_app():
    middleware = HTTPSRedirectMiddleware(PlainTextResponse("OK"))

    async def app(scope, receive, send):
        scope.pop("server", None)
        await middleware(scope, receive, send)
    return app


APPS = {
    "th": Starlette(routes=[Route("/", text("OK"))],
                    middleware=[Middleware(TrustedHostMiddleware, allowed_hosts=["testserver", "*.testserver"])]),
    "th6": Starlette(routes=[Route("/", text("OK"))],
                     middleware=[Middleware(TrustedHostMiddleware,
                                            allowed_hosts=["[::1]", "[v1.foo]", "api_service", "*.example.com"])]),
    "thwww": Starlette(routes=[Route("/", text("OK"))],
                       middleware=[Middleware(TrustedHostMiddleware, allowed_hosts=["www.example.com"])]),
    "https": Starlette(routes=[Route("/", text("OK"))], middleware=[Middleware(HTTPSRedirectMiddleware)]),
    "https_noserver": no_server_app(),
    "cors_all": cors(allow_origins=["*"], allow_headers=["*"], allow_methods=["*"], expose_headers=["X-Status"],
                     allow_credentials=True),
    "cors_all_nocred": cors(allow_origins=["*"], allow_headers=["*"], allow_methods=["*"], expose_headers=["X-Status"]),
    "cors_specific": cors(allow_origins=["https://example.org"], allow_headers=["X-Example", "Content-Type"]),
    "cors_disallowed": cors(allow_origins=["https://example.org"], allow_headers=["X-Example"]),
    "cors_wild_cred": cors(allow_origins=["*"], allow_methods=["POST"], allow_credentials=True),
    "cors_all_methods": cors(allow_origins=["*"], allow_methods=["*"]),
    "cors_regex": cors(allow_headers=["X-Example", "Content-Type"], allow_origin_regex="https://.*",
                       allow_credentials=True),
    "cors_regex_full": cors(allow_headers=["X-Example", "Content-Type"], allow_origin_regex=r"https://.*\.example.org"),
    "cors_vary_default": cors(allow_origins=["https://example.org"]),
    "cors_vary_nocred": Starlette(routes=[Route("/", vary_app)], middleware=[Middleware(CORSMiddleware, allow_origins=["*"])]),
    "cors_vary_cred": Starlette(routes=[Route("/", vary_app)],
                                middleware=[Middleware(CORSMiddleware, allow_origins=["*"], allow_credentials=True)]),
    "cors_vary_specific": Starlette(routes=[Route("/", lambda r: PlainTextResponse("Homepage", headers={"Vary": "Accept-Encoding"}))],
                                    middleware=[Middleware(CORSMiddleware, allow_origins=["https://example.org"])]),
    "cors_pna": cors(allow_origins=["*"], allow_methods=["*"], allow_private_network=True),
    "cors_no_pna": cors(allow_origins=["*"], allow_methods=["*"], allow_private_network=False),
    "cors_gzip": Starlette(routes=[Route("/", text("Homepage", headers={"Vary": "Accept-Language"}))],
                           middleware=[Middleware(GZipMiddleware, minimum_size=0),
                                       Middleware(CORSMiddleware, allow_origins=["https://allowed.example"])]),
    "gz_text": gz(text("x" * 4000)),
    "gz_small": gz(text("OK")),
    "gz_stream": gz(stream()),
    "gz_stream_encoded": gz(stream(headers={"Content-Encoding": "text"})),
    "gz_sse": gz(stream(media_type="text/event-stream")),
    "gz_svg": gz(raw("image/svg+xml")),
    "gz_png": gz(raw("image/png")),
    "gz_grpc_proto": gz(raw("application/grpc+proto")),
    "gz_zip_custom": gz(raw("application/zip"), exclude_content_types=("application/zip",)),
    "gz_sse_cleared": gz(raw("text/event-stream"), exclude_content_types=()),
    "gz_sse_normalized": gz(raw("Text/Event-Stream; charset=utf-8"), exclude_content_types=("text/event-stream",)),
    "gz_zip_normalized": gz(raw("application/zip"), exclude_content_types=("Application/ZIP; charset=utf-8",)),
    "gz_image_wildcard": gz(raw("image/png"), exclude_content_types=("image/*",)),
    "gz_big": gz(text("x" * (128 * 1024))),
    "sessions": sessions(),
    "sessions_secure": sessions(https_only=True),
    "sessions_partitioned": sessions(https_only=True, same_site="none", partitioned=True),
    "sessions_expired": sessions(max_age=-1),
    "sessions_no_max_age": sessions(max_age=None),
    "sessions_zero": sessions(max_age=0),
    "sessions_domain": sessions(domain=".example.com"),
    "sessions_subpath": second_app(),
    "auth": Starlette(routes=auth_routes, middleware=[Middleware(AuthenticationMiddleware, backend=BasicAuth())]),
    "auth_on_error": Starlette(routes=auth_routes,
                               middleware=[Middleware(AuthenticationMiddleware, backend=BasicAuth(), on_error=on_error)]),
}


def call(method, url, headers=None, json_body=None, follow=True, **extra):
    c = {"method": method, "url": url, "headers": headers or {}, "follow": follow}
    if json_body is not None:
        c["json"] = json_body
    c.update(extra)
    return c


def get(url="/", headers=None, **kw):
    return call("GET", url, headers, **kw)


def options(headers, url="/"):
    return call("OPTIONS", url, headers)


def basic(user="tomchristie", password="example"):
    return {"Authorization": "Basic " + base64.b64encode(f"{user}:{password}".encode()).decode()}


PRE = {"Origin": "https://example.org", "Access-Control-Request-Method": "GET", "Access-Control-Request-Headers": "X-Example"}
PNA = {"Origin": "https://example.org", "Access-Control-Request-Method": "GET"}
GZ = {"accept-encoding": "gzip"}
ID = {"accept-encoding": "identity"}
T = "tests/middleware/"

SCENARIOS = [
    (T + "test_trusted_host.py::test_trusted_host_middleware", "th", {}, [get()]),
    (T + "test_trusted_host.py::test_trusted_host_middleware (subdomain)", "th", {"base_url": "http://subdomain.testserver"}, [get()]),
    (T + "test_trusted_host.py::test_trusted_host_middleware (invalid)", "th", {"base_url": "http://invalidhost"}, [get()]),
    (T + "test_trusted_host.py::test_trusted_host_middleware_ipv6", "th6", {},
     [get(headers={"host": h}) for h in ["[::1]", "[::1]:8000", "[v1.foo]", "[:::]", "[::ffff:999.999.999.999]",
                                         "[2001:db8::1]", "[::1", "[::1]evil.example.com", "[::1]@attacker", "[::1].",
                                         "[::1]:evil", "[::1]:", "api_service", "api_service:000080", "api_service:65535",
                                         "api_service:65536", "api_service:100000", "api_service:8000", "api_service/evil",
                                         "api_service?evil", "api_service#evil", "api_service@attacker", "api service"]]),
    (T + "test_trusted_host.py::test_www_redirect", "thwww", {"base_url": "https://example.com"}, [get()]),
    (T + "test_https_redirect.py::test_https_redirect_middleware (https)", "https", {"base_url": "https://testserver"}, [get()]),
    (T + "test_https_redirect.py::test_https_redirect_middleware", "https", {}, [
        get(follow=False), get(headers={"host": "testserver:000080"}, follow=False),
        get(headers={"host": "testserver:65536"}, follow=False), get(headers={"host": "[:::]"}, follow=False)]),
    (T + "test_https_redirect.py::test_https_redirect_middleware (:80)", "https", {"base_url": "http://testserver:80"}, [get(follow=False)]),
    (T + "test_https_redirect.py::test_https_redirect_middleware (:443)", "https", {"base_url": "http://testserver:443"}, [get(follow=False)]),
    (T + "test_https_redirect.py::test_https_redirect_middleware (:123)", "https", {"base_url": "http://testserver:123"}, [get(follow=False)]),
    (T + "test_https_redirect.py::test_https_redirect_middleware ([::1])", "https", {"base_url": "http://[::1]"},
     [get(headers={"host": "[:::]"}, follow=False)]),
    (T + "test_https_redirect.py::test_https_redirect_middleware_without_server", "https_noserver", {},
     [get(headers={"host": "testserver:65536"}, follow=False), get(headers={"host": "[:::]"}, follow=False)]),
    (T + "test_cors.py::test_cors_allow_all", "cors_all", {}, [
        options(PRE), get(headers={"Origin": "https://example.org"}),
        get(headers={"Origin": "https://example.org", "Cookie": "star_cookie=sugar"}), get()]),
    (T + "test_cors.py::test_cors_allow_all_except_credentials", "cors_all_nocred", {}, [
        options(PRE), options({k: v for k, v in PRE.items() if k != "Origin"}),
        get(headers={"Origin": "https://example.org"}), get()]),
    (T + "test_cors.py::test_cors_allow_specific_origin", "cors_specific", {}, [
        options({**PRE, "Access-Control-Request-Headers": "X-Example, Content-Type"}),
        get(headers={"Origin": "https://example.org"}), get()]),
    (T + "test_cors.py::test_cors_disallowed_preflight", "cors_disallowed", {}, [
        options({"Origin": "https://another.org", "Access-Control-Request-Method": "POST",
                 "Access-Control-Request-Headers": "X-Nope"}),
        options({"Origin": "https://example.org", "Access-Control-Request-Method": "GET",
                 "Access-Control-Request-Headers": "X-Nope-1, X-Nope-2"})]),
    (T + "test_cors.py::test_preflight_allows_request_origin_if_origins_wildcard_and_credentials_allowed", "cors_wild_cred", {},
     [options({"Origin": "https://example.org", "Access-Control-Request-Method": "POST"})]),
    (T + "test_cors.py::test_cors_preflight_allow_all_methods", "cors_all_methods", {},
     [options({"Origin": "https://example.org", "Access-Control-Request-Method": m})
      for m in ("DELETE", "GET", "HEAD", "OPTIONS", "PATCH", "POST", "PUT", "QUERY")]),
    (T + "test_cors.py::test_cors_preflight_rejects_custom_method_with_wildcard", "cors_all_methods", {},
     [options({"Origin": "https://example.org", "Access-Control-Request-Method": "CUSTOM"})]),
    (T + "test_cors.py::test_cors_allow_all_methods", "cors_all_methods", {},
     [call(m, "/", {"Origin": "https://example.org"}, json_body={}) for m in ("PATCH", "POST", "PUT")] +
     [call(m, "/", {"Origin": "https://example.org"}) for m in ("DELETE", "GET", "HEAD", "OPTIONS")] +
     [options({"Access-Control-Request-Method": "GET"})]),
    (T + "test_cors.py::test_cors_allow_origin_regex", "cors_regex", {}, [
        get(headers={"Origin": "https://example.org"}),
        get(headers={"Origin": "https://example.org", "Cookie": "star_cookie=sugar"}),
        get(headers={"Origin": "http://example.org"}),
        options({"Origin": "https://another.com", "Access-Control-Request-Method": "GET",
                 "Access-Control-Request-Headers": "X-Example, content-type"}),
        options({"Origin": "http://another.com", "Access-Control-Request-Method": "GET",
                 "Access-Control-Request-Headers": "X-Example"})]),
    (T + "test_cors.py::test_cors_allow_origin_regex_fullmatch", "cors_regex_full", {}, [
        get(headers={"Origin": "https://subdomain.example.org"}),
        get(headers={"Origin": "https://subdomain.example.org.hacker.com"})]),
    (T + "test_cors.py::test_cors_vary_header_defaults_to_origin", "cors_vary_default", {},
     [get(headers={"Origin": "https://example.org"})]),
    (T + "test_cors.py::test_cors_vary_header_is_set_for_non_credentialed_request", "cors_vary_nocred", {},
     [get(headers={"Origin": "https://someplace.org"})]),
    (T + "test_cors.py::test_cors_vary_header_is_properly_set_for_credentialed_request", "cors_vary_cred", {},
     [get(headers={"Origin": "https://someplace.org"})]),
    (T + "test_cors.py::test_cors_vary_header_is_properly_set_when_allow_origins_is_not_wildcard", "cors_vary_specific", {},
     [get(headers={"Origin": "https://example.org"})]),
    (T + "test_cors.py::test_cors_allowed_origin_does_not_leak_between_requests", "cors_vary_default", {}, [
        get(headers={"Origin": "https://example.org"}), get(headers={"Origin": "https://other.org"}),
        get(headers={"Origin": "https://example.org"})]),
    (T + "test_cors.py::test_cors_private_network_access_allowed", "cors_pna", {}, [
        options({**PNA, "Access-Control-Request-Private-Network": "true"}), options(PNA),
        get(headers={**PNA, "Access-Control-Request-Private-Network": "true"})]),
    (T + "test_cors.py::test_cors_private_network_access_disallowed", "cors_no_pna", {}, [
        options(PNA), options({**PNA, "Access-Control-Request-Private-Network": "true"})]),
    (T + "test_cors.py::test_cors_vary_origin_with_gzip", "cors_gzip", {},
     [get(headers={"Origin": "https://allowed.example", "Accept-Encoding": "gzip"})]),
    (T + "test_gzip.py::test_gzip_responses", "gz_text", {}, [get(headers=GZ)]),
    (T + "test_gzip.py::test_gzip_not_in_accept_encoding", "gz_text", {}, [get(headers=ID)]),
    (T + "test_gzip.py::test_gzip_ignored_for_small_responses", "gz_small", {}, [get(headers=GZ)]),
    (T + "test_gzip.py::test_gzip_streaming_response", "gz_stream", {}, [get(headers=GZ)]),
    (T + "test_gzip.py::test_gzip_compression_in_thread", "gz_big", {}, [get(headers=GZ)]),
    (T + "test_gzip.py::test_gzip_streaming_response_identity", "gz_stream", {}, [get(headers=ID)]),
    (T + "test_gzip.py::test_gzip_ignored_for_responses_with_encoding_set", "gz_stream_encoded", {},
     [get(headers={"accept-encoding": "gzip, text"})]),
    (T + "test_gzip.py::test_gzip_ignored_on_server_sent_events", "gz_sse", {}, [get(headers=GZ)]),
    (T + "test_gzip.py::test_gzip_default_exclude_content_types (image/png)", "gz_png", {}, [get(headers=GZ)]),
    (T + "test_gzip.py::test_gzip_default_exclude_content_types (application/grpc+proto)", "gz_grpc_proto", {}, [get(headers=GZ)]),
    (T + "test_gzip.py::test_gzip_compresses_svg_by_default", "gz_svg", {}, [get(headers=GZ)]),
    (T + "test_gzip.py::test_gzip_custom_exclude_content_types", "gz_zip_custom", {}, [get(headers=GZ)]),
    (T + "test_gzip.py::test_gzip_cleared_exclude_content_types", "gz_sse_cleared", {}, [get(headers=GZ)]),
    (T + "test_gzip.py::test_gzip_exclude_content_types_for_identity_client", "gz_zip_custom", {}, [get(headers=ID)]),
    (T + "test_gzip.py::test_gzip_exclude_content_types_matching (header-is-normalized)", "gz_sse_normalized", {}, [get(headers=GZ)]),
    (T + "test_gzip.py::test_gzip_exclude_content_types_matching (configured-value-is-normalized)", "gz_zip_normalized", {},
     [get(headers=GZ)]),
    (T + "test_gzip.py::test_gzip_exclude_content_types_matching (wildcard)", "gz_image_wildcard", {}, [get(headers=GZ)]),
    (T + "test_session.py::test_session", "sessions", {}, [
        get("/view_session"), call("POST", "/update_session", json_body={"some": "data"}), get("/view_session"),
        call("POST", "/clear_session"), get("/view_session")]),
    (T + "test_session.py::test_partitioned_session", "sessions_partitioned", {"base_url": "https://testserver"}, [
        call("POST", "/update_session", json_body={"some": "data"}), call("POST", "/clear_session")]),
    (T + "test_session.py::test_session_expires", "sessions_expired", {}, [
        call("POST", "/update_session", json_body={"some": "data"}), get("/view_session", carry_session=True)]),
    (T + "test_session.py::test_secure_session (http)", "sessions_secure", {"base_url": "http://testserver"}, [
        get("/view_session"), call("POST", "/update_session", json_body={"some": "data"}), get("/view_session")]),
    (T + "test_session.py::test_secure_session (https)", "sessions_secure", {"base_url": "https://testserver"}, [
        get("/view_session"), call("POST", "/update_session", json_body={"some": "data"}), get("/view_session"),
        call("POST", "/clear_session"), get("/view_session")]),
    (T + "test_session.py::test_session_cookie_subpath", "sessions_subpath", {"base_url": "http://testserver/second_app"}, [
        call("POST", "/update_session", json_body={"some": "data"})]),
    (T + "test_session.py::test_invalid_session_cookie", "sessions", {"cookies": {"session": "invalid"}}, [get("/view_session")]),
    (T + "test_session.py::test_session_cookie", "sessions_no_max_age", {}, [
        call("POST", "/update_session", json_body={"some": "data"}), get("/view_session", delete_cookie="session")]),
    (T + "test_session.py::test_session_zero_max_age", "sessions_zero", {}, [
        call("POST", "/update_session", json_body={"some": "data"})]),
    (T + "test_session.py::test_domain_cookie", "sessions_domain", {}, [
        call("POST", "/update_session", json_body={"some": "data"}), get("/view_session", delete_cookie="session")]),
    (T + "test_session.py::test_set_cookie_only_on_modification", "sessions", {}, [
        call("POST", "/update_session", json_body={"some": "data"}), get("/view_session")]),
    (T + "test_session.py::test_vary_cookie_on_access", "sessions", {}, [
        call("POST", "/update_session", json_body={"some": "data"}), get("/view_session"), get("/no_session")]),
    (T + "test_session.py::test_session_persists_mutations (inplace_update)", "sessions", {}, [
        call("POST", "/update_session", json_body={"a": "1", "b": "2"}),
        call("POST", "/inplace_update_session", json_body={"c": "3"}), get("/view_session")]),
    (T + "test_session.py::test_session_persists_mutations (popitem)", "sessions", {}, [
        call("POST", "/update_session", json_body={"a": "1", "b": "2"}), call("POST", "/popitem_session"),
        get("/view_session")]),
    ("tests/test_authentication.py::test_user_interface", "auth", {}, [get(), get(headers=basic())]),
    ("tests/test_authentication.py::test_authentication_required", "auth", {}, [
        get("/dashboard"), get("/dashboard", headers=basic()), get("/dashboard", headers={"Authorization": "basic foobar"})]),
    ("tests/test_authentication.py::test_authentication_redirect", "auth", {}, [
        get("/admin", follow=False), get("/admin"), get("/admin", headers=basic())]),
    ("tests/test_authentication.py (requires: two scopes, status_code=401)", "auth", {}, [
        get("/superuser"), get("/superuser", headers=basic())]),
    ("tests/test_authentication.py::test_custom_on_error", "auth_on_error", {}, [
        get("/", headers=basic()), get("/dashboard", headers={"Authorization": "basic foobar"})]),
]


def result(r):
    return {"status": r.status_code, "headers": [[k.decode("latin-1"), v.decode("latin-1")] for k, v in r.headers.raw],
            "text": r.content.decode("latin-1"), "url": str(r.url)}


for name, app_name, opts, calls in SCENARIOS:
    app = APPS[app_name]
    client = TestClient(app, raise_server_exceptions=False, **opts)
    results = []
    prev = None
    for c in calls:
        if c.get("delete_cookie"):
            client.cookies.delete(c["delete_cookie"])
        if c.get("carry_session"):
            m = re.search(r"session=([^;]*);", prev.headers["set-cookie"])
            client = TestClient(app, raise_server_exceptions=False, cookies={"session": m[1]}, **opts)
        kw = {"headers": c["headers"], "follow_redirects": c["follow"]}
        if "json" in c:
            kw["json"] = c["json"]
        r = client.request(c["method"], c["url"], **kw)
        results.append(result(r))
        prev = r
    print(json.dumps({"name": name, "app": app_name, "client": opts, "calls": calls, "results": results}))
