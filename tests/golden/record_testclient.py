"""Record golden exchanges of Starlette 1.8.0's TestClient, for
tests/Conformance.lean (`testClientGoldenCases`).

Run from the workspace with the upstream-spec venv (not in CI):
  upstream-spec/.venv/bin/python -I lean-starlette/tests/golden/record_testclient.py \
    > lean-starlette/tests/golden/testclient-starlette-1.8.0.jsonl

Each line is one TestClient (its constructor options) and the calls made on
it in order. A call records what the client returned: status, headers, body,
final URL, redirect history and the client's cookie jar after the call, or
the exception it raised. The apps are tests/test_testclient.py's, plus
`echo`, which answers with what the application saw of the request (the
scope Starlette's transport built), so the scope is compared field by field.
The same apps are written in Lean in tests/Conformance.lean.
"""
import json
import warnings

warnings.simplefilter("ignore")

from starlette.applications import Starlette
from starlette.requests import Request
from starlette.responses import JSONResponse, PlainTextResponse, RedirectResponse, Response
from starlette.routing import Route
from starlette.testclient import TestClient


async def echo(request: Request) -> JSONResponse:
    body = await request.body()
    return JSONResponse({
        "method": request.method,
        "url": str(request.url),
        "path": request.scope["path"],
        "root_path": request.scope["root_path"],
        "query_string": request.scope["query_string"].decode("latin-1"),
        "headers": [[k.decode("latin-1"), v.decode("latin-1")] for k, v in request.scope["headers"]],
        "client": list(request.scope["client"]),
        "server": list(request.scope["server"]),
        "body": body.decode("latin-1"),
    })


def redirect(request: Request) -> Response:
    code = int(request.query_params.get("code", "307"))
    return RedirectResponse(request.query_params.get("to", "/echo"), status_code=code)


def set_cookie(request: Request) -> Response:
    response = PlainTextResponse("Hello, world!")
    domain = request.query_params.get("domain")
    response.set_cookie(request.query_params.get("name", "mycookie"),
                        request.query_params.get("value", "myvalue"), path="/", domain=domain)
    return response


def boom(request: Request) -> Response:
    raise RuntimeError("boom")


def mock_service_endpoint(request: Request) -> JSONResponse:
    return JSONResponse({"mock": "example"})


mock_service = Starlette(routes=[Route("/", endpoint=mock_service_endpoint)])


def in_endpoint(request: Request) -> JSONResponse:
    client = TestClient(mock_service)
    response = client.get("/")
    return JSONResponse(response.json())


def query_param(request: Request) -> Response:
    return Response(request.query_params["param"])


def url_path(request: Request) -> Response:
    return Response(request.url.path)


def dup_headers(request: Request) -> JSONResponse:
    return JSONResponse({"x-token": request.headers.getlist("x-token")})


METHODS = ["GET", "HEAD", "POST", "PUT", "PATCH", "DELETE", "OPTIONS"]

app = Starlette(routes=[
    Route("/echo", echo, methods=METHODS),
    Route("/echo/{rest:path}", echo, methods=METHODS),
    Route("/api/v1/echo", echo, methods=METHODS),
    Route("/redirect", redirect, methods=METHODS),
    Route("/cookie", set_cookie),
    Route("/boom", boom),
    Route("/in-endpoint", in_endpoint),
    Route("/query", query_param),
    Route("/api/v1/bar", url_path),
    Route("/dup", dup_headers),
])


def run_call(client: TestClient, call: dict) -> dict:
    kw = {}
    for k in ("params", "headers", "content", "json", "data", "follow_redirects", "cookies"):
        if k in call:
            v = call[k]
            kw[k] = [tuple(x) for x in v] if k == "headers" else v
    try:
        r = client.request(call["method"], call["url"], **kw)
    except Exception as e:  # recorded, compared by class and message
        return {"error": f"{type(e).__name__}: {e}"}
    return {
        "status": r.status_code,
        "headers": [list(p) for p in r.headers.multi_items()],
        "body": r.content.decode("latin-1"),
        "url": str(r.url),
        "history": [h.status_code for h in r.history],
        "jar": sorted([c.name, c.value, c.domain] for c in client.cookies.jar),
    }


G, P = "GET", "POST"
CASES = [
    # tests/test_testclient.py
    ("test_use_testclient_in_endpoint", {}, [{"method": G, "url": "/in-endpoint"}]),
    ("test_testclient_headers_behavior: default", {}, [{"method": G, "url": "/echo"}]),
    ("test_testclient_headers_behavior: user-agent", {"headers": {"user-agent": "non-default-agent"}},
     [{"method": G, "url": "/echo"}]),
    ("test_testclient_headers_behavior: Authentication", {"headers": {"Authentication": "Bearer 123"}},
     [{"method": G, "url": "/echo"}]),
    ("test_client", {}, [{"method": G, "url": "/echo"}]),
    ("test_client_custom_client", {"client": ["192.168.0.1", 3000]}, [{"method": G, "url": "/echo"}]),
    *[(f"test_query_params[{p}]", {}, [{"method": G, "url": "/query", "params": {"param": p}}])
      for p in ("2020-07-14T00:00:00+00:00", "España", "voilà")],
    *[(f"test_domain_restricted_cookies[{d}]", {}, [{"method": G, "url": "/cookie", "params": {"domain": d}}])
      for d in ("testserver", "testserver.local", "localhost", "example.com")],
    ("test_forward_follow_redirects", {"follow_redirects": True},
     [{"method": G, "url": "/redirect", "params": {"to": "/echo"}}]),
    ("test_forward_nofollow_redirects", {"follow_redirects": False},
     [{"method": G, "url": "/redirect", "params": {"to": "/echo"}}]),
    ("test_with_duplicate_headers", {}, [{"method": G, "url": "/dup", "headers": [["x-token", "foo"], ["x-token", "bar"]]}]),
    ("test_merge_url", {"base_url": "http://testserver/api/v1/"}, [{"method": G, "url": "/bar"}]),
    *[(f"test_ipv6_base_url[{b}]", {"base_url": b}, [{"method": G, "url": "/echo"}])
      for b in ("http://[::1]", "http://[::1]:8000", "http://[::1]:0")],
    # The scope, field by field.
    ("scope: https base url", {"base_url": "https://example.org"}, [{"method": G, "url": "/echo"}]),
    ("scope: port in base url", {"base_url": "http://example.org:8080"}, [{"method": G, "url": "/echo?a=1&b=%20"}]),
    ("scope: root_path", {"root_path": "/sub"}, [{"method": G, "url": "/echo"}]),
    ("scope: percent-encoded path", {}, [{"method": G, "url": "/echo/a%20b/%C3%A9"}]),
    ("scope: double-encoded path", {}, [{"method": G, "url": "/echo/x%2541"}]),
    ("scope: unicode path", {}, [{"method": G, "url": "/echo/é"}]),
    ("scope: params merged with query", {}, [{"method": G, "url": "/echo?a=1", "params": {"b": "2"}}]),
    ("scope: request header overrides client header", {"headers": {"X-A": "client"}},
     [{"method": G, "url": "/echo", "headers": [["x-a", "request"]]}]),
    ("scope: absolute url", {}, [{"method": G, "url": "http://other.example:81/echo"}]),
    # Bodies.
    ("body: content", {}, [{"method": P, "url": "/echo", "content": "hello"}]),
    ("body: json", {}, [{"method": P, "url": "/echo", "json": {"a": [1, 2], "b": "é"}}]),
    ("body: form data", {}, [{"method": P, "url": "/echo", "data": {"a": "1", "b": "x y"}}]),
    ("body: put, patch, delete, options",  {}, [
        {"method": "PUT", "url": "/echo", "content": "p"},
        {"method": "PATCH", "url": "/echo", "content": "q"},
        {"method": "DELETE", "url": "/echo"},
        {"method": "OPTIONS", "url": "/echo"}]),
    ("body: head has no body", {}, [{"method": "HEAD", "url": "/echo"}]),
    # Redirects.
    *[(f"redirect: POST then {c}", {}, [{"method": P, "url": "/redirect", "params": {"code": str(c)}, "content": "data"}])
      for c in (301, 302, 303, 307, 308)],
    ("redirect: to another host", {}, [{"method": G, "url": "/redirect", "params": {"to": "http://elsewhere/echo"}}]),
    ("redirect: per-request follow_redirects=False", {},
     [{"method": G, "url": "/redirect", "follow_redirects": False}]),
    # Cookies.
    ("cookies: kept by the client and sent back", {}, [
        {"method": G, "url": "/cookie", "params": {"name": "a", "value": "1"}},
        {"method": G, "url": "/echo"}]),
    ("cookies: client cookies", {"cookies": {"c": "3"}}, [{"method": G, "url": "/echo"}]),
    # Errors.
    ("raise_server_exceptions=True", {}, [{"method": G, "url": "/boom"}]),
    ("raise_server_exceptions=False", {"raise_server_exceptions": False}, [{"method": G, "url": "/boom"}]),
    ("not found", {}, [{"method": G, "url": "/nope"}]),
    ("method not allowed", {}, [{"method": P, "url": "/query"}]),
]


def main() -> None:
    for name, opts, calls in CASES:
        kw = dict(opts)
        if "client" in kw:
            kw["client"] = tuple(kw["client"])
        client = TestClient(app, **kw)
        results = [run_call(client, c) for c in calls]
        print(json.dumps({"name": name, "client": opts, "calls": calls, "results": results}, ensure_ascii=False))


if __name__ == "__main__":
    main()
