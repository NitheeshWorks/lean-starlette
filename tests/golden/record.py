"""Record golden responses from Starlette 1.8.0 for tests/Conformance.lean.

Run from the workspace with the upstream-spec venv (not in CI):
  upstream-spec/.venv/bin/python -I lean-starlette/tests/golden/record.py > lean-starlette/tests/golden/starlette-1.8.0.jsonl

The apps mirror `goldenApps` in tests/Conformance.lean. Each line is one request
with the response's status, the headers compared, and the body.
"""
import json
from starlette.applications import Starlette
from starlette.exceptions import HTTPException
from starlette.responses import JSONResponse, PlainTextResponse, Response, RedirectResponse, HTMLResponse
from starlette.routing import Mount, Route, Router
from starlette.testclient import TestClient

def homepage(r): return Response("Hello, world", media_type="text/plain")
def users(r): return Response("All users", media_type="text/plain")
def user(r): return Response("User " + r.path_params["username"], media_type="text/plain")
def item(r): return JSONResponse({"item_id": r.path_params["item_id"], "q": r.query_params.get("q")})
def echo(r): return JSONResponse({"query": r.query_params.multi_items(), "path": r.url.path})
async def create(r): return JSONResponse(await r.json(), status_code=201)
def teapot(r): raise HTTPException(418, "I'm a teapot", headers={"X-Tea": "earl grey"})
def nobody(r): return Response(status_code=204)
def html(r): return HTMLResponse("<h1>Hi</h1>")
def old(r): return RedirectResponse("/new place")

routes = [
    Route("/", homepage, methods=["GET"]),
    Mount("/users", routes=[Route("/", users), Route("/{username}", user)]),
    Route("/items/{item_id:int}", item),
    Route("/echo/{rest:path}", echo),
    Route("/create", create, methods=["POST"]),
    Route("/teapot", teapot),
    Route("/nobody", nobody),
    Route("/html", html),
    Route("/old", old),
]
app = Starlette(routes=routes)
client = TestClient(app, raise_server_exceptions=False)

KEEP = ["content-type", "content-length", "location", "allow", "x-tea"]
requests = [
    ("GET", "/", None, None),
    ("HEAD", "/", None, None),
    ("POST", "/", None, None),
    ("GET", "/nope", None, None),
    ("GET", "/users", None, None),
    ("GET", "/users/", None, None),
    ("GET", "/users/tom", None, None),
    ("GET", "/users/tom/", None, None),
    ("GET", "/items/42?q=x", None, None),
    ("GET", "/items/007", None, None),
    ("GET", "/items/abc", None, None),
    ("GET", "/echo/a/b?x=1&x=2&y=%ZZ&z", None, None),
    ("GET", "/echo/%E2%82%AC?q=a+b", None, None),
    ("POST", "/create", None, '{"a": [1, 2.5, null, "é"]}'),
    ("POST", "/create", None, "{"),
    ("GET", "/teapot", None, None),
    ("GET", "/nobody", None, None),
    ("GET", "/html", None, None),
    ("GET", "/old", None, None),
    ("PUT", "/items/1", None, None),
]
for method, url, headers, body in requests:
    r = client.request(method, url, headers=headers, content=body, follow_redirects=False)
    print(json.dumps({
        "method": method, "url": url, "body": body,
        "status": r.status_code,
        "headers": {k: r.headers[k] for k in KEEP if k in r.headers},
        "content": r.content.decode("utf-8"),
    }, ensure_ascii=False))
