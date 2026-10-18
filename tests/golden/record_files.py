"""Record golden responses for files, static files, streaming and background
tasks from Starlette 1.8.0, for tests/Conformance.lean (`filesGoldenCases`).

Run from the workspace with the upstream-spec venv (not in CI):
  upstream-spec/.venv/bin/python -I lean-starlette/tests/golden/record_files.py \
    > lean-starlette/tests/golden/files-starlette-1.8.0.jsonl

The directory fixture and the app mirror `filesFixture` and `filesApp` in
tests/Conformance.lean; every file's mtime is set to 1700000000 s, except
frac.txt at 1700000000.123456789 s. The ETag is compared byte for byte; a
multipart boundary is replaced by `*`.
"""
import json, os, tempfile
from starlette.applications import Starlette
from starlette.background import BackgroundTasks
from starlette.responses import FileResponse, PlainTextResponse, StreamingResponse
from starlette.routing import Mount, Route
from starlette.staticfiles import StaticFiles
from starlette.testclient import TestClient

FILES = {
    "static/example.txt": "0123456789abcdefghij",
    "static/index.html": "<h1>Index</h1>",
    "static/sub/index.html": "<h1>Sub</h1>",
    "static/404.html": "<h1>Custom 404</h1>",
    "secret.txt": "secret",
    "static/frac.txt": "fractional mtime",
    "static/x\\y.txt": "backslash name",
}
MTIME_NS = {"static/frac.txt": 1700000000123456789}

root = tempfile.mkdtemp()
for rel, text in FILES.items():
    p = os.path.join(root, rel)
    os.makedirs(os.path.dirname(p), exist_ok=True)
    with open(p, "w") as f:
        f.write(text)
    ns = MTIME_NS.get(rel, 1700000000 * 10**9)
    os.utime(p, ns=(ns, ns))
static = os.path.join(root, "static")

log = []
def file(r): return FileResponse(os.path.join(static, "example.txt"))
async def chunks():
    for c in ["a", "bb", "ccc"]:
        yield c
def stream(r): return StreamingResponse(chunks(), media_type="text/plain")
def bg(r):
    log.clear()
    tasks = BackgroundTasks()
    for i in [1, 2, 3]:
        tasks.add_task(log.append, i)
    return PlainTextResponse("ok", background=tasks)
def bglog(r): return PlainTextResponse(",".join(map(str, log)))

app = Starlette(routes=[
    Mount("/static", StaticFiles(directory=static)),
    Mount("/site", StaticFiles(directory=static, html=True)),
    Route("/file", file),
    Route("/stream", stream),
    Route("/bg", bg),
    Route("/bglog", bglog),
])
client = TestClient(app, raise_server_exceptions=False)

LM = "Tue, 14 Nov 2023 22:13:20 GMT"
KEEP = ["content-type", "content-length", "content-range", "accept-ranges", "last-modified", "etag", "location", "allow"]
requests = [
    ("GET", "/static/example.txt", {}),
    ("HEAD", "/static/example.txt", {}),
    ("GET", "/static/missing.txt", {}),
    ("POST", "/static/example.txt", {}),
    ("GET", "/static/example.txt", {"range": "bytes=0-4"}),
    ("GET", "/static/example.txt", {"range": "bytes=15-"}),
    ("GET", "/static/example.txt", {"range": "bytes=-5"}),
    ("GET", "/static/example.txt", {"range": "bytes=0-1,5-6"}),
    ("GET", "/static/example.txt", {"range": "bytes=0-3,2-5"}),
    ("GET", "/static/example.txt", {"range": "bytes=100-200"}),
    ("GET", "/static/example.txt", {"range": "bytes=5-2"}),
    ("GET", "/static/example.txt", {"range": "items=0-1"}),
    ("GET", "/static/example.txt", {"range": "bytes=0-4", "if-range": LM}),
    ("GET", "/static/example.txt", {"range": "bytes=0-4", "if-range": "Wed, 01 Jan 2020 00:00:00 GMT"}),
    ("GET", "/static/example.txt", {"if-modified-since": LM}),
    ("GET", "/static/example.txt", {"if-modified-since": "Wed, 01 Jan 2020 00:00:00 GMT"}),
    ("GET", "/static/example.txt", {"if-none-match": "*"}),
    ("GET", "/static/example.txt", {"if-none-match": '"nomatch"'}),
    ("GET", "/static/example.txt", {"if-none-match": '"nomatch"', "if-modified-since": LM}),
    ("GET", "/static/frac.txt", {}),
    ("GET", "/static/x%5cy.txt", {}),
    ("GET", "/static/x%5Cy.txt", {"if-none-match": '"nomatch", W/"0f52ab3523ad636d7688dc1b577fc7b1"'}),
    ("GET", "/static/", {}),
    ("GET", "/static/sub", {}),
    ("GET", "/site/", {}),
    ("GET", "/site/sub", {}),
    ("GET", "/site/sub/", {}),
    ("GET", "/site/nope", {}),
    ("GET", "/static/..%2Fsecret.txt", {}),
    ("GET", "/site/..%2Fsecret.txt", {}),
    ("GET", "/file", {}),
    ("GET", "/file", {"range": "bytes=2-3"}),
    ("GET", "/stream", {}),
    ("GET", "/bg", {}),
    ("GET", "/bglog", {}),
]

def norm(k, v):
    if k == "content-type" and v.startswith("multipart/byteranges; boundary="):
        return "multipart/byteranges; boundary=*"
    return v

for method, url, headers in requests:
    r = client.request(method, url, headers=headers, follow_redirects=False)
    multipart = r.headers.get("content-type", "").startswith("multipart/")
    print(json.dumps({
        "method": method, "url": url, "headers_in": headers,
        "status": r.status_code,
        "headers": {k: norm(k, r.headers[k]) for k in KEEP if k in r.headers},
        "content": None if multipart else r.content.decode("utf-8"),
    }, ensure_ascii=False))
