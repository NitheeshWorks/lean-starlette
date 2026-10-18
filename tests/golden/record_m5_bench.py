"""Record Starlette 1.8.0's times on the hostile inputs of m5's benches, for
tests/Bench.lean (`m5bench`), whose bounds are twice these.

Run from the workspace with the upstream-spec venv (not in CI), on an idle
machine:
  upstream-spec/.venv/bin/python -I lean-starlette/tests/golden/record_m5_bench.py \
    > lean-starlette/tests/golden/m5-bench-starlette-1.8.0.json

Every input is built from a recipe that tests/Bench.lean rebuilds byte for
byte. Each time is the best of 5 warm runs, in milliseconds.

* cookie: `starlette.requests.cookie_parser` on a huge `Cookie` header
  (70 000 distinct names, 100 000 repeats of one name, 50 000 quoted
  values with an octal escape).
* cors: 1000 requests through a `Starlette` app with `CORSMiddleware` and
  10 000 allowed origins, called as ASGI (no server): a preflight from an
  origin not in the list (a full scan) and a simple GET from the last one.
* gzip: one GET over TCP (uvicorn 0.54, h11) through `GZipMiddleware`
  (compresslevel 9) with curl asking for gzip: 10 MB of text, 20 MB of
  zeros (a 1000:1 "bomb" body) and 2 MB of random bytes.
"""
import asyncio, json, socket, subprocess, sys, threading, time

import uvicorn
from starlette.applications import Starlette
from starlette.middleware import Middleware
from starlette.middleware.cors import CORSMiddleware
from starlette.middleware.gzip import GZipMiddleware
from starlette.requests import cookie_parser
from starlette.responses import PlainTextResponse, Response
from starlette.routing import Route


def best(f, n=5):
    ts = []
    for _ in range(n):
        t0 = time.perf_counter()
        f()
        ts.append((time.perf_counter() - t0) * 1000)
    return round(min(ts), 3)


# ---- inputs (mirrored in tests/Bench.lean) ----

def cookie_inputs():
    return {
        "distinct70k": "; ".join(f"k{i}=v{i}" for i in range(70000)),
        "dup100k": "; ".join(["a=1"] * 100000),
        "quoted50k": "; ".join(f'k{i}="v\\073{i}"' for i in range(50000)),
    }


def origins():
    return [f"https://o{i}.example.com" for i in range(10000)]


def gz_text(n):
    words = [w.encode() for w in ["starlette ", "lean ", "middleware ", "gzip ", "the ", "a ", "response ",
                                  "body ", "\n", '{"k": 12345} ']]
    out = bytearray()
    x = 12345
    while len(out) < n:
        x = (x * 1103515245 + 12345) % 2147483648
        out += words[x % 10]
    return bytes(out[:n])


def gz_rand(n):
    out = bytearray(n)
    x = 7
    for i in range(n):
        x = (x * 6364136223846793005 + 1442695040888963407) % 18446744073709551616
        out[i] = x >> 56
    return bytes(out)


def gzip_bodies():
    return {"text10m": gz_text(10_000_000), "zeros20m": bytes(20_000_000), "rand2m": gz_rand(2_000_000)}


# ---- cookie ----

def bench_cookie():
    res = {}
    for name, s in cookie_inputs().items():
        n = len(cookie_parser(s))
        res[name] = {"bytes": len(s), "names": n, "upstream_warm_ms": best(lambda: cookie_parser(s))}
    return res


# ---- cors ----

def bench_cors():
    app = Starlette(routes=[Route("/", lambda r: PlainTextResponse("x"))], middleware=[
        Middleware(CORSMiddleware, allow_origins=origins(), allow_methods=["GET"], allow_headers=["X-A"])])

    def scope(method, origin, extra):
        hs = [(b"host", b"example.org"), (b"origin", origin.encode())] + extra
        return {"type": "http", "asgi": {"version": "3.0"}, "http_version": "1.1", "method": method,
                "scheme": "http", "path": "/", "raw_path": b"/", "root_path": "", "query_string": b"",
                "headers": hs, "server": ("example.org", 80), "client": ("127.0.0.1", 1)}

    cases = {
        "preflightMiss": scope("OPTIONS", "https://evil.example.net",
                               [(b"access-control-request-method", b"GET")]),
        "simpleLast": scope("GET", "https://o9999.example.com", []),
    }
    res = {}
    for name, sc in cases.items():
        statuses = []

        async def run1000():
            for _ in range(1000):
                async def receive():
                    return {"type": "http.request", "body": b"", "more_body": False}

                async def send(m):
                    if m["type"] == "http.response.start":
                        statuses.append(m["status"])
                await app(dict(sc), receive, send)

        loop = asyncio.new_event_loop()
        ms = best(lambda: loop.run_until_complete(run1000()))
        loop.close()
        res[name] = {"requests": 1000, "status": statuses[0], "upstream_warm_ms": ms}
    return res


# ---- gzip ----

def free_port():
    s = socket.socket()
    s.bind(("127.0.0.1", 0))
    p = s.getsockname()[1]
    s.close()
    return p


def bench_gzip():
    bodies = gzip_bodies()
    routes = [Route(f"/{k}", (lambda b: lambda r: Response(b, media_type="text/plain"))(v)) for k, v in bodies.items()]
    app = Starlette(routes=routes, middleware=[Middleware(GZipMiddleware, minimum_size=500, compresslevel=9)])
    port = free_port()
    server = uvicorn.Server(uvicorn.Config(app, host="127.0.0.1", port=port, log_level="error", http="h11"))
    th = threading.Thread(target=server.run, daemon=True)
    th.start()
    while not server.started:
        time.sleep(0.05)
    res = {}
    try:
        for name, body in bodies.items():
            out = {}

            def get():
                r = subprocess.run(["curl", "-s", "-H", "Accept-Encoding: gzip", "-o", "/dev/null", "-w",
                                    "%{http_code} %{size_download}", f"http://127.0.0.1:{port}/{name}"],
                                   capture_output=True, text=True, check=True)
                out["r"] = r.stdout

            ms = best(get)
            status, size = out["r"].split()
            res[name] = {"bytes": len(body), "status": int(status), "compressed": int(size), "upstream_warm_ms": ms}
    finally:
        server.should_exit = True
        th.join(timeout=10)
    return res


if __name__ == "__main__":
    import starlette
    doc = {"starlette": starlette.__version__, "uvicorn": uvicorn.__version__,
           "python": sys.version.split()[0],
           "cookie": bench_cookie(), "cors": bench_cors(), "gzip": bench_gzip()}
    print(json.dumps(doc, indent=1))
