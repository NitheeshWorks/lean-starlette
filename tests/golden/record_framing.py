"""Record uvicorn 0.54 (h11 0.16) + Starlette 1.8.0's raw response bytes, for
tests/FramingCases.lean, which replays the same bytes against
`Application.run` and compares what comes back.

Run from the workspace with the upstream-spec venv (not in CI):
  upstream-spec/.venv/bin/python -I lean-starlette/tests/golden/record_framing.py \
    > lean-starlette/tests/golden/framing-uvicorn-0.54.jsonl

With `--port N` it drives a server already listening on N instead (a Lean
one, during development) and prints the differences.

Each scenario is a list of steps on one connection: bytes to send, then
everything received until the connection is idle for 300 ms or closed. The
`date` value is masked; the server header is uvicorn's own (`server:
uvicorn`), which the Lean server is configured to send in the replay.
"""
import json, socket, sys, threading, time

APP_ROUTES = None


def make_app():
    from starlette.applications import Starlette
    from starlette.requests import Request
    from starlette.responses import JSONResponse, PlainTextResponse, Response, StreamingResponse
    from starlette.routing import Route

    async def stream(request):
        async def gen():
            yield b"one"
            yield b""
            yield b"two"
        return StreamingResponse(gen(), media_type="text/plain")

    async def echo(request: Request):
        body = await request.body()
        return PlainTextResponse(f"{len(body)}:{body[:20].decode('latin-1')}")

    async def boom(request):
        raise RuntimeError("boom")

    return Starlette(routes=[
        Route("/200", lambda r: PlainTextResponse("hello")),
        Route("/204", lambda r: Response(status_code=204)),
        Route("/304", lambda r: Response(status_code=304)),
        Route("/422", lambda r: JSONResponse({"detail": "bad"}, status_code=422)),
        Route("/201", lambda r: JSONResponse({"a": 1}, status_code=201)),
        Route("/500", boom),
        Route("/stream", stream),
        Route("/echo", echo, methods=["POST"]),
        Route("/headers", lambda r: PlainTextResponse("h", headers={"X-Custom": "1", "set-cookie": "a=b"})),
    ])


def get(path, extra="", version="HTTP/1.1", method="GET"):
    return f"{method} {path} {version}\r\nHost: x\r\n{extra}\r\n"


SCENARIOS = [
    ("200, kept alive for a second request", [get("/200"), get("/200")]),
    ("204", [get("/204", "Connection: close\r\n")]),
    ("304", [get("/304", "Connection: close\r\n")]),
    ("404", [get("/nope", "Connection: close\r\n")]),
    ("405", [get("/200", "Connection: close\r\n", method="POST")]),
    ("422", [get("/422", "Connection: close\r\n")]),
    ("500 closes the connection", [get("/500")]),
    ("201 JSON", [get("/201", "Connection: close\r\n")]),
    ("HEAD", [get("/200", method="HEAD"), get("/stream", method="HEAD")]),
    ("streaming is chunked", [get("/stream"), get("/200")]),
    ("Connection: close", [get("/200", "Connection: close\r\n")]),
    ("Connection: Close (h11 adds its own)", [get("/200", "Connection: Close\r\n")]),
    ("Connection: keep-alive, close", [get("/200", "Connection: keep-alive, close\r\n")]),
    ("HTTP/1.0", [get("/200", version="HTTP/1.0")]),
    ("HTTP/1.0 stream (until close)", [get("/stream", version="HTTP/1.0")]),
    ("app headers keep their spelling and order", [get("/headers", "Connection: close\r\n")]),
    ("POST with a body, then a GET", ["POST /echo HTTP/1.1\r\nHost: x\r\nContent-Length: 5\r\n\r\nhello", get("/200")]),
    ("pipelined", [get("/200") + get("/201")]),
    ("pipelined after a body", ["POST /echo HTTP/1.1\r\nHost: x\r\nContent-Length: 2\r\n\r\nab" + get("/200")]),
    ("chunked body, then a GET", ["POST /echo HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n3\r\nabc\r\n0\r\n\r\n", get("/200")]),
    ("Expect: 100-continue", ["POST /echo HTTP/1.1\r\nHost: x\r\nContent-Length: 5\r\nExpect: 100-continue\r\n\r\n", "hello"]),
    ("Expect with the body already sent", ["POST /echo HTTP/1.1\r\nHost: x\r\nContent-Length: 5\r\nExpect: 100-continue\r\n\r\nhello"]),
]


def mask(b: bytes) -> str:
    s = b.decode("latin-1")
    out = []
    for line in s.split("\r\n"):
        if line.lower().startswith("date: "):
            line = line[:6] + "<date>"
        out.append(line)
    return "\r\n".join(out)


def run_scenario(port, steps):
    c = socket.create_connection(("127.0.0.1", port))
    c.settimeout(0.3)
    got = []
    closed = False
    for step in steps:
        c.sendall(step.encode("latin-1"))
        data = b""
        while True:
            try:
                d = c.recv(65536)
            except socket.timeout:
                break
            if not d:
                closed = True
                break
            data += d
        got.append(mask(data))
        if closed:
            break
    if not closed:
        try:
            closed = c.recv(1) == b""
        except socket.timeout:
            closed = False
    c.close()
    return got, closed


def serve_uvicorn():
    import uvicorn
    s = socket.socket(); s.bind(("127.0.0.1", 0)); port = s.getsockname()[1]; s.close()
    server = uvicorn.Server(uvicorn.Config(make_app(), host="127.0.0.1", port=port, log_level="critical", http="h11"))
    th = threading.Thread(target=server.run, daemon=True)
    th.start()
    while not server.started:
        time.sleep(0.05)
    return server, th, port


if __name__ == "__main__":
    if "--port" in sys.argv:
        port = int(sys.argv[sys.argv.index("--port") + 1])
        golden = {}
        with open(sys.argv[sys.argv.index("--golden") + 1]) as f:
            for line in f:
                d = json.loads(line); golden[d["name"]] = d
        bad = 0
        for name, steps in SCENARIOS:
            got, closed = run_scenario(port, steps)
            w = golden[name]
            if got != w["received"] or closed != w["closed"]:
                bad += 1
                print("DIFF", name, "closed", closed, "want", w["closed"])
                for g, ww in zip(got, w["received"] + [""] * 5):
                    if g != ww:
                        print("  got ", repr(g)); print("  want", repr(ww))
            else:
                print("ok  ", name)
        sys.exit(1 if bad else 0)
    server, th, port = serve_uvicorn()
    try:
        for name, steps in SCENARIOS:
            got, closed = run_scenario(port, steps)
            print(json.dumps({"name": name, "steps": steps, "received": got, "closed": closed}))
    finally:
        server.should_exit = True
        th.join(5)
