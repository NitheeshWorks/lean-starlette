"""Record uvicorn 0.54 (h11) + Starlette 1.8.0 on large request bodies over
TCP, for tests/Bench.lean (`bodybench`), whose bounds are twice these.

Run from the workspace with the upstream-spec venv (not in CI), on an idle
machine:
  upstream-spec/.venv/bin/python -I lean-starlette/tests/golden/record_body_bench.py \
    > lean-starlette/tests/golden/body-bench-starlette-1.8.0.json

Each case POSTs `mib` MiB of `x` with curl (`Expect:` off, as a client that
does not wait for 100 Continue) to a fresh server process, once to warm up and
then 5 times: `upstream_warm_ms` is the best of the 5, `upstream_rss_mb` the
server's peak resident memory (VmHWM, reset after the warm-up run) less its
resident memory before the 5. `route`: `/missing` is a 404 (the body is not read), `/len`
reads the body and answers its length.
"""
import json, os, socket, subprocess, sys, tempfile, time

APP = '''
from starlette.applications import Starlette
from starlette.responses import PlainTextResponse
from starlette.routing import Route
async def length(request):
    return PlainTextResponse(str(len(await request.body())))
app = Starlette(routes=[Route("/len", length, methods=["POST"])])
'''


def status_kb(pid, key):
    for line in open(f"/proc/{pid}/status"):
        if line.startswith(key + ":"):
            return int(line.split()[1])
    return 0


def free_port():
    s = socket.socket(); s.bind(("127.0.0.1", 0)); p = s.getsockname()[1]; s.close()
    return p


def run_case(mib, route, tmp):
    body = os.path.join(tmp, "body.bin")
    with open(body, "wb") as f:
        for _ in range(mib):
            f.write(b"x" * (1024 * 1024))
    port = free_port()
    proc = subprocess.Popen([sys.executable, "-I", "-c",
                             APP + f"\nimport uvicorn\nuvicorn.run(app, host='127.0.0.1', port={port}, log_level='error', http='h11')"],
                            cwd=tmp)
    try:
        for _ in range(100):
            try:
                socket.create_connection(("127.0.0.1", port)).close(); break
            except OSError:
                time.sleep(0.05)
        args = ["curl", "-s", "-o", "/dev/null", "-w", "%{http_code}", "-H", "Expect:",
                "--data-binary", f"@{body}", f"http://127.0.0.1:{port}{route}"]
        status = subprocess.run(args, capture_output=True, text=True).stdout
        # reset the high-water mark after the warm-up run
        with open(f"/proc/{proc.pid}/clear_refs", "w") as f:
            f.write("5")
        base = status_kb(proc.pid, "VmRSS")
        ts = []
        for _ in range(5):
            t0 = time.perf_counter()
            status = subprocess.run(args, capture_output=True, text=True).stdout
            ts.append((time.perf_counter() - t0) * 1000)
        peak = status_kb(proc.pid, "VmHWM")
        return {"status": int(status), "upstream_warm_ms": round(min(ts), 2),
                "upstream_rss_mb": round((peak - base) / 1024, 1)}
    finally:
        proc.terminate(); proc.wait()
        os.remove(body)


if __name__ == "__main__":
    import starlette, uvicorn
    out = {"starlette": starlette.__version__, "uvicorn": uvicorn.__version__, "cases": {}}
    with tempfile.TemporaryDirectory() as tmp:
        for mib in (10, 20):
            for route, label in (("/missing", "404"), ("/len", "read")):
                out["cases"][f"post{mib}m-{label}"] = {"mib": mib, "route": route, **run_case(mib, route, tmp)}
    print(json.dumps(out, indent=1))
