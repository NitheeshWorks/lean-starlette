"""Record golden responses for request.form() from Starlette 1.8.0, for
tests/Conformance.lean (`formGoldenCases`).

Run from the workspace with the upstream-spec venv (not in CI):
  upstream-spec/.venv/bin/python -I lean-starlette/tests/golden/record_forms.py \
    > lean-starlette/tests/golden/forms-starlette-1.8.0.jsonl

The apps are tests/test_formparsers.py's `app`, `multi_items_app`,
`app_with_headers` and `make_app_max_parts` (plus `sizes`, which reports a
file's length instead of its content), mounted in a Starlette
application (so a MultiPartException is a 400, as in the tests'
`Starlette(routes=[Mount("/", app=app)])` variants). Bodies are written with
fixed boundaries; each line stores the body as latin-1 text, or for large
hostile bodies a `recipe` that tests/Conformance.lean rebuilds byte for byte.
"""
import json, time
from typing import Any
from starlette.applications import Starlette
from starlette.datastructures import UploadFile
from starlette.requests import Request
from starlette.responses import JSONResponse
from starlette.routing import Mount
from starlette.testclient import TestClient


def make_app(kind: str, max_files=1000, max_fields=1000, max_part_size=1024 * 1024):
    async def app(scope, receive, send):
        request = Request(scope, receive)
        data = await request.form(max_files=max_files, max_fields=max_fields, max_part_size=max_part_size)
        output: dict[str, Any] = {}
        pairs = data.multi_items() if kind == "multi" else data.items()
        for key, value in pairs:
            if isinstance(value, UploadFile):
                content = await value.read()
                item = {"filename": value.filename, "size": value.size,
                        "content": len(content) if kind == "sizes" else content.decode(),
                        "content_type": value.content_type}
                if kind == "headers":
                    item["headers"] = list(value.headers.items())
            else:
                item = value
            if kind == "multi":
                output.setdefault(key, []).append(item)
            else:
                output[key] = item
        await request.close()
        await JSONResponse(output)(scope, receive, send)
    return Starlette(routes=[Mount("/", app=app)])


def part(name: str, value: bytes, filename: str | None = None, ctype: str | None = None,
         extra: list[tuple[str, str]] = [], b: str = "B") -> bytes:
    disp = f'form-data; name="{name}"' + (f'; filename="{filename}"' if filename is not None else "")
    hs = f"Content-Disposition: {disp}\r\n"
    if ctype:
        hs += f"Content-Type: {ctype}\r\n"
    for k, v in extra:
        hs += f"{k}: {v}\r\n"
    return f"--{b}\r\n".encode() + hs.encode("utf-8") + b"\r\n" + value + b"\r\n"


def mp(*parts: bytes, b: str = "B") -> bytes:
    return b"".join(parts) + f"--{b}--\r\n".encode()


MP = "multipart/form-data; boundary=B"
UE = "application/x-www-form-urlencoded"


def recipe(r: dict) -> bytes:
    """Large bodies, rebuilt identically by `recipeBody` in tests/Conformance.lean."""
    k, n = r["kind"], r["n"]
    if k == "urlFields":       # a=1&a=1&... n times
        return b"&".join([b"a=1"] * n)
    if k == "urlValue":        # a=<n bytes of x>
        return b"a=" + b"x" * n
    if k == "urlName":         # <n bytes of x>=1
        return b"x" * n + b"=1"
    if k == "mpFields":        # n text parts named f
        return mp(*[part("f", b"v")] * n)
    if k == "mpFiles":         # n file parts named f
        return mp(*[part("f", b"v", filename="f.txt")] * n)
    if k == "mpValue":         # one text part of n bytes
        return mp(part("f", b"x" * n))
    if k == "mpFile":          # one file part of n bytes
        return mp(part("f", b"x" * n, filename="big.txt"))
    raise ValueError(k)


cases = [
    # tests/test_formparsers.py, re-expressed with fixed bodies
    ("test_multipart_request_data", "plain", {}, MP, mp(part("some", b"data"))),
    ("test_multipart_request_files", "plain", {}, MP, mp(part("test", b"<file content>", filename="test.txt"))),
    ("test_multipart_request_files_with_content_type", "plain", {}, MP,
     mp(part("test", b"<file content>", filename="test.txt", ctype="text/plain"))),
    ("test_multipart_request_multiple_files", "plain", {}, MP,
     mp(part("test1", b"<file1 content>", filename="test1.txt", ctype="text/plain"),
        part("test2", b"<file2 content>", filename="test2.txt", ctype="text/plain"))),
    ("test_multipart_request_multiple_files_with_headers", "headers", {}, MP,
     mp(part("test1", b"<file1 content>", filename="test1.txt", ctype="text/plain"),
        part("test2", b"<file2 content>", filename="test2.txt", ctype="text/plain",
             extra=[("x-custom", "f2"), ("X-Second", "Two")]))),
    ("test_multi_items", "multi", {}, MP,
     mp(part("test1", b"abc"), part("test1", b"<file1 content>", filename="test1.txt", ctype="text/plain"),
        part("test1", b"<file2 content>", filename="test2.txt", ctype="text/plain"), part("test2", b"xyz"))),
    ("test_multipart_request_mixed_files_and_data", "plain", {}, "multipart/form-data; boundary=a7f7ac8d4e2e437c877bb7b8d7cc549c",
     mp(part("field0", b"value0", b="a7f7ac8d4e2e437c877bb7b8d7cc549c"),
        part("file", b"<file content>", filename="file.txt", ctype="text/plain", b="a7f7ac8d4e2e437c877bb7b8d7cc549c"),
        part("field1", b"value1", b="a7f7ac8d4e2e437c877bb7b8d7cc549c"), b="a7f7ac8d4e2e437c877bb7b8d7cc549c")),
    ("test_multipart_request_with_charset_for_filename", "plain", {}, "multipart/form-data; charset=utf-8; boundary=B",
     mp(part("file", b"<file content>", filename="文書.txt", ctype="text/plain"))),
    ("test_multipart_request_without_charset_for_filename", "plain", {}, MP,
     mp(part("file", b"<file content>", filename="画像.jpg", ctype="image/jpeg"))),
    ("test_multipart_request_with_encoded_value", "plain", {}, "multipart/form-data; charset=utf-8; boundary=B",
     mp(part("value", "Transférer".encode()))),
    ("test_urlencoded_request_data", "plain", {}, UE, b"some=data"),
    ("test_no_request_data", "plain", {}, None, b""),
    ("test_urlencoded_percent_encoding", "plain", {}, UE, b"some=da+ta"),
    ("test_urlencoded_percent_encoding_keys", "plain", {}, UE, b"so%20me=data"),
    ("urlencoded: raw non-ASCII bytes are latin-1", "plain", {}, UE, "a=é&b=%C3%A9".encode()),
    ("urlencoded: fields without '=' and empty fields", "multi", {}, UE, b"a&b=&&c=1&a=2"),
    ("urlencoded: an invalid escape is kept", "plain", {}, UE, b"a=%ZZ%2&b=%e9"),
    ("urlencoded: charset parameter ignored", "plain", {}, UE + "; charset=utf-8", b"k=v"),
    ("unknown content type: empty form", "plain", {}, "text/plain", b"a=1"),
    ("test_urlencoded_max_fields_is_customizable (low)", "plain", {"max_fields": 1}, UE, b"a=1&b=2"),
    ("test_urlencoded_max_fields_is_customizable (exact)", "plain", {"max_fields": 2}, UE, b"a=1&b=2"),
    ("test_urlencoded_max_part_size_is_customizable", "plain", {"max_part_size": 10}, UE, b"a=123456789"),
    ("test_urlencoded_max_part_size_is_customizable (exact)", "plain", {"max_part_size": 10}, UE, b"a=12345678"),
    ("test_multipart_request_decodes_charset (utf-8)", "plain", {}, "multipart/form-data; charset=utf-8; boundary=B",
     mp(part("value", b"\xc4\x99\xc5\xbc\xc4\x87"))),
    ("test_multipart_request_decodes_charset (bad utf-8)", "plain", {}, "multipart/form-data; charset=utf-8; boundary=B",
     mp(part("value", b"\xe9"))),
    ("test_multipart_request_decodes_charset (invalid-charset)", "plain", {}, "multipart/form-data; charset=invalid-charset; boundary=B",
     mp(part("value", b"\xe9"))),
    ("multipart: latin-1 charset", "plain", {}, "multipart/form-data; charset=ISO-8859-1; boundary=B",
     mp(part("value", b"\xc4\x99"))),
    ("test_multipart_request_resolves_charset_once", "plain", {}, "multipart/form-data; charset=starlette-test-invalid-charset; boundary=B",
     mp(part("one", b"one"), part("two", b"two"))),
    ("test_missing_boundary_parameter", "plain", {}, "multipart/form-data; charset=utf-8",
     b'--B\r\nContent-Disposition: form-data; name="file"; filename="file.txt"\r\n\r\nx\r\n--B--\r\n'),
    ("test_multipart_boundary_exceeds_limit", "plain", {}, "multipart/form-data; boundary=" + "x" * 71,
     b"--" + b"x" * 71 + b'\r\nContent-Disposition: form-data; name="f"\r\n\r\nx\r\n--' + b"x" * 71 + b"--\r\n"),
    ("test_multipart_headers_exceed_limit", "plain", {}, MP,
     b"--B\r\n" + b"".join(f"h{i}: v\r\n".encode() for i in range(9)) + b'Content-Disposition: form-data; name="f"\r\n\r\nx\r\n--B--\r\n'),
    ("test_missing_name_parameter_on_content_disposition", "plain", {}, MP,
     b'--B\r\nContent-Disposition: form-data; ="field0"\r\n\r\nvalue0\r\n--B--\r\n'),
    ("test_max_fields_is_customizable_low_raises", "plain", {"max_fields": 1}, MP, mp(part("a", b"1"), part("b", b"2"))),
    ("test_max_files_is_customizable_low_raises", "plain", {"max_files": 1}, MP,
     mp(part("a", b"1", filename="a.txt"), part("b", b"2", filename="b.txt"))),
    ("test_too_many_files_single_field_raise", "plain", {"max_files": 2}, MP,
     mp(*[part("f", b"x", filename=f"{i}.txt") for i in range(3)])),
    ("test_too_many_files_and_fields_raise (files)", "plain", {"max_files": 2, "max_fields": 2}, MP,
     mp(part("a", b"1", filename="a.txt"), part("b", b"2"), part("c", b"3", filename="c.txt"), part("d", b"4"), part("e", b"5", filename="e.txt"))),
    ("test_max_part_size_exceeds_custom_limit", "plain", {"max_part_size": 10}, MP, mp(part("f", b"x" * 11))),
    ("test_max_part_size_exceeds_custom_limit (file parts are not limited)", "plain", {"max_part_size": 10}, MP,
     mp(part("f", b"x" * 11, filename="f.txt"))),
    ("multipart: malformed (no closing boundary)", "plain", {}, MP, b'--B\r\nContent-Disposition: form-data; name="f"\r\n\r\nx'),
    ("multipart: garbage before the first boundary", "plain", {}, MP, b"junk\r\n" + mp(part("f", b"x"))),
    # limits at Starlette's defaults, and hostile sizes (rebuilt from recipes)
    ("test_urlencoded_too_many_fields_raise", "plain", {}, UE, {"kind": "urlFields", "n": 1001}),
    ("urlencoded: 1000 fields is the limit", "multi", {}, UE, {"kind": "urlFields", "n": 1000}),
    ("test_urlencoded_field_exceeds_max_part_size_raise", "plain", {}, UE, {"kind": "urlValue", "n": 1024 * 1024 + 1}),
    ("test_urlencoded_field_name_exceeds_max_part_size_raise", "plain", {}, UE, {"kind": "urlName", "n": 1024 * 1024 + 1}),
    ("test_too_many_fields_raise", "plain", {}, MP, {"kind": "mpFields", "n": 1001}),
    ("test_too_many_files_raise", "plain", {}, MP, {"kind": "mpFiles", "n": 1001}),
    ("test_max_fields_is_customizable_high", "plain", {"max_fields": 2000}, MP, {"kind": "mpFields", "n": 2000}),
    ("test_max_part_size_exceeds_limit", "plain", {}, MP, {"kind": "mpValue", "n": 1024 * 1024 + 1}),
    ("multipart: a 3 MB file part is not limited by max_part_size", "sizes", {}, MP, {"kind": "mpFile", "n": 3 * 1024 * 1024}),
    ("hostile: 200k urlencoded fields", "plain", {}, UE, {"kind": "urlFields", "n": 200000}),
    ("hostile: 50k multipart fields", "plain", {}, MP, {"kind": "mpFields", "n": 50000}),
    ("hostile: a 20 MB urlencoded value", "plain", {}, UE, {"kind": "urlValue", "n": 20 * 1024 * 1024}),
    ("hostile: a 20 MB multipart text part", "plain", {}, MP, {"kind": "mpValue", "n": 20 * 1024 * 1024}),
]

for name, kind, limits, ctype, body in cases:
    raw = recipe(body) if isinstance(body, dict) else body
    client = TestClient(make_app(kind, **limits), raise_server_exceptions=False)
    headers = {"content-type": ctype} if ctype else {}
    t0 = time.monotonic()
    r = client.post("/", content=raw, headers=headers)
    ms = (time.monotonic() - t0) * 1000
    # warm best of 5 (stack policy for tight bounds): the first call above warms up
    warm = []
    for _ in range(5):
        t1 = time.monotonic()
        client.post("/", content=raw, headers=headers)
        warm.append((time.monotonic() - t1) * 1000)
    print(json.dumps({
        "name": name, "kind": kind, "limits": limits, "content_type": ctype,
        "body": body if isinstance(body, dict) else raw.decode("latin-1"),
        "status": r.status_code, "content_type_out": r.headers.get("content-type"),
        "content": r.content.decode("utf-8"), "upstream_ms": round(ms, 1),
        "upstream_warm_ms": round(min(warm), 2),
    }, ensure_ascii=False))
