"""Record unit goldens for the m5 middleware card from Python 3.13 and
Starlette 1.8.0, for tests/Conformance.lean (`unitGoldenCases` in
tests/MiddlewareCases.lean).

Run from the workspace with the upstream-spec venv (not in CI):
  upstream-spec/.venv/bin/python -I lean-starlette/tests/golden/record_m5_units.py \
    > lean-starlette/tests/golden/m5-units-starlette-1.8.0.jsonl

Kinds:
* `regex`: `re.compile(p)` (or its error) and `fullmatch` on each text, as
  `CORSMiddleware(allow_origin_regex=p)` uses it.
* `cookie_parser`: `starlette.requests.cookie_parser(s)`, the inputs of
  tests/test_requests.py's cookie tests and more.
* `quote`: `http.cookies._quote(v)`.
* `set_cookie`: the `Set-Cookie` value of `Response.set_cookie(...)`, or the
  exception it raises.
* `session_sign`: the cookie value `SessionMiddleware` writes for a session at
  a fixed signing time (`TimestampSigner("example")`, base64 of `json.dumps`).
"""
import http.cookies
import json
import re
from base64 import b64encode

import itsdangerous
from starlette.requests import cookie_parser
from starlette.responses import Response

pats = [r"https://.*", r"https://.*\.example.org", r"https://[a-z0-9-]+\.example\.org", r"^https?://(www\.)?foo\.com$",
 r"https://(?:api|www)\.x\.io(:\d{2,5})?", r"[^/]+", r"\w+://\w+", r"\d{3}", r"a{,3}b", r"a{2,}", r"x{", r"{", r"a{3}", r"[]a]+",
 r"[a\-z]", r"[\d.]+", r"\bfoo\b.*", r"\Bx", r"a|b|", r"(a|b)*c", r"(?P<h>[a-z]+)\.com", r"a(?#comment)b", r"\x41é\U0001F600",
 r"\0\101", r"[\101-\132]+", r"\s*x", r"\S+", r"\W", r"\D", r".", r"\.", r"\\", r"a**", r"^*", r"(", r")", r"[", r"[]", r"\q", r"\1",
 r"(?=a)", r"(?<!a)", r"(?i)a", r"a*+", r"(?>a)", r"\N{DIGIT ONE}", r"a{3,2}", r"[z-a]", r"[\d-a]", r"(?P=n)", r"a$", r"a$\n", r"(?:)*", r"()*b",
 r"[^\W\d]+", r"[\s\S]", r"\Aab\Z", r"a{1000}", r"a{1001}", r"https://(?:[a-z0-9-]+\.)*example\.(com|org)", r"[-a]", r"[a-]", r"[--]", r"é+", r"\é",
 r"(?P<1a>x)", r"a?", r"a??", r"a+?b", r"[\b]", r"\Z*", r"a{,}", r"(a)(b)(c)", r"[^]]", r"[^]", r"\8", r"[\8]", r"\400", r"\377", r"(?", r"(?x)"]
texts = ["", "a", "b", "ab", "aaa", "aab", "c", "abc", "https://a.example.org", "https://evil.com/?https://a.example.org", "http://x",
 "https://", "foo.com", "https://foo.com", "http://www.foo.com", "https://api.x.io:8080", "https://www.x.io", "123", "12", "١٢٣", "x{", "{",
 "aaab", "]a]", "-", "z", "1.2", "foo bar", " foo", "Ax", "xx", "é", "Aé😀", "\0A", "ABC", "  x", "　x", "_", "a\n", "\n", "aaaaaaaa",
 "https://a.b.example.com", "https://example.org", "ab.com", "b", "]", "^", "\b", "a"*1000, "a"*1001, "8", "\x08", "\xff", "abcd", "café"]

for p in pats:
    try:
        rx = re.compile(p)
    except re.error as e:
        print(json.dumps({"kind": "regex", "pattern": p, "error": str(e)}))
        continue
    print(json.dumps({"kind": "regex", "pattern": p, "texts": texts, "match": [bool(rx.fullmatch(t)) for t in texts]}))

COOKIES = [
    "chips=ahoy; vienna=finger",
    'keebler="E=mc2; L=\\"Loves\\"; fudge=\\012;"',
    "keebler=E=mc2", "key:term=value:term", "a=b; c=[; d=r; f=h", "a=b; Domain=example.com", "a=b; h=i; a=c",
    "abc=def; unnamed; django_language=en", 'a=b; "; c=d', "a b c=d e = f; gh=i",
    'a   b,c<>@:/[]?{}=d  "  =e,f g', "saint=Andr\u00e9 Bessette", "  =  b  ;  ;  =  ;   c  =  ;  ",
    'q="a\\073b\\"c\\\\d"', 'q="\\400\\377\\08"', 'q="unterminated', 'q=""', 'q="\\', "", ";;;", "=", "a=1\u3000",
    "\u3000a=1", "x=\\012", "sessionid=abc; csrftoken=def; sessionid=ghi",
]
for c in COOKIES:
    print(json.dumps({"kind": "cookie_parser", "input": c, "output": list(cookie_parser(c).items())}))

VALUES = ["", "abc", "a b", "a;b", 'a"b', "a\\b", "caf\u00e9", "\u20ac", "x\ny", "{}", "a,b", "=", "(:)", "\x7f", "\x00"]
for v in VALUES:
    print(json.dumps({"kind": "quote", "value": v, "quoted": http.cookies._quote(v)}))

SET = [
    {"key": "mycookie", "value": "myvalue", "max_age": 10, "expires": "Wed, 21 Oct 2015 07:28:00 GMT", "path": "/",
     "domain": "localhost", "secure": True, "httponly": True, "samesite": "none"},
    {"key": "mycookie", "value": "myvalue", "path": None},
    {"key": "mycookie", "value": "myvalue", "samesite": "strict"},
    {"key": "mycookie", "value": "myvalue", "samesite": None},
    {"key": "k", "value": "a b;c", "max_age": -5},
    {"key": "k", "value": "", "domain": "", "path": ""},
    {"key": "k!#$%&'*+-.^_`|~:", "value": "v"},
    {"key": "bad key", "value": "v"},
    {"key": "Path", "value": "v"},
    {"key": "", "value": "v"},
]
for kw in SET:
    r = Response()
    try:
        r.set_cookie(**kw)
        out = {"ok": [v.decode("latin-1") for k, v in r.raw_headers if k == b"set-cookie"][0]}
    except Exception as e:
        out = {"error": type(e).__name__}
    print(json.dumps({"kind": "set_cookie", "args": kw, **out}))

for data, ts in [({}, 0), ({"some": "data"}, 1700000000), ({"a": "1", "b": [1, 2.5, None, True], "c": {"d": "\u00e9"}}, 1760000000)]:
    signer = itsdangerous.TimestampSigner("example")
    signer.get_timestamp = lambda ts=ts: ts
    value = signer.sign(b64encode(json.dumps(data).encode("utf-8"))).decode("utf-8")
    print(json.dumps({"kind": "session_sign", "secret": "example", "data": data, "timestamp": ts, "cookie": value}))
