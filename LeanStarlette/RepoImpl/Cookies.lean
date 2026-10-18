import LeanStarlette.RepoImpl.Responses
import LeanStarlette.RepoImpl.Request
import LeanStarlette.RepoImpl.HttpDate
import LeanStarlette.RepoImpl.PyRe

/-!
# RepoImpl: cookies

* `cookieParser` is `starlette.requests.cookie_parser`: split on `;`, split
  each piece at its first `=` (no `=`: an empty name), strip both sides
  (Python's `str.strip`, Unicode whitespace), skip a piece with neither, and
  unquote the value as `http.cookies._unquote` does; a later name wins,
  keeping the first one's place (a `dict`).
* `Response.set_cookie` and `Response.delete_cookie` print the
  `Set-Cookie` line of `http.cookies.SimpleCookie`: the value quoted by
  `_quote`, then the attributes in `Morsel.OutputString`'s order (sorted
  by attribute key).

Differences from upstream, documented in CONTRIBUTING: `samesite` is an
enumeration (upstream asserts one of the three strings); `expires` is a
date or text (upstream's integer form, seconds from now, needs the clock:
pass the date); `delete_cookie` expires the cookie at the Unix epoch, where
upstream prints the current time (both are in the past when the browser
reads them); `partitioned` prints `Partitioned` (Python 3.14's output;
3.13 raises); a value character above U+00FF is sent as is, where
upstream's `latin-1` encoding raises.
-/

namespace LeanStarlette

/-- `http.cookies._LegalChars`: the characters of a name, and of a value
sent unquoted. -/
def isCookieLegal (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || ('0' ≤ c && c ≤ '9') || "!#$%&'*+-.^_`|~:".toList.contains c

/-- `_UnescapedChars`: kept as they are inside quotes. -/
def isCookieUnescaped (c : Char) : Bool := isCookieLegal c || " ()/<=>?@[]{}".toList.contains c

/-- `Morsel._reserved`: names a cookie may not have. -/
def cookieReserved : List String :=
  ["expires", "path", "comment", "domain", "max-age", "secure", "httponly", "version", "samesite", "partitioned"]

/-- A name `SimpleCookie` accepts: legal characters, at least one, and not
an attribute name (any case). -/
def isCookieKey (k : String) : Bool :=
  !k.toList.isEmpty && k.toList.all isCookieLegal && !cookieReserved.contains (lowerAscii k)

/-- Three octal digits. -/
def octal3 (n : Nat) : List Char := [digitChar (n / 64 % 8), digitChar (n / 8 % 8), digitChar (n % 8)]

/-- `_Translator`: one character inside quotes. -/
def cookieEscape (c : Char) : List Char :=
  if c = '"' then ['\\', '"']
  else if c = '\\' then ['\\', '\\']
  else if c.toNat < 256 && !isCookieUnescaped c then '\\' :: octal3 c.toNat
  else [c]

/-- `http.cookies._quote` on characters. -/
def cookieQuoteChars (v : List Char) : List Char :=
  if !v.isEmpty && v.all isCookieLegal then v else '"' :: v.flatMap cookieEscape ++ ['"']

/-- `http.cookies._quote`. -/
def cookieQuote (v : String) : String := String.ofList (cookieQuoteChars v.toList)

def isOct (c : Char) : Bool := '0' ≤ c && c ≤ '7'

/-- `_unquote`'s substitution `\\(?:([0-3][0-7][0-7])|(.))`, left to
right: three octal digits are a character, a backslash before any other
character but a newline is dropped, anything else is kept. -/
def unquoteBody : List Char → List Char
  | [] => []
  | '\\' :: t@(a :: rest) =>
    match h : rest with
    | b :: c :: r =>
      if '0' ≤ a && a ≤ '3' && isOct b && isOct c then
        Char.ofNat ((a.toNat - 48) * 64 + (b.toNat - 48) * 8 + (c.toNat - 48)) :: unquoteBody r
      else if a ≠ '\n' then a :: unquoteBody rest else '\\' :: unquoteBody t
    | _ => if a ≠ '\n' then a :: unquoteBody rest else '\\' :: unquoteBody t
  | x :: r => x :: unquoteBody r
termination_by s => s.length
decreasing_by all_goals simp_all <;> omega

/-- `http.cookies._unquote` on characters: a value in double quotes loses
them and its escapes; any other value is kept. -/
def cookieUnquoteChars (s : List Char) : List Char :=
  match s with
  | '"' :: t@(_ :: _) => if t.getLast? = some '"' then unquoteBody t.dropLast else s
  | _ => s

/-- Python's `str.strip()`. -/
def pyStrip (s : List Char) : List Char :=
  ((s.dropWhile PyRe.isSpace).reverse.dropWhile PyRe.isSpace).reverse

/-- `d[k] = v` on a `dict` kept as a list. -/
def dictSet (d : List (String × String)) (k v : String) : List (String × String) :=
  if d.any (·.1 == k) then d.map (fun p => if p.1 == k then (p.1, v) else p) else d ++ [(k, v)]

/-- One `;`-separated piece of a `Cookie` header. -/
def cookieChunk (d : List (String × String)) (chunk : List Char) : List (String × String) :=
  let (k, v) := match splitFirst '=' chunk with
    | (k, some v) => (k, v)
    | (c, none) => ([], c)
  let k := pyStrip k
  let v := pyStrip v
  if k.isEmpty && v.isEmpty then d else dictSet d (String.ofList k) (String.ofList (cookieUnquoteChars v))

/-- **`cookie_parser(cookie_string)`**. -/
def cookieParser (s : String) : List (String × String) :=
  (splitAll ';' s.toList).foldl cookieChunk []

/-- `request.cookies`: the first `Cookie` header, parsed. -/
def Request.cookies (r : Request) : List (String × String) :=
  match r.headers.get? "cookie" with
  | some c => cookieParser c
  | none => []

/-- A `Cookie` request header carrying name–value pairs, values quoted as
`set_cookie` sends them: what a browser sends back. -/
def cookieHeader : List (String × String) → String
  | [] => ""
  | [(k, v)] => k ++ "=" ++ cookieQuote v
  | (k, v) :: rest => k ++ "=" ++ cookieQuote v ++ "; " ++ cookieHeader rest

/-- `samesite`. -/
inductive SameSite where
  | lax
  | strict
  | none
  deriving DecidableEq, Repr

def SameSite.str : SameSite → String
  | .lax => "lax"
  | .strict => "strict"
  | .none => "none"

/-- `expires`: a date (a `datetime`, as Unix seconds) or a text sent as is. -/
inductive CookieExpires where
  | date (unixSeconds : Int)
  | text (s : String)
  deriving DecidableEq, Repr

/-- The `Set-Cookie` value `set_cookie` sends. -/
def setCookieLine (key value : String) (max_age : Option Int) (expires : Option CookieExpires)
    (path domain : Option String) (secure httponly : Bool) (samesite : Option SameSite) (partitioned : Bool) :
    String :=
  let nonEmpty (name : String) (v : String) : Option String := if v.isEmpty then none else some (name ++ "=" ++ v)
  let attrs : List (Option String) := [
    domain.bind (nonEmpty "Domain"),
    expires.bind (fun | .text s => nonEmpty "expires" s | .date t => some ("expires=" ++ formatHttpDate t)),
    if httponly then some "HttpOnly" else none,
    max_age.map (fun n => "Max-Age=" ++ toString n),
    if partitioned then some "Partitioned" else none,
    path.bind (nonEmpty "Path"),
    samesite.map (fun s => "SameSite=" ++ s.str),
    if secure then some "Secure" else none]
  "; ".intercalate ((key ++ "=" ++ cookieQuote value) :: attrs.filterMap id)

/-- **`response.set_cookie(key, value="", max_age=None, expires=None,
path="/", domain=None, secure=False, httponly=False, samesite="lax",
partitioned=False)`**: appends a `Set-Cookie` header. The name is checked
where upstream's `SimpleCookie` raises `CookieError`. -/
def Response.set_cookie (r : Response) (key : String) (value : String := "") (max_age : Option Int := none)
    (expires : Option CookieExpires := none) (path : Option String := some "/") (domain : Option String := none)
    (secure : Bool := false) (httponly : Bool := false) (samesite : Option SameSite := some .lax)
    (partitioned : Bool := false) (_h : isCookieKey key = true := by decide +kernel) : Response :=
  let line := setCookieLine key value max_age expires path domain secure httponly samesite partitioned
  { r with headers := r.headers.append "set-cookie" line }

/-- **`response.delete_cookie(key, path="/", domain=None, secure=False,
httponly=False, samesite="lax", partitioned=False)`**: an empty value with
`Max-Age=0`, expired at the Unix epoch. -/
def Response.delete_cookie (r : Response) (key : String) (path : String := "/") (domain : Option String := none)
    (secure : Bool := false) (httponly : Bool := false) (samesite : Option SameSite := some .lax)
    (partitioned : Bool := false) (h : isCookieKey key = true := by decide +kernel) : Response :=
  r.set_cookie key "" (max_age := some 0) (expires := some (.date 0)) (path := some path) (domain := domain)
    (secure := secure) (httponly := httponly) (samesite := samesite) (partitioned := partitioned) h

/-! ## What a browser keeps (RFC 6265 §5.2, the part the theorems need) -/

/-- A browser's cookies for one site: names and raw values, in order. -/
abbrev CookieJar := List (String × String)

/-- A `Max-Age` value (RFC 6265 §5.2.2): an optional `-` and digits. -/
def maxAgeValue? : List Char → Option Int
  | '-' :: ds => if !ds.isEmpty && ds.all isDigitChar then some (-(ofDigits ds : Int)) else none
  | ds => if !ds.isEmpty && ds.all isDigitChar then some (ofDigits ds) else none

/-- Whether an attribute is `Max-Age` of zero or less. -/
def maxAgeExpired (a : List Char) : Bool :=
  match splitFirst '=' (pyStrip a) with
  | (n, some val) => n.map asciiLower == "max-age".toList && ((maxAgeValue? val).map (fun i => decide (i ≤ 0))).getD false
  | _ => false

/-- Receive one `Set-Cookie` value: the name and value before the first
`;` (split at the first `=`, stripped); a `Max-Age` of zero or less
removes the cookie, anything else stores the value. -/
def CookieJar.receive (jar : CookieJar) (line : String) : CookieJar :=
  match splitAll ';' line.toList with
  | [] => jar
  | first :: attrs =>
    match splitFirst '=' first with
    | (_, none) => jar
    | (k, some v) =>
      let k := String.ofList (pyStrip k)
      let expired := attrs.any maxAgeExpired
      let jar := jar.filter (·.1 != k)
      if expired then jar else jar ++ [(k, String.ofList (pyStrip v))]

/-- Receive every `Set-Cookie` header of a response, in order. -/
def CookieJar.receiveAll (jar : CookieJar) (r : Response) : CookieJar :=
  (r.headers.raw.filter (·.1 == "set-cookie")).foldl (fun j p => j.receive p.2) jar

end LeanStarlette
