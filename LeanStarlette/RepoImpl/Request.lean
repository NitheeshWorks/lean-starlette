import LeanStarlette.RepoImpl.Headers
import LeanStarlette.RepoImpl.Encoding

/-!
# RepoImpl: query parameters, URLs and the request

* `QueryParams.parse` is `parse_qsl(qs, keep_blank_values=True)`, and
  `toString` is `urlencode`. Lookup is last-wins, like the `dict` Starlette
  builds; `getlist` keeps every value.
* `URL` is `urllib.parse.SplitResult` with Starlette's `URL(scope=...)`
  construction (`Host` header first, then the server address).
* The `Request` accessors are Starlette's properties, Lean-cased, with the
  Python spellings beside them.
-/

namespace LeanStarlette

/-! ## Query parameters -/

namespace QueryParams

/-- One `name=value` field, `+` and `%XX` decoded; a field without `=` has
an empty value (`keep_blank_values=True`). -/
def parseField (f : List Char) : String × String :=
  match splitFirst '=' f with
  | (k, none) => (unquotePlus (String.ofList k), "")
  | (k, some v) => (unquotePlus (String.ofList k), unquotePlus (String.ofList v))

/-- `QueryParams("a=1&b=2")`: split on `&`, skip empty fields. -/
def parse (qs : String) : QueryParams :=
  ⟨((splitAll '&' qs.toList).filter (!·.isEmpty)).map parseField⟩

/-- `params[key]` / `params.get(key)`: the last value, like a `dict`. -/
def get? (q : QueryParams) (key : String) : Option String :=
  (q.items.reverse.find? (·.1 == key)).map (·.2)

/-- `params.getlist(key)`. -/
def getlist (q : QueryParams) (key : String) : List String :=
  (q.items.filter (·.1 == key)).map (·.2)

/-- `params.keys()`: each key once, in first-seen order. -/
def keys (q : QueryParams) : List String := dedup (q.items.map (·.1))

/-- `params.multi_items()`. -/
def multiItems (q : QueryParams) : List (String × String) := q.items

/-- `key in params`. -/
def contains (q : QueryParams) (key : String) : Bool := q.items.any (·.1 == key)

/-- `str(params)`: `urlencode`. -/
instance : ToString QueryParams where
  toString q := "&".intercalate (q.items.map fun p => quotePlus p.1 ++ "=" ++ quotePlus p.2)

instance : GetElem? QueryParams String String (fun q k => (q.get? k).isSome) where
  getElem q k ok := (q.get? k).get ok
  getElem? q k := q.get? k

end QueryParams

/-! ## URLs -/

/-- A URL, split as `urllib.parse.urlsplit` splits it. -/
structure URL where
  scheme : String := ""
  netloc : String := ""
  path : String := ""
  query : String := ""
  fragment : String := ""
  deriving BEq, Repr, Inhabited

namespace URL

/-- `geturl()` / `str(url)`. -/
def toStr (u : URL) : String :=
  let base := if u.netloc.isEmpty then u.path
    else "//" ++ u.netloc ++ (if u.path.isEmpty || u.path.startsWith "/" then u.path else "/" ++ u.path)
  let s := if u.scheme.isEmpty then base else u.scheme ++ ":" ++ base
  let s := if u.query.isEmpty then s else s ++ "?" ++ u.query
  if u.fragment.isEmpty then s else s ++ "#" ++ u.fragment

instance : ToString URL := ⟨toStr⟩

/-- `[a-zA-Z][a-zA-Z0-9+.-]*` -/
def isSchemeChars : List Char → Bool
  | [] => false
  | c :: cs => (('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')) &&
      cs.all fun c => ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || isDigitChar c || c = '+' || c = '.' || c = '-'

/-- `urlsplit(s)`. -/
def parse (s : String) : URL :=
  let cs := s.toList
  let (scheme, rest) := match splitFirst ':' cs with
    | (sch, some r) => if isSchemeChars sch then (String.ofList (sch.map asciiLower), r) else ("", cs)
    | _ => ("", cs)
  let (netloc, rest) := match rest with
    | '/' :: '/' :: r =>
      let n := r.takeWhile (fun c => c ≠ '/' && c ≠ '?' && c ≠ '#')
      (String.ofList n, r.drop n.length)
    | r => ("", r)
  let (rest, fragment) := match splitFirst '#' rest with
    | (a, some f) => (a, String.ofList f)
    | (a, none) => (a, "")
  let (path, query) := match splitFirst '?' rest with
    | (a, some q) => (String.ofList a, String.ofList q)
    | (a, none) => (String.ofList a, "")
  { scheme, netloc, path, query, fragment }

/-- `url.is_secure`. -/
def isSecure (u : URL) : Bool := u.scheme == "https" || u.scheme == "wss"

/-- `url.hostname`: the host, lower-cased, without user info, port or brackets. -/
def hostname (u : URL) : Option String :=
  let hostport := match splitFirst '@' u.netloc.toList.reverse with
    | (h, some _) => h.reverse
    | (h, none) => h.reverse
  let host := match hostport with
    | '[' :: r => r.takeWhile (· ≠ ']')
    | r => (splitFirst ':' r).1
  if u.netloc.isEmpty then none else some (String.ofList (host.map asciiLower))

/-- `url.replace(path=...)` and friends. -/
def replacePath (u : URL) (path : String) : URL := { u with path }
def replaceQuery (u : URL) (query : String) : URL := { u with query }

/-- `url.include_query_params(**kwargs)`. -/
def includeQueryParams (u : URL) (kv : List (String × String)) : URL :=
  let q := QueryParams.parse u.query
  let keep := q.items.filter fun p => !(kv.any (·.1 == p.1))
  { u with query := toString (QueryParams.mk (keep ++ kv)) }

/-- `url.replace_query_params(**kwargs)`. -/
def replaceQueryParams (u : URL) (kv : List (String × String)) : URL :=
  { u with query := toString (QueryParams.mk kv) }

/-- `url.remove_query_params(keys)`. -/
def removeQueryParams (u : URL) (keys : List String) : URL :=
  let q := QueryParams.parse u.query
  { u with query := toString (QueryParams.mk (q.items.filter fun p => !keys.contains p.1)) }

end URL

/-- A path as `url_path_for` returns it (`URLPath`): the path, with `\` and a
leading `//` escaped, and the protocol of the route (`http`, `websocket`, or
empty for a mount). -/
structure URLPath where
  path : String
  protocol : String := ""
  deriving BEq, Repr

namespace URLPath

/-- `URLPath(path, protocol)`: escape what would change the URL's meaning. -/
def ofPath (path : String) (protocol : String := "") : URLPath :=
  let p := String.ofList (path.toList.flatMap fun c => if c = '\\' then "%5C".toList else [c])
  let p := match p.toList with
    | '/' :: '/' :: r => "/%2F" ++ String.ofList r
    | _ => p
  ⟨p, protocol⟩

instance : ToString URLPath := ⟨URLPath.path⟩

/-- `make_absolute_url(base_url)`. -/
def makeAbsoluteURL (p : URLPath) (base : URL) : URL :=
  let scheme :=
    if p.protocol == "http" then (if base.isSecure then "https" else "http")
    else if p.protocol == "websocket" then (if base.isSecure then "wss" else "ws")
    else base.scheme
  let basePath := String.ofList (base.path.toList.reverse.dropWhile (· = '/')).reverse
  { scheme, netloc := base.netloc, path := basePath ++ p.path }

end URLPath

/-! ## The Host header -/

/-- `[a-z0-9._~%!$&'()*+,;=-]` (any case): a reg-name or IPv4 host. -/
def isHostChar (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || isDigitChar c || "._~%!$&'()*+,;=-".toList.contains c

/-- `parse_host_header`: `(host, port?)` for a well-formed `Host` value. An
IP literal keeps its brackets; it is checked for its character set only
(see `CONTRIBUTING.md`). -/
def parseHostHeader (v : String) : Option (String × Option String) :=
  let cs := v.toList
  let (host, rest) := match cs with
    | '[' :: r =>
      match splitFirst ']' r with
      | (inner, some after) =>
        if !inner.isEmpty && inner.all (fun c => isHexChar c || c = ':' || c = '.' || c = 'v' || isHostChar c)
        then (some ('[' :: inner ++ [']']), after) else (none, [])
      | _ => (none, [])
    | _ =>
      let h := cs.takeWhile (· ≠ ':')
      (if !h.isEmpty && h.all isHostChar then some h else none, cs.drop h.length)
  match host with
  | none => none
  | some h =>
    match rest with
    | [] => some (String.ofList h, none)
    | ':' :: p => if !p.isEmpty && p.all isDigitChar then some (String.ofList h, some (String.ofList p)) else none
    | _ => none

/-- `ParsedHost.is_valid_port`. -/
def isValidPort : Option String → Bool
  | none => true
  | some p => (p.toList.dropWhile (· = '0')).length ≤ 5 && (ofDigits p.toList ≤ 65535)

/-! ## The request -/

namespace PathParams

/-- `request.path_params[name]`. -/
def get? (ps : PathParams) (name : String) : Option PathParam := ps.items.lookup name

instance : GetElem? PathParams String PathParam (fun ps k => (ps.get? k).isSome) where
  getElem ps k ok := (ps.get? k).get ok
  getElem? ps k := ps.get? k

/-- The names. -/
def keys (ps : PathParams) : List String := ps.items.map (·.1)

end PathParams

instance : ToString PathParam := ⟨PathParam.text⟩

/-- A path parameter in a JSON response: a number for `int` and `float`
(as Python's `json.dumps` writes the converted value), else a string. -/
instance : LeanJson.IntoJson PathParam where
  intoJson p :=
    if p.convertor == "int" || p.convertor == "float" then
      match LeanJson.parseStr p.text with
      | .ok v => v.val
      | .error _ => .str p.text
    else .str p.text

namespace Request

/-- `request.query_params`. -/
def queryParams (r : Request) : QueryParams := QueryParams.parse r.query_string
abbrev query_params := @queryParams

/-- `request.path_params`. -/
def pathParams (r : Request) : PathParams := r.path_params

/-- `get_route_path(scope)`: the path with `root_path` removed. -/
def routePath (r : Request) : String :=
  if r.root_path.isEmpty then r.path
  else if !r.path.startsWith r.root_path then r.path
  else if r.path == r.root_path then ""
  else if (r.path.drop r.root_path.length).startsWith "/" then (r.path.drop r.root_path.length).toString
  else r.path

/-- The server address as an authority, default port elided. -/
def serverNetloc (r : Request) : Option String :=
  r.server.map fun (host, port) =>
    let host := if host.contains ':' && !host.startsWith "[" then "[" ++ host ++ "]" else host
    let default := if r.scheme == "https" || r.scheme == "wss" then 443 else 80
    if port == default then host else host ++ ":" ++ toString port

/-- The authority Starlette puts in `request.url`: the `Host` header when
it is valid, else the server address. -/
def netloc (r : Request) : Option String :=
  match (r.headers.get? "host").bind parseHostHeader with
  | some (h, p) =>
    if isValidPort p then some (match p with | none => h | some p => h ++ ":" ++ p)
    else r.serverNetloc
  | none => r.serverNetloc

/-- `request.url` (`URL(scope=scope)`). -/
def url (r : Request) : URL :=
  let path := String.ofList (r.path.toList.flatMap fun c =>
    if c = '?' then "%3F".toList else if c = '#' then "%23".toList else if c = '\\' then "%5C".toList else [c])
  match r.netloc with
  | some n => { scheme := r.scheme, netloc := n, path, query := r.query_string }
  | none =>
    let path := match path.toList with
      | '/' :: '/' :: rest => "/%2F" ++ String.ofList rest
      | _ => path
    { path, query := r.query_string }

/-- `request.base_url`: the root of the application. -/
def baseURL (r : Request) : URL :=
  let root := if r.root_path.endsWith "/" then r.root_path else r.root_path ++ "/"
  url { r with path := root, query_string := "", root_path := r.root_path }
abbrev base_url := @baseURL

/-- `request.client`. -/
def clientOf (r : Request) : Option (String × Nat) := r.client

/-- `await request.body()`. -/
def body (r : Request) : AppM ByteArray := pure r.bodyBytes

/-- The body parsed as JSON, or the parse error (lean-json's error, which
also reports nesting beyond its depth limit). -/
def json? (r : Request) : Except LeanJson.JsonError LeanJson.Json :=
  (LeanJson.from_json r.bodyBytes).map (·.val)

/-- `await request.json()`. A body that is not JSON is a `400 Bad Request`
(`HTTPException`), not a crash: upstream lets `json.loads` raise, which
becomes a 500, and a deeply nested body there is a `RecursionError`. -/
def json (r : Request) : AppM LeanJson.Json :=
  match r.json? with
  | .ok v => pure v
  | .error e => throw (.http 400 s!"Invalid JSON: {e.description}" [] (by decide))

/-- `request.url_for(name, **path_params)`: the absolute URL of a named
route, or `none` (upstream `NoMatchFound`). -/
def urlFor (r : Request) (name : String) (params : List (String × String) := []) : Option URL :=
  (r.urlPathFor name params).map fun (path, protocol) =>
    (URLPath.ofPath path protocol).makeAbsoluteURL r.baseURL
abbrev url_for := @urlFor

end Request

end LeanStarlette
