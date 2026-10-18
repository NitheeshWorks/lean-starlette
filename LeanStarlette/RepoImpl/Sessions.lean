import LeanStarlette.RepoImpl.Cookies
import LeanStarlette.RepoImpl.Middleware
import LeanItsdangerous
import LeanHttpx.RepoImpl.Base64

/-!
# RepoImpl: sessions (`starlette/middleware/sessions.py`)

The session is a JSON object carried in a signed cookie:
`TimestampSigner(secret_key).sign(b64encode(json.dumps(session)))`.
`encodeSession` builds the cookie value, `decodeSession` reads it back
(`session_sign_verify`: within `max_age` it is the same object).

`SessionMiddleware` gives the application `request.session` (an
`IO.Ref SessionState`) and, after the response, sets the cookie when the
session was changed and is not empty, or clears it when it was changed to
empty from a loaded one, and adds `Vary: Cookie` when the session was read.

The cookie is read as bytes by Latin-1, where upstream encodes the text as
UTF-8: a signed value is ASCII, so a value with any other character fails
the signature either way (one beyond U+00FF is refused here before it).
-/

namespace LeanStarlette

open LeanJson LeanItsdangerous

/-- Characters as bytes (Latin-1), when every one is below U+0100. -/
def latin1Bytes? (s : List Char) : Option Bytes :=
  if s.all (·.toNat < 256) then some (s.map (·.toNat.toUInt8)) else none

/-- Bytes as characters (Latin-1). -/
def latin1Chars (b : Bytes) : List Char := b.map fun x => Char.ofNat x.toNat

/-- `json.dumps(session)`: `", "` and `": "`, non-ASCII escaped. -/
def sessionPrintOpts : PrintOpts := { ensureAscii := true, spaced := true }

/-- The base64 text of the session's JSON. -/
def sessionPayload (d : Array (String × Json)) : List Char :=
  LeanHttpx.Base64.encodeList (LeanJson.print (.obj d) sessionPrintOpts).val.data.toList

/-- **The session cookie's value**: the signed base64 of the JSON, signed
at `now`. -/
def encodeSession (t : TimestampSigner) (d : Array (String × Json)) (now : UInt64) : String :=
  String.ofList (latin1Chars (t.sign ((sessionPayload d).map (·.toNat.toUInt8)) now))

/-- What a session cookie loads to. -/
inductive SessionLoad where
  /-- No valid signature, or expired: an empty session (`BadSignature`). -/
  | invalid
  /-- The session. -/
  | loaded (d : Array (String × Json))
  /-- Validly signed but not base64 JSON of an object: upstream raises
  (only someone with the key can make one). -/
  | broken (why : String)

/-- **Load a session cookie** at `now`. -/
def decodeSession (t : TimestampSigner) (maxAge : Option Nat) (now : UInt64) (cookie : String) : SessionLoad :=
  match latin1Bytes? cookie.toList with
  | none => .invalid
  | some bs =>
    match (t.unsign bs maxAge now).val with
    | .error _ => .invalid
    | .ok (payload, _) =>
      match LeanHttpx.Base64.decodeList (latin1Chars payload) with
      | none => .broken "binascii.Error: invalid base64 in a signed session"
      | some raw =>
        match parseDocument ⟨raw.toArray⟩ with
        | .ok (.obj d) => .loaded d
        | .ok _ => .broken "the signed session is not a JSON object"
        | .error _ => .broken "json.JSONDecodeError in a signed session"

/-- The wall clock, in Unix seconds. -/
def unixNow : IO UInt64 := do
  let t ← Std.Time.Timestamp.now
  pure t.toSecondsSinceUnixEpoch.val.toNat.toUInt64

/-- `SessionMiddleware`'s cookie attributes after the value. -/
def sessionFlags (same_site : SameSite) (https_only : Bool) (domain : Option String) (partitioned : Bool) :
    String :=
  "httponly; samesite=" ++ same_site.str ++ (if https_only then "; secure" else "") ++
    (match domain with | some d => "; domain=" ++ d | none => "") ++ (if partitioned then "; partitioned" else "")

/-- The headers `SessionMiddleware` sends after the application ran. -/
def sessionResponseHeaders (t : TimestampSigner) (session_cookie : String) (max_age : Option Nat) (path flags : String)
    (initialEmpty : Bool) (s : SessionState) (now : UInt64) (h : Headers) : Headers :=
  let h := if s.accessed then addVary h "Cookie" else h
  if s.modified && !s.data.isEmpty then
    let maxAge := match max_age with | some m => s!"Max-Age={m}; " | none => ""
    h.append "set-cookie" s!"{session_cookie}={encodeSession t s.data now}; path={path}; {maxAge}{flags}"
  else if s.modified && !initialEmpty then
    h.append "set-cookie" s!"{session_cookie}=null; path={path}; expires=Thu, 01 Jan 1970 00:00:00 GMT; {flags}"
  else h

/-- **`SessionMiddleware(app, secret_key, session_cookie="session",
max_age=14 * 24 * 60 * 60, path="/", same_site="lax", https_only=False,
domain=None, partitioned=False)`**. `now` is the clock (the wall clock by
default). -/
def SessionMiddleware (secret_key : String) (session_cookie : String := "session")
    (max_age : Option Nat := some (14 * 24 * 60 * 60)) (path : String := "/") (same_site : SameSite := .lax)
    (https_only : Bool := false) (domain : Option String := none) (partitioned : Bool := false)
    (now : IO UInt64 := unixNow) : Middleware :=
  let t := TimestampSigner.new secret_key
  let flags := sessionFlags same_site https_only domain partitioned
  fun app req => do
    let clock ← liftM now
    let (initial, initialEmpty) ← match req.cookies.lookup session_cookie with
      | some c => match decodeSession t max_age clock c with
        | .loaded d => pure (d, false)
        | .invalid => pure (#[], true)
        | .broken why => throw (.custom "ValueError" why .null)
      | none => pure (#[], true)
    let ref ← liftM (IO.mkRef ({ data := initial } : SessionState))
    let resp ← app { req with session? := some ref }
    let s ← liftM (ref.get : IO SessionState)
    let clock ← liftM now
    return { resp with headers := sessionResponseHeaders t session_cookie max_age path flags initialEmpty s clock resp.headers }

/-! ## `request.session` -/

/-- `request.session` without `SessionMiddleware`: upstream's assertion. -/
def noSession : Exception :=
  .custom "AssertionError" "SessionMiddleware must be installed to access request.session" .null

/-- The session, marked read. -/
def Request.sessionRef (r : Request) : AppM (IO.Ref SessionState) := do
  match r.session? with
  | some ref => liftM (ref.modify (fun s => { s with accessed := true }) : IO Unit); pure ref
  | none => throw noSession

/-- `request.session`: the session's items, in order. -/
def Request.session (r : Request) : AppM (Array (String × Json)) := do
  let ref ← r.sessionRef
  return (← liftM (ref.get : IO SessionState)).data

/-- `request.session.get(key)`. -/
def Request.sessionGet (r : Request) (key : String) : AppM (Option Json) := do
  return ((← r.session).find? (·.1 == key)).map (·.2)

/-- `request.session[key] = value`. -/
def Request.sessionSet (r : Request) (key : String) (value : Json) : AppM Unit := do
  let ref ← r.sessionRef
  liftM (ref.modify (fun s =>
    let data := if s.data.any (·.1 == key) then s.data.map (fun p => if p.1 == key then (key, value) else p)
      else s.data.push (key, value)
    { s with data, modified := true }) : IO Unit)

/-- `request.session.pop(key, None)`. -/
def Request.sessionPop (r : Request) (key : String) : AppM (Option Json) := do
  let ref ← r.sessionRef
  let s ← liftM (ref.get : IO SessionState)
  match s.data.find? (·.1 == key) with
  | some (_, v) =>
    liftM (ref.set { s with data := s.data.filter (·.1 != key), modified := true } : IO Unit)
    return some v
  | none => return none

/-- `request.session.clear()`. -/
def Request.sessionClear (r : Request) : AppM Unit := do
  let ref ← r.sessionRef
  liftM (ref.modify (fun s => { s with data := #[], modified := true }) : IO Unit)

/-- `request.session.update(items)`. -/
def Request.sessionUpdate (r : Request) (items : List (String × Json)) : AppM Unit := do
  let ref ← r.sessionRef
  liftM (ref.modify (fun s => { s with modified := true }) : IO Unit)
  for (k, v) in items do r.sessionSet k v

end LeanStarlette
