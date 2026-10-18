import LeanStarlette

/-!
# Property tests: fast feedback where there is no proof

Generates values with a seeded generator and checks the properties that are
tested rather than proved. Not a substitute for the theorems; the check that
runs in under a second so a mistake surfaces while the change is still in
your head.

Run with `lake exe props`, or a different seed with `lake exe props 12345`.
A failure prints the seed and the value, so it reproduces exactly.
-/

/-- xorshift64*: four lines, no dependency, deterministic from the seed. -/
structure Rng where
  s : UInt64
  deriving Inhabited

def Rng.next (r : Rng) : UInt64 × Rng :=
  let x := r.s
  let x := x ^^^ (x >>> 12)
  let x := x ^^^ (x <<< 25)
  let x := x ^^^ (x >>> 27)
  (x * 2685821657736338717, { s := x })

def Rng.nat (r : Rng) (bound : Nat) : Nat × Rng :=
  let (v, r) := r.next
  (if bound == 0 then 0 else v.toNat % bound, r)

/-- A property: a name and a check that, given a generator, either passes or
returns a description of the failing value. -/
structure Property where
  name : String
  check : Rng → Option String × Rng

open LeanStarlette

/-- A character from a pool that exercises escaping: letters, digits,
delimiters, `%`, `+`, space, and multi-byte characters. -/
def pool : List Char := "aZ09-._~ /?#&=+%:@!$'()*,;é€😀\\\"".toList

def Rng.char (r : Rng) : Char × Rng :=
  let (i, r) := r.nat pool.length
  (pool[i]!, r)

def Rng.string (r : Rng) (maxLen : Nat := 12) : String × Rng := Id.run do
  let (n, r0) := r.nat (maxLen + 1)
  let mut r := r0
  let mut cs : List Char := []
  for _ in [0:n] do
    let (c, r') := r.char
    r := r'
    cs := c :: cs
  return (String.ofList cs, r)

/-- A string of letters and digits only (one path segment). -/
def Rng.word (r : Rng) : String × Rng := Id.run do
  let (n, r0) := r.nat 8
  let mut r := r0
  let mut cs : List Char := ['w']
  for _ in [0:n] do
    let (i, r') := r.nat 36
    r := r'
    cs := (if i < 10 then Char.ofNat (48 + i) else Char.ofNat (87 + i)) :: cs
  return (String.ofList cs, r)

def check (name : String) (ok : Bool) (why : Unit → String) : Option String :=
  if ok then none else some s!"{name}: {why ()}"

def wordApp : Application := Router [Route "/users/{username}" (fun (r : Request) =>
  PlainTextResponse (toString r.pathParams["username"]!)) (name := "user"),
  Route "/n/{n:int}" (fun (r : Request) => PlainTextResponse (toString r.pathParams["n"]!)) (name := "n")]

def respWith (i : Nat) (s : String) : Response :=
  match i with
  | 0 => PlainTextResponse s
  | 1 => PlainTextResponse s (status_code := 201)
  | 2 => PlainTextResponse s (status_code := 204)
  | 3 => PlainTextResponse s (status_code := 304)
  | 4 => PlainTextResponse s (status_code := 101)
  | _ => PlainTextResponse s (status_code := 500)

def randFields (r : Rng) (maxN : Nat) : List (String × String) × Rng := Id.run do
  let (n, r0) := r.nat maxN
  let mut r := r0
  let mut items : List (String × String) := []
  for _ in [0:n] do
    let (k, r1) := r.string 6
    let (v, r2) := r1.string 6
    r := r2
    items := items ++ [(k, v)]
  return (items, r)

def urlBody (fs : List (String × String)) : ByteArray :=
  ("&".intercalate (fs.map fun (k, v) => quotePlus k ++ "=" ++ quotePlus v)).toUTF8

def formTexts (items : List (String × FormItem)) : List (String × String) :=
  items.filterMap fun (k, v) => match v with | .text s => some (k, s) | .file _ => none

def urlCt : Option String := some "application/x-www-form-urlencoded"

def properties : List Property := [
  ⟨"unquote (quote s) = s", fun r =>
    let (s, r) := r.string
    (check "quote" (unquote (quote s []) == s) (fun _ => s.quote), r)⟩,
  ⟨"unquote_plus (quote_plus s) = s", fun r =>
    let (s, r) := r.string
    (check "quote_plus" (unquotePlus (quotePlus s) == s) (fun _ => s.quote), r)⟩,
  ⟨"UTF-8 decoding agrees with String.fromUTF8? on valid input", fun r =>
    let (s, r) := r.string
    (check "utf8" (String.ofList (decodeUtf8 s.toUTF8.toList) == s) (fun _ => s.quote), r)⟩,
  ⟨"UTF-8 decoding with replacement is total and never longer than its input", fun r => Id.run do
    let (n, r0) := r.nat 12
    let mut r := r0
    let mut bs : List UInt8 := []
    for _ in [0:n] do
      let (b, r') := r.nat 256
      r := r'
      bs := UInt8.ofNat b :: bs
    return (check "utf8-replace" ((decodeUtf8 bs).length ≤ bs.length) (fun _ => toString bs), r)⟩,
  ⟨"QueryParams.parse (str q) = q", fun r => Id.run do
    let (n, r0) := r.nat 4
    let mut r := r0
    let mut items : List (String × String) := []
    for _ in [0:n] do
      let (k, r1) := r.string 6
      let (v, r2) := r1.string 6
      r := r2
      items := items ++ [(k, v)]
    let q : QueryParams := ⟨items⟩
    return (check "qs" (QueryParams.parse (toString q) == q) (fun _ => toString q), r)⟩,
  ⟨"headers[k] = v after headers[K] = v, any case", fun r =>
    let (k, r) := r.word
    let (v, r) := r.word
    let h := (Headers.ofList [("X-Other", "1"), (k, "old"), (k, "older")]).set (upperAscii k) v
    (check "headers" (h.get? k == some v && h.getlist k == [v] && h.get? "x-other" == some "1") (fun _ => k), r)⟩,
  ⟨"content-length is the body size, absent when the status forbids a body", fun r =>
    let (s, r) := r.string 20
    let (i, r) := r.nat 6
    let resp := respWith i s
    let status := resp.status_code
    let cl := resp.headers.get? "content-length"
    (check "cl" (if bodyAllowed status then cl == some (toString s.toUTF8.size) else cl == none && resp.body.size == 0)
      (fun _ => s!"{status} {s.quote}"), r)⟩,
  ⟨"routing then url_path_for round-trips a segment and an int", fun r =>
    let (w, r) := r.word
    let (n, r) := r.nat 100000
    let p1 := (wordApp.urlPathFor "user" [("username", w)]).map toString
    let p2 := (wordApp.urlPathFor "n" [("n", toString n)]).map toString
    (check "route" (p1 == some s!"/users/{w}" && p2 == some s!"/n/{n}") (fun _ => w), r)⟩,
  ⟨"an urlencoded form of quote_plus'd fields parses back to them", fun r =>
    let (fs, r) := randFields r 6
    let fs := fs.filter fun (k, v) => !(k.isEmpty && v.isEmpty)
    let got := (formItems {} urlCt (urlBody fs)).toOption.map formTexts
    (check "form-url" (got == some fs) (fun _ => toString fs), r)⟩,
  ⟨"an urlencoded form is accepted iff it has at most max_fields fields", fun r =>
    let (n, r) := r.nat 12
    let (m, r) := r.nat 12
    let body := ("&".intercalate ((List.range (n + 1)).map fun i => s!"f{i}=v")).toUTF8
    let ok := (formItems { maxFields := m } urlCt body).toBool
    (check "form-limit" (ok == decide (n + 1 ≤ m)) (fun _ => s!"{n + 1} fields, max {m}"), r)⟩,
  ⟨"FormData: get is the last of getlist, keys are distinct, len counts them", fun r =>
    let (fs, r) := randFields r 6
    let (k, r) := r.string 6
    let fd : FormData := { multiItems := fs.map fun (a, b) => (a, .text b) }
    let all := (fd.getlist k).filterMap (·.text?)
    let ok := ((fd.get? k).bind (·.text?)) == all.getLast? &&
      fd.keys.eraseDups == fd.keys && fd.length == (fs.map (·.1)).eraseDups.length &&
      fd.contains k == !all.isEmpty
    (check "formdata" ok (fun _ => toString fs), r)⟩,
  ⟨"TestClient: params lean-httpx encodes reach the app as Starlette's query_params (grouped by key, as httpx)", fun r =>
    let (fs, r) := randFields r 4
    let got := match LeanHttpx.URL.parse "http://testserver/p" with
      | .ok u => match LeanHttpx.Request.new "GET" u (params := some (LeanHttpx.QueryParams.ofList fs)) with
        | .ok req => some (scopeRequest "" ("testclient", 50000) req).queryParams.multiItems
        | .error _ => none
      | .error _ => none
    -- httpx's QueryParams groups a repeated key's values at its first position.
    let keys := fs.foldl (fun ks (k, _) => if ks.contains k then ks else ks ++ [k]) []
    let want := keys.flatMap fun k => fs.filter (·.1 == k)
    (check "tc-params" (got == some want) (fun _ => s!"{fs} got {got}"), r)⟩
]


def main (args : List String) : IO UInt32 := do
  let seed := (args.head? >>= String.toNat?).getD 88172645463325252
  let cases := 200
  let mut rng : Rng := { s := UInt64.ofNat seed }
  let mut failures := 0
  for p in properties do
    let mut failed : Option String := none
    for _ in [0:cases] do
      if failed.isSome then break
      let (res, rng') := p.check rng
      rng := rng'
      failed := res
    match failed with
    | none => IO.println s!"ok    {p.name} ({cases} cases)"
    | some why =>
      failures := failures + 1
      IO.println s!"FAIL  {p.name}: {why}  (seed {seed})"
  IO.println s!"{properties.length} properties, {failures} failing (seed {seed})"
  return if failures == 0 then 0 else 1
