import LeanStarlette
import LeanStarlette.RepoImpl.Deflate

/-!
# Large JSON body, end to end

`lake build bench && /usr/bin/time -v .lake/build/bin/bench [array|object] [MB]`
sends one `POST` with a JSON body of about `MB` megabytes through
`Application.exchange` (Std.Http's parser and writer over its in-memory
connection), the app calls `request.json()` and answers with the element count.
Peak memory (maximum resident set size) is recorded in CONTRIBUTING.md.
-/

open LeanStarlette LeanJson

def countApp : Application := Starlette (routes := [
  Route "/" (fun (r : Request) => do
    let j ← r.json
    let n := match j with
      | .arr xs => xs.size
      | .obj kvs => kvs.size
      | _ => 0
    return JSONResponse (json% {"n": n})) (methods := ["POST"])])

/-- About `mb` megabytes of JSON: `[0,1,2,...]` or `{"k0":0,"k1":1,...}`. -/
def bigBody (shape : String) (mb : Nat) : ByteArray := Id.run do
  let target := mb * 1000 * 1000
  let mut out := ByteArray.emptyWithCapacity (target + 64)
  out := out.push (if shape == "object" then 123 else 91)
  let mut i := 0
  while out.size < target do
    if i > 0 then out := out.push 44
    let item := if shape == "object" then s!"\"k{i}\":{i}" else toString i
    out := out ++ item.toUTF8
    i := i + 1
  out := out.push (if shape == "object" then 125 else 93)
  return out

def numApp : Application := Starlette (routes := [
  Route "/i/{n:int}" (fun (r : Request) => PlainTextResponse (toString (toString r.pathParams["n"]!).length)),
  Route "/f/{x:float}" (fun (r : Request) => PlainTextResponse (toString (toString r.pathParams["x"]!).length))])

def rangeKind {n : Nat} : RangeDecision n → String
  | .full => "full" | .ranges _ => "ranges" | .malformed m => s!"malformed ({m})" | .unsatisfiable => "unsatisfiable"

def timeIt (label : String) (act : Unit → IO String) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let out ← act ()
  let t1 ← IO.monoNanosNow
  IO.println s!"{label}: {out} in {(t1 - t0) / 1000} µs"

/-- Numeric parses of attacker input at 8 KiB and 64 KiB of digits. -/
def digits : IO Unit := do
  for n in [8192, 65536] do
    let ds := String.ofList (List.replicate n '7')
    timeIt s!"Range bytes=N-, {n} digits" fun _ => (pure (rangeKind (parseRangeHeader s!"bytes={ds}-" 1000)))
    timeIt s!"Range bytes=0-N, {n} digits" fun _ => (pure (rangeKind (parseRangeHeader s!"bytes=0-{ds}" 1000)))
    timeIt s!"If-Modified-Since year of {n} digits" fun _ => (pure (toString (parseHttpDate s!"Sun, 06 Nov {ds} 08:49:37 GMT").isSome))
    timeIt s!"Host port of {n} digits" fun _ => (pure (toString (isValidPort (some ds))))
    timeIt s!"Keel.Codec.digitsValue, {n} digits" fun _ => pure (toString (Keel.Codec.digitsValue ds.toList % 10))
    let big := Keel.Codec.digitsValue ds.toList
    timeIt s!"Keel.Codec.decimal, {n} digits" fun _ => pure (toString (Keel.Codec.decimal big).length)
    timeIt s!"Nat.repr, {n} digits" fun _ => pure (toString (Nat.repr big).length)
    for (route, label) in [(s!"/i/{ds}", "int"), (s!"/f/{ds}.5", "float")] do
      timeIt s!"{label} path convertor, {n} digits" fun _ => do
        let r ← numApp.call { path := route }
        pure s!"{r.status_code}"
    timeIt s!"JSON integer of {n} digits" fun _ => (pure (match LeanJson.from_json ds.toUTF8 with | .ok _ => "ok" | .error e => s!"error {repr e.kind}"))

def splitApp : Application := Starlette (routes := [
  Route "/s/{a}/x" (fun (_ : Request) => PlainTextResponse "x"),
  Route "/t/{a}/{b}" (fun (_ : Request) => PlainTextResponse "t"),
  Route "/p/{a:path}/end" (fun (_ : Request) => PlainTextResponse "p"),
  Route "/u/{a}-{b}" (fun (_ : Request) => PlainTextResponse "u")])

/-- Long paths against templates with several captures. -/
def paths : IO Unit := do
  for n in [8192, 65000] do
    let a := String.ofList (List.replicate n 'a')
    for (path, label) in [(s!"/s/{a}/x", "/s/{a}/x"), (s!"/s/{a}", "/s/{a}/x, no match"),
        (s!"/t/{a}/b", "/t/{a}/{b}"), (s!"/p/{a}/end", "/p/{a:path}/end"), (s!"/p/{a}", "/p/{a:path}/end, no match"),
        (s!"/u/{a}", "/u/{a}-{b}, no match"), (s!"/u/{a}-b", "/u/{a}-{b}")] do
      timeIt s!"{label}, {n} chars" fun _ => do
        let r ← splitApp.call { path := path }
        pure s!"{r.status_code}"

/-- Serve a file of `mb` megabytes over TCP and download it with curl: peak
memory should not grow with the file (it is sent in 64 KiB chunks). -/
def fileBench (mb : Nat) : IO Unit := do
  let dir ← IO.FS.createTempDir
  let path := dir / "big.bin"
  IO.FS.withFile path .write fun h => do
    let chunk := ByteArray.mk (Array.replicate (1024 * 1024) 120)
    for _ in [0:mb] do h.write chunk
  let app := Starlette (routes := [Route "/big" (fun (_ : Request) => FileResponse path.toString)])
  let _ ← IO.asTask (app.run (port := 18741)) .dedicated
  IO.sleep 500
  let t0 ← IO.monoMsNow
  let out ← IO.Process.output { cmd := "curl", args := #["-s", "-o", "/dev/null", "-w", "%{http_code} %{size_download}", "http://127.0.0.1:18741/big"] }
  IO.println s!"file {mb} MB over TCP: {out.stdout} in {(← IO.monoMsNow) - t0} ms"
  IO.FS.removeDirAll dir
  IO.Process.exit 0

/-- lean-multipart's Starlette parsers alone, on the bodies the form limits stop. -/
def formParse : IO Unit := do
  let big := ByteArray.mk (Array.replicate (1024 * 1024 + 1) 120)
  let lim : LeanMultipart.FormLimits := {}
  for (label, body, ct) in [("urlencoded a=<1 MiB + 1>", "a=".toUTF8 ++ big, none),
      ("urlencoded <1 MiB + 1>=1", big ++ "=1".toUTF8, none),
      ("urlencoded 200k fields", (String.intercalate "&" (List.replicate 200000 "a=1")).toUTF8, none),
      ("multipart <1 MiB + 1> text part", "--B\r\nContent-Disposition: form-data; name=\"f\"\r\n\r\n".toUTF8 ++ big ++ "\r\n--B--\r\n".toUTF8, some "multipart/form-data; boundary=B")] do
    let t0 ← IO.monoNanosNow
    let r : Except LeanMultipart.LimitError Nat := match ct with
      | none => (LeanMultipart.API.Starlette.parseUrlencoded lim body).map fun (fs : {fs : List LeanMultipart.QsField // _}) => fs.val.length
      | some c => (LeanMultipart.API.Starlette.parseMultipartForm lim c.toUTF8 body).map fun (ps : {ps : List LeanMultipart.StarlettePart // _}) => ps.val.length
    let t1 ← IO.monoNanosNow
    IO.println s!"{label}: {match r with | .ok n => s!"ok {n}" | .error e => s!"error {repr e}"} in {(t1 - t0) / 1000} µs"

/-- Decode a chunked body of `mb` MiB in 64 KiB chunks (or 1 KiB with
`small`) with lean-httpx's verified codec. -/
def chunkDecode (mb : Nat) (chunk : Nat) : IO Unit := do
  let data := (List.range (mb * 1024 * 1024 / chunk)).map fun _ => ByteArray.mk (Array.replicate chunk 120)
  let enc := LeanHttpx.H1.encodeChunked data
  let t0 ← IO.monoMsNow
  let r := LeanHttpx.H1.decodeChunked enc
  let n := match r with | some (cs, _) => (LeanHttpx.H1.concatChunks cs).size | none => 0
  IO.println s!"decodeChunked {enc.size} bytes in {chunk}-byte chunks: {n} in {(← IO.monoMsNow) - t0} ms"

/-- Peak resident memory of this process, in KB (`VmHWM`). -/
def peakKB : IO Nat := do
  let s ← IO.FS.readFile "/proc/self/status"
  for line in s.splitOn "\n" do
    if line.startsWith "VmHWM:" then
      return ((line.drop 6).trimAscii.toString.takeWhile Char.isDigit).toNat!
  return 0

def mib : Nat := 1024 * 1024

/-- `n` bytes of `x`, built in place (no boxed array on the way). -/
def xBytes (n : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity n
  for _ in [0:n] do b := b.push 120
  return b

def mpPart (name : String) (value : ByteArray) (filename : Option String := none) : ByteArray :=
  let disp := s!"form-data; name=\"{name}\"" ++ (filename.map (s!"; filename=\"{·}\"")).getD ""
  s!"--B\r\nContent-Disposition: {disp}\r\n\r\n".toUTF8 ++ value ++ "\r\n".toUTF8

def repeatB (b : ByteArray) (n : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (b.size * n)
  for _ in [0:n] do out := out ++ b
  return out

/-- The chunked pipeline's stages on `mb` MiB in 64 KiB chunks, timed apart. -/
def chunkPipe (mb : Nat) : IO Unit := do
  let data := (List.range (mb * 16)).map fun _ => xBytes 65536
  let enc := LeanHttpx.H1.encodeChunked data
  let pieces := (List.range ((enc.size + 65535) / 65536)).toArray.map fun i => enc.extract (i * 65536) ((i + 1) * 65536)
  let t0 ← IO.monoMsNow
  let mut st : ChunkScan := .sizeLine .empty
  let mut got := 0
  for p in pieces do
    let (s', g') := st.feed p got (1 <<< 30)
    st := s'; got := g'
  let t1 ← IO.monoMsNow
  let raw := joinChunks "H".toUTF8 pieces
  let t2 ← IO.monoMsNow
  let some (out, _) := decodeChunkedBody raw 1 (ByteArray.emptyWithCapacity (got + 1) ++ "H".toUTF8)
    | IO.println "decode failed"
  let t3 ← IO.monoMsNow
  IO.println s!"{enc.size} bytes, {pieces.size} pieces: feed {t1 - t0} ms, join raw {t2 - t1} ms, decode into the output {t3 - t2} ms ({out.size} bytes; got {got}, done {match st with | .done _ => true | _ => false})"

/-- `n` MiB of `x`, as pieces written one at a time. -/
def xPieces (n : Nat) : List (Unit → ByteArray) := List.replicate n fun _ => xBytes mib

/-- A multipart part's head (`--B`, its `Content-Disposition`, the blank line). -/
def mpHeadB (name : String) (filename : Option String := none) : ByteArray :=
  let p := mpPart name .empty filename
  p.extract 0 (p.size - 2)

/-- Hostile form bodies, end to end over TCP (an in-process server, curl
uploading from a file): each is `(name, content type, body pieces, expected
status, time bound ms, peak bound MB)`. The body file is written a piece at
a time, so the peak is the server's own (the bench process at rest is about
20 MB). Cases named `chunked…` are sent with `Transfer-Encoding: chunked`
(curl's 64 KiB chunks); their bounds are three times uvicorn 0.54 +
Starlette 1.8.0 on the same request (20 MB: 0.09-0.10 s, peak 76 MB; 50 MB
multipart file: 0.26-0.31 s, peak 127 MB), the others about twice Lean's
measured cost with headroom for CI. -/
def formCases : List (String × String × List (Unit → ByteArray) × String × Nat × Nat) := [
  ("url200k", "application/x-www-form-urlencoded",
    [fun _ => "a=1".toUTF8 ++ repeatB "&a=1".toUTF8 199999], "400", 200, 150),
  ("urlValue20m", "application/x-www-form-urlencoded",
    (fun _ => "a=".toUTF8) :: xPieces 20, "400", 800, 300),
  ("mpValue20m", "multipart/form-data; boundary=B",
    (fun _ => mpHeadB "f") :: xPieces 20 ++ [fun _ => "\r\n--B--\r\n".toUTF8], "400", 800, 300),
  ("mpFields50k", "multipart/form-data; boundary=B",
    [fun _ => repeatB (mpPart "f" "v".toUTF8) 50000 ++ "--B--\r\n".toUTF8], "400", 300, 150),
  ("mpFile50m", "multipart/form-data; boundary=B",
    (fun _ => mpHeadB "f" (some "big.bin")) :: xPieces 50 ++ [fun _ => "\r\n--B--\r\n".toUTF8], "200", 2000, 700),
  ("chunked20m", "application/octet-stream", xPieces 20, "200", 300, 228),
  ("expectMpFile10m", "multipart/form-data; boundary=B",
    (fun _ => mpHeadB "f" (some "big.bin")) :: xPieces 10 ++ [fun _ => "\r\n--B--\r\n".toUTF8], "200", 200, 250),
  ("chunkedMpFile50m", "multipart/form-data; boundary=B",
    (fun _ => mpHeadB "f" (some "big.bin")) :: xPieces 50 ++ [fun _ => "\r\n--B--\r\n".toUTF8], "200", 780, 381)]

def formSizeApp : Application := Starlette (routes := [Route "/" (fun (r : Request) => do
    let data ← r.form
    let mut n := 0
    for (_, v) in data.multi_items do
      if let .file f := v then n := n + (← (f.read : IO ByteArray)).size
    return PlainTextResponse (toString n) : Request → AppM Response) (methods := ["POST"])])

def nullApp : Application := Starlette (routes := [Route "/" (fun (r : Request) =>
    PlainTextResponse (toString r.bodyBytes.size)) (methods := ["POST"])])

/-- One hostile form case; exits 1 when a bound is exceeded. `name!` runs the
same body through an app that ignores it (the transport's share). -/
def formMem (name0 : String) : IO UInt32 := do
  let null := name0.endsWith "!"
  let name := if null then (name0.dropEnd 1).toString else name0
  let some (_, ct, mk, want, msBound, mbBound) := formCases.find? (·.1 == name)
    | IO.println s!"unknown case {name}"; return 2
  let dir ← IO.FS.createTempDir
  let path := dir / "body.bin"
  let size ← IO.FS.withFile path .write fun h => do
    let mut n := 0
    for piece in mk do
      let b := piece ()
      h.write b
      n := n + b.size
    return n
  let port : Nat := 18751
  let _ ← IO.asTask ((if null then nullApp else formSizeApp).run (port := port)) .dedicated
  IO.sleep 300
  let base ← peakKB
  let t0 ← IO.monoMsNow
  let chunked := name.startsWith "chunked"
  let te := if chunked then #["-H", "Transfer-Encoding: chunked"] else #[]
  -- `expect…` cases keep curl's `Expect: 100-continue` (sent for bodies over 1 MiB)
  let expect := if name.startsWith "expect" then #[] else #["-H", "Expect:"]
  let res ← IO.Process.output { cmd := "curl", args := #["-s", "-i", "-X", "POST", "-H", s!"content-type: {ct}"] ++ expect ++ te ++
    #["--data-binary", s!"@{path}", s!"http://127.0.0.1:{port}/"] }
  let ms := (← IO.monoMsNow) - t0
  IO.FS.removeDirAll dir
  let out := res.stdout.toUTF8
  let body : ByteArray := .empty
  let _ := body
  let peak ← peakKB
  let text := (String.fromUTF8? out).getD ""
  -- the final response's status (after any `100 Continue`)
  let status := (((text.splitOn "HTTP/1.1 ").getLastD "").splitOn " ").headD ""
  IO.println s!"RESULT {name} size={size} status={status} ms={ms} peakMB={peak / 1024} (before the request {base / 1024} MB; bounds {msBound} ms, {mbBound} MB)"
  let mut ok := true
  if status != want then IO.println s!"  FAIL status {status}, want {want}"; ok := false
  if ms > msBound then IO.println s!"  FAIL time {ms} ms > {msBound} ms"; ok := false
  if peak > mbBound * 1024 then IO.println s!"  FAIL memory {peak / 1024} MB > {mbBound} MB"; ok := false
  return if ok then 0 else 1

/-- Plain `Std.Http.Server.serve` reading a POST body with `readAll`: the
toolchain's own upload speed, for comparison with `Application.run`. -/
def plainUpload (mb : Nat) : IO Unit := do
  let dir ← IO.FS.createTempDir
  let path := dir / "body.bin"
  IO.FS.writeBinFile path (xBytes (mb * mib))
  let handler : Std.Http.Server.StatelessHandler := Std.Http.Server.Handler.ofFn fun req => do
    let body : ByteArray ← req.body.readAll
    toHttpResponse (PlainTextResponse (toString body.size))
  let addr : Std.Net.SocketAddress := .v4 ⟨(Std.Net.IPv4Addr.ofString "127.0.0.1").get!, 18752⟩
  let _ ← IO.asTask (Std.Async.Async.block do
    let _ ← Std.Http.Server.serve addr handler
    Std.Async.sleep 600000) .dedicated
  IO.sleep 300
  let t0 ← IO.monoMsNow
  let res ← IO.Process.output { cmd := "curl", args := #["-s", "-X", "POST", "-H", "Expect:",
    "--data-binary", s!"@{path}", "http://127.0.0.1:18752/"] }
  IO.println s!"plain Std.Http, {mb} MB upload: {res.stdout} in {(← IO.monoMsNow) - t0} ms"
  IO.FS.removeDirAll dir
  IO.Process.exit 0

def gzText (n : Nat) : ByteArray := Id.run do
  let words : Array ByteArray := #["starlette ", "lean ", "middleware ", "gzip ", "the ", "a ", "response ", "body ",
    "\n", "{\"k\": 12345} "].map String.toUTF8
  let mut b := ByteArray.emptyWithCapacity (n + 16)
  let mut x := 12345
  for _ in [0:n] do
    if b.size ≥ n then break
    x := (x * 1103515245 + 12345) % 2147483648
    let w := words[x % 10]!
    for k in [0:w.size] do b := b.push w[k]!
  return b.extract 0 n

def gzRand (n : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity n
  let mut x := 7
  for _ in [0:n] do
    x := (x * 6364136223846793005 + 1442695040888963407) % 18446744073709551616
    b := b.push (x / 72057594037927936).toUInt8
  return b
/-- Compress inputs, check them through lean-httpx's gunzip and write them to `dir` for zlib. -/
def gzipTest (dir : String) : IO Unit := do
  let cases : List (String × ByteArray) := [("empty", .empty), ("a", "a".toUTF8), ("text1k", gzText 1000), ("text1m", gzText 1000000),
    ("zeros20m", ⟨Array.replicate 20000000 0⟩), ("rand200k", gzRand 200000), ("text10m", gzText 10000000)]
  for (name, src) in cases do
    let t0 ← IO.monoMsNow
    let z := LeanStarlette.Deflate.gzip src
    let t1 ← IO.monoMsNow
    let back := LeanHttpx.Decoders.gunzip z
    let ok := match back with | .ok b => b == src | .error _ => false
    IO.println s!"{name}: {src.size} -> {z.size} in {t1 - t0} ms, httpx gunzip ok {ok}"
    (← IO.getStdout).flush
    IO.FS.writeBinFile s!"{dir}/gz-{name}.gz" z
    IO.FS.writeBinFile s!"{dir}/gz-{name}.raw" src
  -- sync-flushed pieces concatenate
  let a := gzText 70000; let b := gzText 5000
  let z := LeanStarlette.Deflate.gzipHeader ++ LeanStarlette.Deflate.deflate a false ++ LeanStarlette.Deflate.deflate b true ++
    LeanStarlette.Deflate.gzipTrailer (LeanStarlette.Deflate.crc32Update (LeanStarlette.Deflate.crc32Update 0 a) b) (a.size + b.size)
  IO.FS.writeBinFile (dir ++ "/gz-pieces.gz") z
  IO.FS.writeBinFile (dir ++ "/gz-pieces.raw") (a ++ b)
  IO.println s!"pieces httpx ok {match LeanHttpx.Decoders.gunzip z with | .ok x => x == a ++ b | .error _ => false}"

/-- Time the compressor's parts on one input. -/
def gzParts : IO Unit := do
  for (name, src) in [("rand200k", gzRand 200000), ("text1m", gzText 1000000), ("zeros20m", (⟨Array.replicate 20000000 0⟩ : ByteArray))] do
    let t0 ← IO.monoNanosNow
    let crc := LeanStarlette.Deflate.crc32Update 0 src
    let t1 ← IO.monoNanosNow
    let (toks, _) := LeanStarlette.Deflate.tokenize {} src 0 (min src.size 65535)
    let t2 ← IO.monoNanosNow
    let bits := toks.foldl (fun a t => a + LeanStarlette.Deflate.tokenBits t) 0
    let t3 ← IO.monoNanosNow
    let w := toks.foldl LeanStarlette.Deflate.putToken { out := .empty }
    let t4 ← IO.monoNanosNow
    let t5 ← IO.monoNanosNow
    let c := (({} : LeanStarlette.Deflate.Chains).insertRun src (min src.size 65535) 0)
    let t6 ← IO.monoNanosNow
    let mut acc := 0
    for i in [0:min src.size 65535] do
      acc := acc + c.best src i (min src.size 65535) / 65536
    let t7 ← IO.monoNanosNow
    IO.println s!"  inserts {c.head.size} {(t6 - t5) / 1000} us; best x64K on full chains {acc} {(t7 - t6) / 1000} us"
    IO.println s!"{name}: crc {crc} {(t1 - t0) / 1000} us (all); first 64K: tokenize {toks.size} {(t2 - t1) / 1000} us, bits {bits} {(t3 - t2) / 1000} us, put {w.out.size} {(t4 - t3) / 1000} us"

/-! ## m5: hostile inputs to cookies, CORS and GZip, against twice Starlette

`tests/golden/m5-bench-starlette-1.8.0.json` holds Starlette 1.8.0's warm
best-of-5 times on the same inputs (`tests/golden/record_m5_bench.py`
builds them from the same recipes); each case here is the best of 5 after a
first run, and fails above twice upstream. -/

def m5Golden : IO Json := do
  let t ← IO.FS.readBinFile "tests/golden/m5-bench-starlette-1.8.0.json"
  match LeanJson.from_json t with
  | .ok j => pure j.val
  | .error _ => throw (IO.userError "m5 golden: bad JSON")

/-- A golden time in microseconds. -/
def goldenUs (j : Json) : Nat :=
  let t := String.fromUTF8! (LeanJson.to_json j).val
  match t.splitOn "." with
  | [i] => i.toNat! * 1000
  | i :: f :: _ => i.toNat! * 1000 + ((f ++ "000").toList.take 3).foldl (fun a c => a * 10 + (c.toNat - 48)) 0
  | [] => 0

/-- Best of 5 after a first run, in microseconds, and the last result. -/
def bestOf5 {α : Type} (act : Unit → IO α) : IO (Nat × α) := do
  let mut r ← act ()
  let mut best := 1000000000000
  for _ in [0:5] do
    let t0 ← IO.monoNanosNow
    r ← act ()
    let t1 ← IO.monoNanosNow
    best := min best ((t1 - t0) / 1000)
  return (best, r)

/-- Inputs are functions, so they are not built when the bench starts. -/
def cookieInputs (_ : Unit) : List (String × String) := [
  ("distinct70k", "; ".intercalate ((List.range 70000).map fun i => s!"k{i}=v{i}")),
  ("dup100k", "; ".intercalate (List.replicate 100000 "a=1")),
  ("quoted50k", "; ".intercalate ((List.range 50000).map fun i => s!"k{i}=\"v\\073{i}\""))]

def benchOrigins (_ : Unit) : List String := (List.range 10000).map fun i => s!"https://o{i}.example.com"

def corsBenchApp (_ : Unit) : Application := Starlette (routes := [Route "/" (fun (_ : Request) => PlainTextResponse "x")])
  (middleware := [Middleware CORSMiddleware (allow_origins := benchOrigins ()) (allow_methods := ["GET"])
    (allow_headers := ["X-A"])])

def corsInputs : List (String × Request) := [
  ("preflightMiss", { method := "OPTIONS", headers := Headers.ofList [("host", "example.org"),
      ("origin", "https://evil.example.net"), ("access-control-request-method", "GET")] }),
  ("simpleLast", { headers := Headers.ofList [("host", "example.org"), ("origin", "https://o9999.example.com")] })]

/-- `n` zero bytes, built in place. -/
def zeroBytes (n : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity n
  for _ in [0:n] do b := b.push 0
  return b

def gzipInputs (_ : Unit) : List (String × ByteArray) :=
  [("text10m", gzText 10000000), ("zeros20m", zeroBytes 20000000), ("rand2m", gzRand 2000000)]

/-- Report one case against twice upstream; `true` when it holds. -/
def m5Check (group name : String) (us upUs : Nat) (detail : String) (ok : Bool) : IO Bool := do
  let held := ok && us ≤ 2 * upUs
  IO.println s!"RESULT {group}/{name}: {us / 1000}.{toString (us % 1000 + 1000) |>.drop 1} ms (upstream {upUs / 1000}.{toString (upUs % 1000 + 1000) |>.drop 1} ms, bound {2 * upUs / 1000} ms) {detail}{if held then "" else "  FAIL"}"
  (← IO.getStdout).flush
  return held

def m5Bench (only : String) : IO UInt32 := do
  let g ← m5Golden
  let up (group name : String) : Option Json := (g.getObjVal? group).bind (·.getObjVal? name)
  let mut ok := true
  if only == "" || only == "cookie" then
    for (name, s) in cookieInputs () do
      let some e := up "cookie" name | IO.println s!"no golden for cookie/{name}"; return 2
      let want := ((e.getObjVal? "names").bind Json.getInt?).getD (-1)
      let (us, n) ← bestOf5 fun _ => pure (cookieParser s).length
      ok := (← m5Check "cookie" name us (goldenUs ((e.getObjVal? "upstream_warm_ms").getD .null))
        s!"{n} names" (n == want.toNat)) && ok
  if only == "" || only == "cors" then
    let app := corsBenchApp ()
    for (name, req) in corsInputs do
      let some e := up "cors" name | IO.println s!"no golden for cors/{name}"; return 2
      let want := ((e.getObjVal? "status").bind Json.getInt?).getD (-1)
      let (us, st) ← bestOf5 fun _ => do
        let mut st := 0
        for _ in [0:1000] do st := (← app.call req).status_code
        pure st
      ok := (← m5Check "cors" name us (goldenUs ((e.getObjVal? "upstream_warm_ms").getD .null))
        s!"1000 requests, status {st}" (st == want.toNat)) && ok
  if only == "" || only == "gzip" then
    let port : Nat := 18761
    let inputs := gzipInputs ()
    let app := Starlette (routes := inputs.map fun (n, b) =>
        Route s!"/{n}" (fun (_ : Request) => Response b (media_type := some "text/plain")))
      (middleware := [Middleware GZipMiddleware (minimum_size := 500) (compresslevel := 9)])
    let _ ← IO.asTask (app.run (port := port)) .dedicated
    IO.sleep 300
    for (name, body) in inputs do
      let some e := up "gzip" name | IO.println s!"no golden for gzip/{name}"; return 2
      let dir ← IO.FS.createTempDir
      let path := dir / "body.gz"
      let (us, out) ← bestOf5 fun _ => IO.Process.output { cmd := "curl", args := #["-s", "-H", "Accept-Encoding: gzip",
        "-o", path.toString, "-w", "%{http_code} %{size_download}", s!"http://127.0.0.1:{port}/{name}"] }
      let z ← IO.FS.readBinFile path
      IO.FS.removeDirAll dir
      let back := match LeanHttpx.Decoders.gunzip z with | .ok b => b == body | .error _ => false
      ok := (← m5Check "gzip" name us (goldenUs ((e.getObjVal? "upstream_warm_ms").getD .null))
        s!"{out.stdout} (upstream {((e.getObjVal? "compressed").bind Json.getInt?).getD 0} bytes), gunzip {back}, peak {(← peakKB) / 1024} MB"
        (out.stdout.startsWith "200" && back)) && ok
  return if ok then 0 else 1

/-- The whole compressor and its CRC on the m5 inputs. -/
def gzFull : IO Unit := do
  for (name, src) in gzipInputs () do
    let (crcUs, crc) ← bestOf5 fun _ => pure (LeanStarlette.Deflate.crc32Update 0 src)
    let (us, z) ← bestOf5 fun _ => pure (LeanStarlette.Deflate.gzip src)
    IO.println s!"{name}: gzip {src.size} -> {z.size} in {us / 1000} ms; crc {crc} in {crcUs / 1000} ms"

def main (args : List String) : IO Unit := do
  if args.headD "" == "gzfull" then gzFull; return
  if args.headD "" == "m5bench" then IO.Process.exit (← m5Bench (args.getD 1 "")).toUInt8
  if args.headD "" == "plainupload" then plainUpload ((args.getD 1 "20").toNat!)
  if args.headD "" == "formmem" then IO.Process.exit (← formMem (args.getD 1 "")).toUInt8
  if args.headD "" == "formparse" then formParse; return
  if args.headD "" == "chunkpipe" then chunkPipe ((args.getD 1 "50").toNat!); return
  if args.headD "" == "chunkdecode" then chunkDecode ((args.getD 1 "20").toNat!) ((args.getD 2 "65536").toNat!); return
  if args.headD "" == "file" then fileBench ((args.getD 1 "100").toNat!)
  if args.headD "" == "paths" then paths; return
  if args.headD "" == "gziptest" then gzipTest (args.getD 1 "."); return
  if args.headD "" == "gzparts" then gzParts; return
  if args.headD "" == "digits" then digits; return
  let shape := args.headD "array"
  let mb := (args.getD 1 "20").toNat!
  let body := bigBody shape mb
  if args.getD 2 "" == "parse" then
    let t0 ← IO.monoMsNow
    let r := LeanJson.from_json body
    let n := match r with
      | .ok j => (match j.val with | .arr xs => xs.size | .obj kvs => kvs.size | _ => 0)
      | .error _ => 0
    IO.println s!"from_json only, {shape}, {body.size} bytes: {n} in {(← IO.monoMsNow) - t0} ms"
    return
  let head := s!"POST / HTTP/1.1\r\nHost: x\r\nContent-Type: application/json\r\nContent-Length: {body.size}\r\nConnection: close\r\n\r\n"
  let t0 ← IO.monoMsNow
  let out ← countApp.exchange (head.toUTF8 ++ body)
  let t1 ← IO.monoMsNow
  let text := String.fromUTF8? out |>.getD ""
  IO.println s!"{shape}, {body.size} bytes: {(text.splitOn "\r\n").headD ""} {(text.splitOn "\r\n\r\n").getLastD ""} in {t1 - t0} ms"
