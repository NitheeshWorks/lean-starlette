import LeanStarlette

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

def main (args : List String) : IO Unit := do
  if args.headD "" == "file" then fileBench ((args.getD 1 "100").toNat!)
  if args.headD "" == "paths" then paths; return
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
