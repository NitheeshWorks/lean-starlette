import LeanStarlette

/-!
# Framing conformance: raw bytes against uvicorn (`tests/golden/record_framing.py`)

`tests/golden/framing-uvicorn-0.54.jsonl` holds what uvicorn 0.54 (h11 0.16)
serving Starlette 1.8.0 sent for each scenario: the bytes of each step on one
connection (until 300 ms of silence or the close), and whether the connection
was closed at the end. `framingApp` is the recorder's app in Lean; it is
served by `Application.run` with `serverName := "uvicorn"`, so the bytes
compare equal but for the masked `date` value.
-/

namespace FramingCases

open LeanStarlette LeanJson Std.Async Std.Async.TCP

def framingApp : Application := Starlette (routes := [
  Route "/200" (fun (_ : Request) => PlainTextResponse "hello"),
  Route "/204" (fun (_ : Request) => Response (status_code := 204)),
  Route "/304" (fun (_ : Request) => Response (status_code := 304)),
  Route "/422" (fun (_ : Request) => JSONResponse (json% {"detail": "bad"}) (status_code := 422)),
  Route "/201" (fun (_ : Request) => JSONResponse (json% {"a": 1}) (status_code := 201)),
  Route "/500" (fun (_ : Request) => (throw (.custom "RuntimeError" "boom" .null) : AppM Response)),
  Route "/stream" (fun (_ : Request) => StreamingResponse (fun send => do
    send "one".toUTF8; send .empty; send "two".toUTF8) (media_type := some "text/plain")),
  Route "/echo" (fun (r : Request) =>
    PlainTextResponse s!"{r.bodyBytes.size}:{latin1Decode (r.bodyBytes.extract 0 20)}") (methods := ["POST"]),
  Route "/headers" (fun (_ : Request) => PlainTextResponse "h" (headers := [("X-Custom", "1"), ("set-cookie", "a=b")]))])

def framingPort : Nat := 18771

/-- The server for the replay: uvicorn's `server` value and keep-alive timeout. -/
def framingConfig : Std.Http.Config :=
  { serverName := some (.ofString! "uvicorn"), keepAliveTimeout := ⟨5000, by decide⟩ }

/-- `date: <value>` lines masked, as the recorder does. -/
def mask (s : String) : String :=
  "\r\n".intercalate ((s.splitOn "\r\n").map fun l =>
    if (lowerAscii l).startsWith "date: " then (l.take 6).toString ++ "<date>" else l)

/-- Read until `idle` ms pass with nothing, or the peer closes (`true`). -/
def readIdle (c : Socket.Client) (idle : Nat) : Async (ByteArray × Bool) := do
  let rec go (acc : ByteArray) : Nat → Async (ByteArray × Bool)
    | 0 => pure (acc, false)
    | n + 1 => do
      let deadline ← Selector.sleep (.ofNat idle)
      let r ← Selectable.one #[
        .case (c.recvSelector 65536) (fun x => pure (some x)),
        .case deadline (fun _ => pure none)]
      match r with
      | none => pure (acc, false)
      | some none => pure (acc, true)
      | some (some d) => if d.size == 0 then pure (acc, true) else go (acc ++ d) n
  go .empty 100000

/-- Run one scenario's steps on one connection. -/
def runSteps (port : Nat) (steps : List String) : IO (List String × Bool) := Async.block do
  let c ← (Socket.Client.mk : IO Socket.Client)
  c.connect (.v4 ⟨(Std.Net.IPv4Addr.ofString "127.0.0.1").get!, port.toUInt16⟩)
  let mut got : List String := []
  let mut closed := false
  for step in steps do
    c.sendAll #[⟨(step.toList.map fun ch => ch.toNat.toUInt8).toArray⟩]
    let (d, cl) ← readIdle c 300
    got := got ++ [mask (latin1Decode d)]
    closed := cl
    if cl then break
  if !closed then
    let (_, cl) ← readIdle c 300
    closed := cl
  try c.shutdown catch _ => pure ()
  return (got, closed)

def strs (j : Option Json) : List String :=
  match j with
  | some (.arr xs) => xs.toList.filterMap Json.getStr?
  | _ => []

/-- One case per golden scenario. -/
def framingCases : IO (List (String × String × IO Bool)) := do
  let lines ← IO.FS.lines "tests/golden/framing-uvicorn-0.54.jsonl"
  return lines.toList.filterMap fun l => (from_json l).toOption.bind fun j => do
    let j := j.val
    let name ← (j.getObjVal? "name").bind Json.getStr?
    let steps := strs (j.getObjVal? "steps")
    let want := strs (j.getObjVal? "received")
    let wantClosed ← (j.getObjVal? "closed").bind Json.getBool?
    pure ("uvicorn 0.54 (h11) + Starlette 1.8.0, raw bytes (golden) [socket]", s!"framing: {name}", do
      let (got, closed) ← runSteps framingPort steps
      let good := got == want && closed == wantClosed
      unless good do
        IO.println s!"      closed {closed}, want {wantClosed}"
        for (g, w) in got.zip (want ++ List.replicate 5 "") do
          if g != w then
            IO.println s!"      got  {g.quote}"
            IO.println s!"      want {w.quote}"
      pure good)

end FramingCases
