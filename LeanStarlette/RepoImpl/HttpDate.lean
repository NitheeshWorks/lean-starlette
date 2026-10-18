import Keel.Codec
import LeanStarlette.RepoImpl.Text

/-!
# RepoImpl: HTTP dates

`email.utils.formatdate(t, usegmt=True)` for `Last-Modified`, and
`email.utils.parsedate` for comparing `If-Modified-Since` with it. Starlette
compares the parsed tuples `(year, month, day, hour, minute, second)`
directly, ignoring any zone; so does `HttpDate`'s order.

The calendar is the proleptic Gregorian one (Howard Hinnant's
`civil_from_days`), with integer arithmetic only.
-/

namespace LeanStarlette

/-- A broken-down UTC time: `(year, month, day, hour, minute, second)`. -/
structure HttpDate where
  year : Int
  month : Nat
  day : Nat
  hour : Nat
  minute : Nat
  second : Nat
  deriving BEq, Repr, DecidableEq

/-- Lexicographic `<` on equal-length tuples. -/
def lexLt : List Int → List Int → Bool
  | a :: as, b :: bs => a < b || (a == b && lexLt as bs)
  | _, _ => false

/-- The fields as a tuple. -/
def HttpDate.fields (d : HttpDate) : List Int := [d.year, d.month, d.day, d.hour, d.minute, d.second]

/-- `d₁ ≥ d₂` as Python compares the tuples. -/
def HttpDate.ge (a b : HttpDate) : Bool := !lexLt a.fields b.fields

/-- The civil date of a day number (days since 1970-01-01). -/
def civilFromDays (z : Int) : Int × Nat × Nat :=
  let z := z + 719468
  let era := (if z ≥ 0 then z else z - 146096) / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let y := yoe + era * 400
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  ((if m ≤ 2 then y + 1 else y), m.toNat, d.toNat)

/-- The day number of a civil date. -/
def daysFromCivil (y : Int) (m d : Nat) : Int :=
  let y := if m ≤ 2 then y - 1 else y
  let era := (if y ≥ 0 then y else y - 399) / 400
  let yoe := y - era * 400
  let mp : Int := if m > 2 then m - 3 else m + 9
  let doy := (153 * mp + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe - 719468

/-- The UTC broken-down time of a Unix timestamp. -/
def HttpDate.ofUnix (t : Int) : HttpDate :=
  let days := (if t ≥ 0 then t else t - 86399) / 86400
  let secs := (t - days * 86400).toNat
  let (y, m, d) := civilFromDays days
  { year := y, month := m, day := d, hour := secs / 3600, minute := secs / 60 % 60, second := secs % 60 }

def weekdays : List String := ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"]
def monthNames : List String := ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"]

def pad2 (n : Nat) : String := if n < 10 then "0" ++ toString n else toString n

/-- `formatdate(t, usegmt=True)`: `Wed, 18 Oct 2023 10:00:00 GMT`. -/
def formatHttpDate (t : Int) : String :=
  let d := HttpDate.ofUnix t
  let days := (if t ≥ 0 then t else t - 86399) / 86400
  -- 1970-01-01 was a Thursday
  let wd := ((days + 3) % 7).toNat
  s!"{weekdays[wd]!}, {pad2 d.day} {monthNames[d.month - 1]!} {d.year} {pad2 d.hour}:{pad2 d.minute}:{pad2 d.second} GMT"

/-- A decimal number, under `int()`'s digit limit (`parsedate` returns
`None` when `int()` raises). Linear in `s`. -/
def natOf? (s : List Char) : Option Nat :=
  if !s.isEmpty && s.all Char.isDigit then boundedDigits? s else none

/-- `parsedate(s)` for the date forms HTTP uses: `Wed, 18 Oct 2023 10:00:00
GMT` (IMF-fixdate, the weekday optional) and `Wed Oct 18 10:00:00 2023`
(asctime). -/
def parseHttpDate (s : String) : Option HttpDate :=
  let words := (splitAll ' ' (s.toList.map fun c => if c = ',' || c = '\t' then ' ' else c)).filter (!·.isEmpty)
  let words := match words with
    | w :: rest => if weekdays.contains (String.ofList w) then rest else w :: rest
    | [] => []
  let month? (w : List Char) : Option Nat :=
    (monthNames.findIdx? (· == String.ofList w)).map (· + 1)
  let time? (w : List Char) : Option (Nat × Nat × Nat) :=
    match splitAll ':' w with
    | [h, m, sec] => do pure (← natOf? h, ← natOf? m, ← natOf? sec)
    | [h, m] => do pure (← natOf? h, ← natOf? m, 0)
    | _ => none
  let build (y : Nat) (mo d : Nat) (t : Nat × Nat × Nat) : Option HttpDate :=
    let y : Nat := if y < 50 then y + 2000 else if y < 100 then y + 1900 else y
    if 1 ≤ d && d ≤ 31 && t.1 ≤ 24 && t.2.1 ≤ 59 && t.2.2 ≤ 61 then
      some { year := y, month := mo, day := d, hour := t.1, minute := t.2.1, second := t.2.2 }
    else none
  match words with
  | d :: mo :: y :: t :: _ =>
    match natOf? d, month? mo, natOf? y, time? t with
    | some d, some mo, some y, some t => build y mo d t
    | _, _, _, _ =>
      -- asctime: `Oct 18 10:00:00 2023`
      match month? d, natOf? mo, time? y, natOf? t with
      | some mo, some dd, some tt, some yy => build yy mo dd tt
      | _, _, _, _ => none
  | _ => none

end LeanStarlette
