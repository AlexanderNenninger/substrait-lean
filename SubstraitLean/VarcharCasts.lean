import Sverify.Core.Value
import Sverify.Core.Float
import Sverify.Core.Time

/-!
# Casts from VARCHAR: Lean's evaluators (#806)

The black boxes `varchar_bigint`, `varchar_double`, `varchar_boolean`,
`varchar_date`, `varchar_timestamp` and their `try_` rows
(`SubstraitLean/DuckDBBoxes.lean`) are DuckDB's `CAST` and `TRY_CAST` of a
string. No proof depends on what they compute. This file is how Lean runs
them, and it reads a string three ways:

* `val v`: a string of the subset below, with the value DuckDB gives it;
* `bad`: a string DuckDB rejects for sure (`CAST` raises, `TRY_CAST` is NULL);
* `unknown`: anything else. The evaluator panics there, and
  `substrait-check` refuses to print rows rather than print wrong ones.

The subset, after spaces at either end (DuckDB 2.0.0, probed;
`duckdb-cast-varchar`):

* numbers: `[+-]` digits, a fraction, an exponent (`1.5e-3`, `.5`, `5.`). A
  BIGINT rounds the exact decimal half away from zero and must fit 64 bits;
  a DOUBLE is the decimal correctly rounded (`1e400` is `+∞`, `1e-400` is
  `0`). Also `inf`, `infinity` and `nan` with a sign, any case, for a DOUBLE.
  Exponents of more than 40 digits' worth are `unknown`.
* booleans: `true t yes y 1` and `false f no n 0`, any case, nothing around.
* dates: `Y-M-D` (or with `/` or spaces), a year from 1 to 9999 (more is `unknown`: DuckDB's dates
  go further than the reference's), a month and day of one or two digits;
  `epoch`; a time after the date, as below, is dropped.
* timestamps: a date, then a space or `T` and `H:MM`, `H:MM:SS` or
  `H:MM:SS.f`, hours to 23; digits of a second past six are dropped, as
  DuckDB truncates them, and so is an offset (`Z`, `+HH`, `+HH:MM`).

A string is `bad` when it is empty, when it is of the subset's form but out
of range (a month 13, `2023-02-29`, a minute 60, a BIGINT beyond 64 bits),
or when it holds a character no form DuckDB reads has: for a number, one
other than digits, signs, points, spaces and `e`, where it is not `inf…` or
`nan…` (a double's), `0x…` or `0b…` (an integer's), and has no `(`, `_` or
tab; for a date, no digit or fewer than two separators, and not a word DuckDB
reads.
-/

namespace Substrait.VarcharCasts

/-- What Lean makes of a string DuckDB casts. -/
inductive Parsed where
  | val (v : Value)
  | bad
  | unknown
  deriving Repr, BEq, Inhabited

def trim (cs : List Char) : List Char :=
  ((cs.dropWhile (· == ' ')).reverse.dropWhile (· == ' ')).reverse

def digitsVal (ds : List Char) : Nat := ds.foldl (fun n c => n * 10 + (c.toNat - 48)) 0

def sign : List Char → Bool × List Char
  | '-' :: r => (true, r)
  | '+' :: r => (false, r)
  | r => (false, r)

/-- `[+-] digits [. digits] [(e|E) [+-] digits]`, with a digit before or
after the point: the sign, the digits as one integer, and the power of ten
it is scaled by. -/
def decimal? (cs : List Char) : Option (Bool × Nat × Int) :=
  let (neg, r) := sign cs
  let ip := r.takeWhile Char.isDigit
  let r := r.drop ip.length
  let (fd, r) := match r with
    | '.' :: r => let f := r.takeWhile Char.isDigit; (f, r.drop f.length)
    | r => ([], r)
  if ip.isEmpty && fd.isEmpty then none else
  let e : Option Int := match r with
    | [] => some 0
    | c :: r =>
      if c == 'e' || c == 'E' then
        let (eneg, ed) := sign r
        if ed.isEmpty || !ed.all Char.isDigit then none
        else some (if eneg then -(digitsVal ed : Int) else digitsVal ed)
      else none
  e.map fun e => (neg, digitsVal (ip ++ fd), e - fd.length)

#guard decimal? "1.5e-3".toList == some (false, 15, -4)
#guard decimal? "-.5".toList == some (true, 5, -1) && decimal? "5.".toList == some (false, 5, 0)
#guard decimal? "1.e2".toList == some (false, 1, 2) && decimal? ".e1".toList == none
#guard decimal? "1e".toList == none && decimal? "+".toList == none && decimal? "1_0".toList == none

/-- `n · 10ᵉ`, rounded half away from zero, as an integer. -/
def roundScaled (n : Nat) (e : Int) : Nat :=
  if 0 ≤ e then n * 10 ^ e.toNat
  else
    let d := 10 ^ (-e).toNat
    (2 * n + d) / (2 * d)

#guard roundScaled 15 (-1) == 2 && roundScaled 14 (-1) == 1 && roundScaled 25 (-1) == 3
#guard roundScaled 5 (-1) == 1 && roundScaled 4999 (-4) == 0 && roundScaled 155 (-1) == 16

def lower (cs : List Char) : String := String.ofList (cs.map Char.toLower)

/-- A sign that is not first or after the exponent's `e`. -/
def midSign (cs : List Char) : Bool :=
  ((cs.zip (' ' :: cs)).drop 1).any fun (c, p) => (c == '+' || c == '-') && p != 'e' && p != 'E'

/-- A string that is surely not a number (spaces around it trimmed): empty,
with a sign but first or after the exponent's `e`, two points, or a
character outside digits, signs, points and the exponent's `e`, unless it may be one
of the other forms DuckDB reads: `inf…` or `nan…` (`nan(…)`) for a double,
`0x…` or `0b…` for an integer, or digits with `_` or tabs. -/
def notANumber (asDouble : Bool) (cs : List Char) : Bool :=
  let core := lower (sign cs).2
  if cs.isEmpty then true
  else if cs.any fun c => c == '(' || c == '_' || c == '\t' || c == '\n' || c == '\r' then false
  else if asDouble && (core.startsWith "inf" || core.startsWith "nan") then false
  else if !asDouble && (core.startsWith "0x" || core.startsWith "0b") then false
  else cs.any (fun c => !(c.isDigit || "+-.eE".contains c)) || midSign cs || cs.count '.' > 1

/-- The large exponents DuckDB reads its own way. -/
def tame (n : Nat) (e : Int) : Bool := (toString n).length + e.natAbs ≤ 40

/-- `CAST(s AS BIGINT)`. -/
def bigint (s : String) : Parsed :=
  let cs := trim s.toList
  match decimal? cs with
  | some (neg, n, e) =>
    if !tame n e then .unknown else
    let m : Int := roundScaled n e
    let v := if neg then -m else m
    if -2 ^ 63 ≤ v && v < 2 ^ 63 then .val (.int v) else .bad
  | none => if notANumber false cs then .bad else .unknown

#guard bigint " 12 " == .val (.int 12) && bigint "1.5" == .val (.int 2)
#guard bigint "-1.5" == .val (.int (-2)) && bigint "1e3" == .val (.int 1000)
#guard bigint "9223372036854775808" == .bad && bigint "-9223372036854775808" == .val (.int (-2 ^ 63))
#guard bigint "-9223372036854775808.5" == .bad && bigint "123456789012345678.5" == .val (.int 123456789012345679)
#guard bigint "12.3 p" == .bad && bigint ":" == .bad && bigint "" == .bad && bigint "0x1F" == .unknown
#guard bigint "1_000" == .unknown && bigint "\t7" == .unknown && bigint "f" == .bad
#guard bigint "0x1F" == .unknown && bigint "1e" == .unknown && bigint "yes" == .bad

/-- `CAST(s AS DOUBLE)`, as a double's code. -/
def double (s : String) : Parsed :=
  let cs := trim s.toList
  let (neg, r) := sign cs
  let w := lower r
  if w == "inf" || w == "infinity" then .val (.float (if neg then FloatCode.negInf else FloatCode.posInf))
  else if w == "nan" then .val (.float FloatCode.nan)
  else match decimal? cs with
    | some (neg, n, e) =>
      if !tame n e then .unknown else
      let f := if e < 0 then Float.ofScientific n true (-e).toNat else Float.ofScientific n false e.toNat
      .val (.float (FloatCode.ofFloat (if neg then -f else f)))
    | none => if notANumber true cs then .bad else .unknown

#guard double " 1.5 " == .val (.float (FloatCode.ofFloat 1.5)) && double "1e3" == .val (.float (FloatCode.ofFloat 1000))
#guard double "-Infinity" == .val (.float FloatCode.negInf) && double "NaN" == .val (.float FloatCode.nan)
#guard double "1e400" == .unknown && double "12.3 p" == .bad && double "1,5" == .bad
#guard double "nan(abc)" == .unknown && double "0.1" == .val (.float (FloatCode.ofFloat 0.1))
#guard double "T" == .bad && double "yes" == .bad && double "infin" == .unknown
#guard double "0 0" == .bad
#guard double "2024-13-01" == .bad && double "1.2.3" == .bad && double " -1e-5" == .val (.float (FloatCode.ofFloat (-1e-5)))

/-- `CAST(s AS BOOLEAN)`: DuckDB's words, any case, nothing around them. -/
def boolean (s : String) : Parsed :=
  let w := lower s.toList
  if ["true", "t", "yes", "y", "1"].contains w then .val (.bool true)
  else if ["false", "f", "no", "n", "0"].contains w then .val (.bool false)
  else .bad

#guard boolean "TRUE" == .val (.bool true) && boolean "n" == .val (.bool false)
#guard boolean " t " == .bad && boolean "on" == .bad && boolean "01" == .bad

/-- `n` digits: one or two (`two`), or any number. -/
def field? (cs : List Char) (two : Bool) : Option (Nat × List Char) :=
  let ds := cs.takeWhile Char.isDigit
  if ds.isEmpty || (two && ds.length > 2) then none else some (digitsVal ds, cs.drop ds.length)

/-- The days of `Y-M-D` (or `Y/M/D`, `Y M D`) and what follows it: `bad` for a month or day the
calendar lacks, `unknown` outside the years 1 to 9999. -/
def ymd? (cs : List Char) : Option (Parsed × List Char) := do
  let (y, r) ← field? cs false
  let sep :: r := r | none
  if !"-/ ".contains sep then none
  let (m, r) ← field? r true
  let sep' :: r := r | none
  if sep' != sep then none
  let (d, r) ← field? r true
  if y < 1 || y > 9999 then return (.unknown, r)
  if m < 1 || m > 12 || d < 1 then return (.bad, r)
  let i : Int := y * 12 + m - 1
  let first := Time.monthStart i
  if (d : Int) > Time.monthStart (i + 1) - first then return (.bad, r)
  return (.val (.date (first + d - 1)), r)

/-- The runs of digits in `cs`. -/
def runs (cs : List Char) : Nat :=
  ((cs.zip (' ' :: cs)).filter fun (c, p) => c.isDigit && !p.isDigit).length

#guard runs "2024-01-05".toList == 3 && runs "/ 0".toList == 1 && runs "".toList == 0

/-- A string that is surely not a date or timestamp: empty, or not one of
DuckDB's words and without the three numbers and two separators of a
year, month and day. -/
def notADate (cs : List Char) : Bool :=
  let words := ["epoch", "infinity", "-infinity", "+infinity"]
  cs.isEmpty || (!words.contains (lower cs) &&
    (runs cs < 3 || ((sign cs).2.filter ("-/ ".contains ·)).length < 2))

/-- Nothing, or the offset DuckDB reads and drops from a timestamp: `Z`, or
a sign, two digits and two more (`:MM` or `MM`), after a space or not. -/
def offset : List Char → Bool
  | [] | ['Z'] => true
  | ' ' :: r => match r with
    | c :: _ => (c == '+' || c == '-') && offset r
    | [] => false
  | c :: r =>
    (c == '+' || c == '-') &&
    match r with
    | [a, b] | [a, b, ':', _, _] | [a, b, _, _] =>
      a.isDigit && b.isDigit && (r.drop 2).all fun x => x.isDigit || x == ':'
    | _ => false

#guard offset [] && offset "Z".toList && offset "+00:00".toList && offset "-02".toList
#guard offset " +01".toList && offset "+0130".toList && !offset "+1".toList && !offset "x".toList

/-- `H:MM[:SS[.f]]` as microseconds: `bad` past 23:59:59, `unknown` at 24. -/
def time? (cs : List Char) : Option Parsed := do
  let (h, r) ← field? cs true
  let ':' :: r := r | none
  let md := r.takeWhile Char.isDigit
  if md.length != 2 then none
  let mi := digitsVal md
  let (sec, us, rest) ← match r.drop 2 with
    | [] => some (0, 0, [])
    | ':' :: r =>
      let sd := r.takeWhile Char.isDigit
      if sd.length != 2 then none else
      match r.drop 2 with
      | '.' :: f =>
        let fd := f.takeWhile Char.isDigit
        let us := digitsVal (fd.take 6 ++ List.replicate (6 - min 6 fd.length) '0')
        some (digitsVal sd, us, f.drop fd.length)
      | r => some (digitsVal sd, 0, r)
    | r => some (0, 0, r)
  if !offset rest then none
  if h == 24 then return .unknown
  if h > 24 || mi > 59 || sec > 59 then return .bad
  return .val (.tod (((h * 60 + mi) * 60 + sec) * 1000000 + us))

/-- `CAST(s AS DATE)`, as days since 1970-01-01. -/
def date (s : String) : Parsed :=
  let cs := trim s.toList
  if lower cs == "epoch" then .val (.date 0) else
  match ymd? cs with
  | some (p, []) => p
  -- A time after the date, which DuckDB drops.
  | some (p, c :: r) =>
    if (c == ' ' || c == 'T') && (time? r matches some (.val _)) then p
    else if notADate cs then .bad else .unknown
  | none => if notADate cs then .bad else .unknown

#guard date "2024-01-05 10:00:00.5" == .val (.date 19727) && date "2024-01-05T23:59" == .val (.date 19727)
#guard date "2024-01-05" == .val (.date 19727) && date " 2024-1-5 " == .val (.date 19727)
#guard date "2024-02-30" == .bad && date "2023-02-29" == .bad && date "2024-02-29" == .val (.date 19782)
#guard date "1-1-1" == .val (.date Time.dayMin) && date "9999-12-31" == .val (.date Time.dayMax)
#guard date "2024-13-01" == .bad && date "12024-01-01" == .unknown && date "abc" == .bad
#guard date "2024/01/05" == .val (.date 19727) && date "2024 1 5" == .val (.date 19727)
#guard date "/ 0" == .bad && date "0 0" == .bad
#guard date "1" == .bad && date "-5" == .bad && date "1.5e3" == .bad && date "2024 01/05" == .unknown
#guard date "infinity" == .unknown && date "2024-01-05 10:00" == .val (.date 19727) && date "EPOCH" == .val (.date 0)

/-- `CAST(s AS TIMESTAMP)`, as microseconds since 1970-01-01. -/
def timestamp (s : String) : Parsed :=
  let cs := trim s.toList
  if lower cs == "epoch" then .val (.ts 0) else
  match ymd? cs with
  | some (p, []) => match p with
    | .val (.date d) => .val (.ts (d * Time.usPerDay))
    | p => p
  | some (p, c :: r) =>
    if c != ' ' && c != 'T' then (if notADate cs then .bad else .unknown) else
    match p, time? r with
    | .val (.date d), some (.val (.tod t)) => .val (.ts (d * Time.usPerDay + t))
    | .bad, some _ => .bad
    | .val _, some .bad => .bad
    | _, _ => .unknown
  | none => if notADate cs then .bad else .unknown

#guard timestamp "2024-01-05" == .val (.ts (19727 * Time.usPerDay))
#guard timestamp "2024-01-05 10:00" == .val (.ts (19727 * Time.usPerDay + 36000000000))
#guard timestamp "2024-01-05T10:00:01.1234567" == .val (.ts (19727 * Time.usPerDay + 36001123456))
#guard timestamp "2024-01-05 10:00:00." == .val (.ts (19727 * Time.usPerDay + 36000000000))
#guard timestamp "2024-01-05 25:00" == .bad && timestamp "2024-01-05 23:60:00" == .bad
#guard timestamp "2024-01-05 24:00:00" == .unknown && timestamp "2024-01-05 1:2" == .unknown
#guard timestamp "2024-01-05 10:00+01" == .val (.ts (19727 * Time.usPerDay + 36000000000))
#guard timestamp "2024-05-03T01:00:02+00:00" == timestamp "2024-05-03 01:00:02" && timestamp "x" == .bad

end Substrait.VarcharCasts
