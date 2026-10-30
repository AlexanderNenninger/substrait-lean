/-!
# Floats and timestamps as integers

**Floats.** DataFusion compares doubles by Arrow's *total order*
(`f64::total_cmp`): `-NaN < -∞ < negatives < -0.0 < +0.0 < positives < +∞ < NaN`,
and NaN equals NaN. A double is represented by an integer *code* with exactly
that order: for magnitude `m` (`|x| · 2¹⁰⁷⁴` for finite `x`, which is an exact
integer; `M + 1` for ∞, `M + 2` for NaN) the code is `±(2m + 1)`. Comparing
doubles is then comparing codes, so filters such as `v > 0.5` or
`v <> -9999.0` are modelled exactly and reuse all of the integer reasoning,
and negation is code negation.

Float *arithmetic* rounds; it is computed with Lean's native `Float` and
treated as "some double" by the contract checker, so no rounding facts are
assumed. The conversions below go through the IEEE bit pattern and are
trusted code.

**Timestamps** are microseconds since 1970-01-01, dates are days, and
day/second intervals are microseconds.
-/

namespace Substrait.FloatCode

/-- Magnitude of the largest finite double: (2⁵³ − 1) · 2⁹⁷¹ · 2¹⁰⁷⁴. -/
@[irreducible] def maxMag : Nat := (2 ^ 53 - 1) * 2 ^ 2045
def infMag : Nat := maxMag + 1
def nanMag : Nat := maxMag + 2

def ofMag (negative : Bool) (m : Nat) : Int :=
  let c : Int := 2 * m + 1
  if negative then -c else c

def posInf : Int := ofMag false infMag
def negInf : Int := ofMag true infMag
def nan : Int := ofMag false nanMag
def negNan : Int := ofMag true nanMag

/-- The code of a native double. -/
def ofFloat (f : Float) : Int :=
  let bits : Nat := f.toBits.toNat
  let negative := bits / 2 ^ 63 == 1
  let e : Nat := (bits / 2 ^ 52) % 2 ^ 11
  let m : Nat := bits % 2 ^ 52
  let mag : Nat :=
    if e == 2047 then (if m == 0 then infMag else nanMag)
    else if e == 0 then m else (2 ^ 52 + m) * 2 ^ (e - 1)
  ofMag negative mag

/-- The native double for a code (exact for every code `ofFloat` produces). -/
def toFloat (c : Int) : Float :=
  let sign : Nat := if c < 0 then 1 else 0
  let mag := (c.natAbs - 1) / 2
  let bits :=
    if mag ≥ nanMag then 0x7FF8000000000000
    else if mag == infMag then 0x7FF0000000000000
    else if mag < 2 ^ 52 then mag
    else
      let l := Nat.log2 mag
      let e := l - 51
      (e % 2 ^ 11) * 2 ^ 52 + (mag / 2 ^ (l - 52) - 2 ^ 52)
  Float.ofBits (UInt64.ofNat (sign * 2 ^ 63 + bits))

def lift₂ (op : Float → Float → Float) (a b : Int) : Int := ofFloat (op (toFloat a) (toFloat b))

/-- `ROUND(x, d)`, as DataFusion computes it: `round(x · 10ᵈ) / 10ᵈ`. -/
def roundTo (d : Int) (c : Int) : Int :=
  let p := Float.pow 10.0 (Float.ofInt d)
  ofFloat ((toFloat c * p).round / p)

/-- Negation flips the sign, also of zero and NaN. -/
def neg (c : Int) : Int := -c

def ofInt (i : Int) : Int := ofFloat (Float.ofInt i)

def isNan (c : Int) : Bool := c == nan || c == negNan

/-- `(-1)^s · m · 2⁻¹⁰⁷⁴` for a finite code, as `(negative, m)`. -/
def finiteParts (c : Int) : Bool × Nat := (c < 0, (c.natAbs - 1) / 2)

end Substrait.FloatCode

namespace Substrait.Time

/-- Days since 1970-01-01 for a proleptic Gregorian date (Howard Hinnant's
`days_from_civil`). -/
def daysFromCivil (y m d : Int) : Int :=
  let y := if m ≤ 2 then y - 1 else y
  let era := (if y ≥ 0 then y else y - 399) / 400
  let yoe := y - era * 400
  let mp := (m + 9) % 12
  let doy := (153 * mp + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe - 719468

def parseNat? (s : String) : Option Nat := if s.isEmpty then none else s.toNat?

/-- `YYYY-MM-DD` → days since the epoch. -/
def parseDate? (s : String) : Option Int := do
  let [y, m, d] := s.splitOn "-" | none
  return daysFromCivil (← parseNat? y) (← parseNat? m) (← parseNat? d)

/-- `YYYY-MM-DD[ HH:MM:SS[.ffffff]]` → microseconds since the epoch. -/
def parseTimestamp? (s : String) : Option Int := do
  let (datePart, timePart) := match s.splitOn " " with
    | [d] => (d, "00:00:00")
    | [d, t] => (d, t)
    | _ => ("", "")
  let days ← parseDate? datePart
  let (hms, fracPart) := match timePart.splitOn "." with
    | [t] => (t, "")
    | [t, f] => (t, f)
    | _ => ("", "")
  let [h, mi, sec] := hms.splitOn ":" | none
  let frac := (fracPart ++ "000000").take 6
  let micros ← if fracPart.isEmpty then pure 0 else parseNat? frac.toString
  return ((days * 24 + (← parseNat? h)) * 60 + (← parseNat? mi)) * 60_000_000 +
    (← parseNat? sec) * 1_000_000 + micros

end Substrait.Time

namespace Substrait.Base64

def decodeChar (c : Char) : Option Nat :=
  if 'A' ≤ c ∧ c ≤ 'Z' then some (c.toNat - 'A'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'z' then some (c.toNat - 'a'.toNat + 26)
  else if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat + 52)
  else if c = '+' then some 62
  else if c = '/' then some 63
  else none

/-- Decode standard base64 into bytes. -/
def decode (s : String) : Option (List Nat) := do
  let vals ← (s.toList.filter (· ≠ '=')).mapM decodeChar
  let bits := vals.flatMap fun v => (List.range 6).reverse.map fun i => (v / 2 ^ i) % 2
  let nbytes := bits.length / 8
  return (List.range nbytes).map fun b =>
    ((List.range 8).map fun i => bits[b * 8 + i]! * 2 ^ (7 - i)).sum

/-- A little-endian two's-complement integer (Substrait's decimal encoding). -/
def leSigned (bytes : List Nat) : Int :=
  let n : Nat := (bytes.zipIdx.map fun (b, i) => b * 256 ^ i).sum
  if bytes.length > 0 && bytes.getLast! ≥ 128 then (n : Int) - 256 ^ bytes.length else n

end Substrait.Base64
