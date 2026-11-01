/-!
# Floats and timestamps as integers

**Floats.** Doubles compare as SQL engines compare them (PostgreSQL, DuckDB,
Spark, Snowflake): `-∞ < negatives < 0.0 < positives < +∞ < NaN`, where
`-0.0` *is* `0.0` and every NaN is the same NaN, equal to itself. The model
has one zero and one NaN, so `-0.0` never appears in a result (`-1 · 0.0` is
`0.0`) and `-0.0 >= 0` holds. (DataFusion's own order, `f64::total_cmp`,
puts `-0.0` below `+0.0` and negative NaNs first; `sverify` canonicalizes
DataFusion's inputs and results instead.)

A double is represented by an integer *code* with exactly that order: for
magnitude `m` (`|x| · 2¹⁰⁷⁴` for finite `x`, which is an exact integer;
`M + 1` for ∞, `M + 2` for NaN) the code is `±(2m + 1)`, and zero is `0`.
Comparing doubles is then comparing codes, so filters such as `v > 0.5` or
`v <> -9999.0` are modelled exactly and reuse all of the integer reasoning,
and negation is code negation (the parser keeps NaN fixed under it).

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

/-- The code of magnitude `m`: zero has one code, `0`, and NaN is never
negative. -/
def ofMag (negative : Bool) (m : Nat) : Int :=
  let c : Int := 2 * m + 1
  if m = 0 then 0 else if negative ∧ m ≠ nanMag then -c else c

def posInf : Int := ofMag false infMag
def negInf : Int := ofMag true infMag
def nan : Int := ofMag false nanMag

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

/-- Negation flips the sign; zero (code `0`) stays zero. Code negation would
turn NaN into a code below `-∞`, so the parser writes `negate` as
`CASE WHEN x = NaN THEN x ELSE -x END`, as SQL engines have one NaN. -/
def neg (c : Int) : Int := -c

def ofInt (i : Int) : Int := ofFloat (Float.ofInt i)

def isNan (c : Int) : Bool := c == nan

-- One zero and one NaN: `-0.0` and a negative NaN (as x86 computes `0/0`)
-- have the codes of `0.0` and NaN, and negation keeps zero.
#guard ofFloat (Float.ofBits 0x8000000000000000) == 0 && ofFloat 0.0 == 0
#guard ofFloat (Float.ofBits 0xFFF8000000000000) == nan && ofFloat (0.0 / 0.0) == nan
#guard neg (ofFloat 0.0) == 0 && neg (ofFloat 1.5) == ofFloat (-1.5)
#guard ofFloat (-1.0 * 0.0) == 0 && negInf < ofFloat (-1.0) && ofFloat 5e-324 > 0 && posInf < nan

/-- `(-1)^s · m · 2⁻¹⁰⁷⁴` for a finite code, as `(negative, m)`. -/
def finiteParts (c : Int) : Bool × Nat := (c < 0, (c.natAbs - 1) / 2)

/-- `fmod(a, b)`, the remainder of doubles in C and IEEE 754, which DuckDB,
DataFusion and Spark compute for `%`: `a - b · trunc(a / b)`, with the sign of
`a`. It is exact, so the codes give it without rounding: the magnitude of a
finite double is an integer (`|x| · 2¹⁰⁷⁴`), and the remainder of the
magnitudes is the magnitude of the remainder. NaN or an infinite `a` give
NaN, and an infinite `b` gives `a`. A zero `b` gives NaN here, but the model
reports it as a division by zero (`BinFn.issue`), as for integers (#203). -/
def fmod (a b : Int) : Int :=
  let (negative, ma) := finiteParts a
  let mb := (finiteParts b).2
  if infMag ≤ ma ∨ nanMag ≤ mb ∨ mb = 0 then nan
  else if mb = infMag then a
  else ofMag negative (ma % mb)

#guard fmod (ofFloat 7.5) (ofFloat 2.0) == ofFloat 1.5
#guard fmod (ofFloat (-7.5)) (ofFloat 2.0) == ofFloat (-1.5)
#guard fmod (ofFloat 7.5) (ofFloat (-2.0)) == ofFloat 1.5
-- `-0.0` in IEEE; the model's one zero.
#guard fmod (ofFloat (-4.0)) (ofFloat 2.0) == 0 && fmod 0 (ofFloat 2.0) == 0
#guard fmod (ofFloat 7.5) 0 == nan && fmod 0 0 == nan && fmod nan (ofFloat 2.0) == nan
#guard fmod posInf (ofFloat 2.0) == nan && fmod negInf (ofFloat 2.0) == nan
#guard fmod (ofFloat 7.5) posInf == ofFloat 7.5 && fmod (ofFloat (-7.5)) negInf == ofFloat (-7.5)
#guard fmod (ofFloat 7.5) nan == nan && fmod posInf posInf == nan
-- Exact where `a - b · trunc(a / b)` in doubles is not (it gives `0.0` for
-- the first and third), across exponents and for subnormals.
#guard fmod (ofFloat 1e308) (ofFloat 3.0) == ofFloat 2.0
#guard fmod (ofFloat 1e308) (ofFloat 1e-300) == ofFloat 3.0195000970293847e-301
#guard fmod (ofFloat 1152921504606846977.0) (ofFloat 7.0) == ofFloat 1.0
#guard fmod (ofFloat 0.3) (ofFloat 0.1) == ofFloat 0.09999999999999998
#guard fmod (ofFloat 5e-324) (ofFloat 2.0) == ofFloat 5e-324

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
