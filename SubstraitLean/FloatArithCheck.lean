import SubstraitLean.FloatArith

/-!
# D31 against native doubles

`#guard`s that compare the exact operations of `FloatArith.lean` with the
platform's native doubles (IEEE 754 binary64, round to nearest even), so the
proof build checks them on every run:

* `addI`, `subI`, `mulI` and `divI` against native `+ - * /` bit for bit,
  `-0.0` included, with any NaN equal to any NaN (D31 leaves a produced
  NaN's sign open);
* the reference's `fadd`, `fsub`, `fmul` and `fdiv` against `lift₂`, the
  native definitions they replace, so no value of the reference changes.

The operands: every pair of a table of edge values (zeros, the smallest
subnormal, the largest subnormal, the smallest normal, one, the largest
double, the infinities, NaN, and their negatives), operands that tie
(`1 + 2⁻⁵³`, the subnormal halfway points), and pseudo-random operands at
every exponent from `0` to `2046` paired with operands at random exponents,
whose sums, products and quotients cross each binade, the subnormal range
and the overflow threshold.
-/

namespace Substrait.FloatCode.Check

/-- A native double's code, `-0.0` and the negative NaN kept. -/
def codeOf (x : Float) : Int :=
  let neg := x.toBits >>> 63 == 1
  if x == 0 && neg then negZero
  else if x.isNaN && neg then negNan
  else ofFloat x

/-- Equal codes, any NaN equal to any NaN. -/
def same (a b : Int) : Bool := a == b || (isNanCode a && isNanCode b)

/-- The four operations, exact and native. -/
def ops : List ((Int → Int → Int) × (Int → Int → Int) × (Float → Float → Float)) :=
  [(addI, fadd, (· + ·)), (subI, fsub, (· - ·)), (mulI, fmul, (· * ·)), (divI, fdiv, (· / ·))]

/-- Does every operation agree with the native one on `x` and `y`? -/
def agrees (x y : Float) : Bool :=
  ops.all fun (ieee, ref, nat) =>
    same (ieee (codeOf x) (codeOf y)) (codeOf (nat x y)) &&
      ref (ofFloat x) (ofFloat y) ==
        lift₂ nat (ofFloat x) (ofFloat y)

def bits (n : UInt64) : Float := Float.ofBits n

/-- Edge values and their negatives. -/
def edges : List Float :=
  let pos := [0, 1, 0x000FFFFFFFFFFFFF, 0x0010000000000000, 0x0010000000000001,
    0x3FF0000000000000, 0x3FF0000000000001, 0x3CA0000000000000, 0x3C90000000000000,
    0x4340000000000000, 0x7FEFFFFFFFFFFFFF, 0x7FE0000000000000, 0x7FF0000000000000,
    0x7FF8000000000000, 0x0000000000000003, 0x0008000000000000]
  pos.map bits ++ pos.map fun n => bits (n ||| 0x8000000000000000)

/-- A linear congruential generator over 64 bits. -/
def next (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

/-- `n` pairs: the first operand at exponent `i` for `i` from `0` to `2046`,
the second at a random exponent, with random significands and signs. -/
def randomPairs : List (Float × Float) := Id.run do
  let mut s : UInt64 := 0x5EED
  let mut out := []
  for i in [0:2047] do
    s := next s
    let m1 := s >>> 12
    s := next s
    let e2 := (s >>> 40) % 2047
    let m2 := (s >>> 12) &&& 0xFFFFFFFFFFFFF
    let sg := (s &&& 3)
    let x := bits (((sg &&& 1) <<< 63) ||| (i.toUInt64 <<< 52) ||| m1)
    let y := bits (((sg >>> 1) <<< 63) ||| (e2 <<< 52) ||| m2)
    out := (x, y) :: out
  return out

#guard edges.all fun x => edges.all fun y => agrees x y
#guard randomPairs.all fun (x, y) => agrees x y && agrees y x
-- Ties to even: `1 + 2⁻⁵³` rounds to `1`, `1 + 3 · 2⁻⁵³` to `1 + 2⁻⁵¹`, and
-- halfway subnormals to the even neighbour.
#guard agrees 1.0 (bits 0x3CA0000000000000) && agrees 1.0 (bits 0x3CB8000000000000)
#guard agrees (bits 3) (bits 0x3FE0000000000000) && agrees (bits 1) (bits 0x3FE0000000000000)
-- Signed zeros: `(-0) + (-0)` is `-0`, `x - x` is `+0`, `-1 · 0` is `-0`.
#guard addI negZero negZero == negZero && subI (ofFloat 1.5) (ofFloat 1.5) == 0
#guard mulI (ofFloat (-1.0)) 0 == negZero && divI (ofFloat 1.0) negZero == negInf

end Substrait.FloatCode.Check
