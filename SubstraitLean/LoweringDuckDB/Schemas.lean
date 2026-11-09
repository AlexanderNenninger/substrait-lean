import SubstraitLean.LoweringSearch
import SubstraitLean.LoweringDuckDB.Lemmas

/-!
# DuckDB's hand-written template schemas (#241, #242)

The constructs the lowering search does not reach on DuckDB's profile, for
`generate_lowering … hand_written duckdbSchemas` (`scripts/RegenLowering.lean`):
the wrap-around of `overflow` = `SILENT`, and the guards that copy the
reference's error conditions where DuckDB's IEEE operations give NaN, `±∞` or
`0` instead (FACTS R15). Each instance is proved by the kernel, as any
generated entry is.
-/

namespace Substrait.LoweringSearch

open Lean

/-- The guard on which a double operation makes a NaN of numbers (`nanCase`),
atom for atom. -/
def nanGuard : BinFn → Option Tm
  | .fadd => some (orFn (andFn (eqFn (.field 0) posInfT) (eqFn (.field 1) negInfT))
      (andFn (eqFn (.field 0) negInfT) (eqFn (.field 1) posInfT)))
  | .fsub => some (orFn (andFn (eqFn (.field 0) posInfT) (eqFn (.field 1) posInfT))
      (andFn (eqFn (.field 0) negInfT) (eqFn (.field 1) negInfT)))
  | .fmul => some (orFn (andFn (eqFn (.field 0) (.lit (.float 0))) (isInfT (.field 1)))
      (andFn (isInfT (.field 0)) (eqFn (.field 1) (.lit (.float 0)))))
  | .fdiv => some (andFn (isInfT (.field 0)) (isInfT (.field 1)))
  -- IEEE division (D39): `0 / 0` too, either zero's sign.
  | .fdivIeee => some (orFn (andFn (isInfT (.field 0)) (isInfT (.field 1)))
      (andFn (eqFn (.field 0) (.lit (.float 0))) (eqFn (.field 1) (.lit (.float 0)))))
  | .fmod => some (andFn (isInfT (.field 0)) (notFn (eqFn (.field 1) nanT)))
  | _ => none

/-- `CASE WHEN x IS NOT NULL AND y = 0 THEN error ELSE e END`: a zero divisor
raises, `NULL / 0` stays `NULL`. `x` is of one of the kinds `ks`, `0` of kind
`k` (#923). -/
def zeroGuard (ks : List NumKind) (k : NumKind) (e : Tm) : Tm :=
  let isNum := match ks with
    | [] => Tm.lit (.bool false)
    | k :: ks => ks.foldl (fun g k => orFn g (isNumFn k (.field 0))) (isNumFn k (.field 0))
  .ite (andFn isNum (eqFn (.field 1) (.lit (k.val 0))))
    (.raise "division by zero" (.field 1)) e

/-- **DuckDB's unary schemas.**

* `overflow` = `SILENT` wraps around at a width, which takes arithmetic rather
  than a `CASE`: `CASE WHEN x IS NOT NULL THEN ((x + h) % m + m) % m - h ELSE x
  END` in 128-bit integers (`BinFn.dadd`, `dsub`, `imod`), with `h = 2^(w-1)`
  and `m = 2^w`.
* An elementary function raises outside its domain (`FMath.inDomain`), where
  DuckDB gives NaN or `-∞`: `CASE WHEN x < lo OR (hi < x AND x <> NaN) THEN
  error ELSE f(x) END`, the bounds written as `FMath.lo?` and `FMath.hi?`.
* `round` and `ceil` give `0.0` for a negative value that rounds to zero, where
  DuckDB gives IEEE's `-0.0` (`round_zero_sign`). -/
def schema? : UnFn → Option Tm
  | .fit .silent w =>
    let h := w.half
    let m := w.modulus
    let x := Tm.field 0
    some (.ite (isNumFn .int x)
      (dsubFn (imodFn (daddFn (imodFn (daddFn x (.lit (.int h))) (.lit (.int m))) (.lit (.int m)))
        (.lit (.int m))) (.lit (.int h))) x)
  | .fmath f =>
    let x := Tm.field 0
    -- The bounds as `FMath.lo?` and `FMath.hi?` write them, by name, so that
    -- the proofs treat `±1` and `±∞` as the variables they generalize to.
    let c (n : Lean.Name) := Lean.mkConst n
    let op (h i inst : Lean.Name) (a : Lean.Expr) : Lean.Expr :=
      mkApp6 (Lean.mkConst h [Level.zero, Level.zero, Level.zero]) (c ``Int) (c ``Int) (c ``Int)
        (mkApp2 (Lean.mkConst i [Level.zero]) (c ``Int) (c inst)) a (toExpr (1 : Int))
    let term (v : Int) : Lean.Expr :=
      if v == FloatCode.negOne then c ``FloatCode.negOne
      else if v == FloatCode.one then c ``FloatCode.one
      else if v == FloatCode.negInf + 1 then op ``HAdd.hAdd ``instHAdd ``Int.instAdd (c ``FloatCode.negInf)
      else if v == FloatCode.posInf - 1 then op ``HSub.hSub ``instHSub ``Int.instSub (c ``FloatCode.posInf)
      else toExpr v
    let bound (v : Int) (l : String) : Tm := namedFloat v (term v) l
    let lo := f.lo?.map fun v => ltFn x (bound v s!"lo({f.name})")
    let hi := f.hi?.map fun v =>
      andFn (ltFn (bound v s!"hi({f.name})") x) (notFn (eqFn x nanT))
    let g := match lo, hi with
      | some a, some b => some (orFn a b)
      | some a, none => some a
      | none, some b => some b
      | none, none => none
    g.map fun g => .ite g (.raise "domain error" x) (.self [x])
  -- A negative value that rounds to zero is `0.0`, where DuckDB gives IEEE's
  -- `-0.0` (`round_zero_sign`): `Lowering.zeroTemplate`, written and proved by
  -- hand (`Lowering.fround_agree`), as the tactic's proof is slower.
  | .fround => some (.expr Lowering.froundTemplate (Lean.mkConst ``Lowering.froundTemplate)
      "round: 0.0 for a negative value that rounds to zero")
  | .fceil => some (.expr Lowering.fceilTemplate (Lean.mkConst ``Lowering.fceilTemplate)
      "ceil: 0.0 for a negative value that rounds to zero")
  | _ => none

/-- **DuckDB's binary schemas** (#242), for its IEEE operations:

* `+ - * / % ^` of doubles raise where the reference does: a zero divisor
  (`zeroGuard`), and the operands of which IEEE 754 makes a NaN (`nanGuard`),
  where DuckDB gives NaN or `±∞`.
* `%` of integers is `0` by `-1`, where DuckDB raises on `MIN % -1`.
* `>>` raises on a shift outside `0`–`63`, where DuckDB gives `0`. -/
def schemaBin? (f : BinFn) : Option Tm :=
  let self := Tm.self [.field 0, .field 1]
  let nan (e : Tm) : Option Tm := (nanGuard f).map fun g => .ite g (.raise "domain error" (.field 1)) e
  match f with
  | .fdiv | .fmod => (nan self).map (zeroGuard [.float] .float)
  -- `(-∞) ^ y` for a finite `y` that is not an integer raises too
  -- (`negInfPow`), where DuckDB gives `+∞` or `0`: `Lowering.fpowTemplate`,
  -- written and proved by hand (`Lowering.fpow_agree`), as the tactic's proof
  -- is slower.
  | .fpow => some (.expr Lowering.fpowTemplate (Lean.mkConst ``Lowering.fpowTemplate)
      "power: error where the reference raises, else #0 ^ #1")
  | .imod => some (zeroGuard [.int, .tod] .int
      (.ite (andFn (eqFn (.field 1) (.lit (.int (-1)))) (isNumFn .int (.field 0))) (.lit (.int 0)) self))
  -- `<<` is `Lowering.shlTemplate`, written and proved by hand
  -- (`Lowering.bit_shl_agree`): the tactic does not reach it in time.
  | .bit .shl => some (.expr Lowering.shlTemplate (Lean.mkConst ``Lowering.shlTemplate)
      "shl: error outside 0-63, else wrap64(#0 * 2^#1)")
  | .bit .shr => some (.ite (andFn (isNumFn .int (.field 0))
      (orFn (ltFn (.field 1) (.lit (.int 0))) (notFn (ltFn (.field 1) (.lit (.int 64))))))
      (.raise "domain error" (.field 1)) self)
  | _ => nan self

/-- DuckDB's schemas, for `generate_lowering`. -/
def duckdbSchemas : Schemas := { un := schema?, bin := schemaBin? }

end Substrait.LoweringSearch
