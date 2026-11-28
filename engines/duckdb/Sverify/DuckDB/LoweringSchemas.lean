import Sverify.Engines.LoweringGuards
import Sverify.DuckDB.LoweringLemmas

/-!
# DuckDB's hand-written template schemas (#241, #242)

The constructs the lowering search does not reach on DuckDB's profile, for
`generate_lowering … hand_written duckdbSchemas` (`scripts/RegenLowering.lean`):
the wrap-around of `overflow` = `SILENT`, and the guards that copy the
reference's error conditions where DuckDB's IEEE operations give NaN, `±∞` or
`0` instead (FACTS R15). Each instance is proved by the kernel, as any
generated entry is. The guards no engine owns (`nanGuard`, `zeroGuard`,
`fmathGuard`) are engines-common's (`Sverify.Engines.LoweringGuards`).
-/

namespace Substrait.LoweringSearch

open Lean

/-- **DuckDB's unary schemas.**

* `overflow` = `SILENT` wraps around at a width, which takes arithmetic rather
  than a `CASE`: `CASE WHEN x IS NOT NULL THEN ((x + h) % m + m) % m - h ELSE x
  END` in 128-bit integers (`BinFn.dadd`, `dsub`, `imod`), with `h = 2^(w-1)`
  and `m = 2^w`.
* An elementary function raises outside its domain (`FMath.inDomain`), where
  DuckDB gives NaN or `-∞`: `CASE WHEN x < lo OR (hi < x AND x <> NaN) THEN
  error ELSE f(x) END`, the bounds written as `FMath.lo?` and `FMath.hi?`.
* `round` and `ceil` give `0.0` for a negative value that rounds to zero, where
  DuckDB gives IEEE's `-0.0` (`round_zero_sign`).
* A cast of a double to an integer truncates first, as DuckDB's cast rounds half
  to even (`float_to_int`, duckdb-R9, ruling 284). -/
def schema? : UnFn → Option Tm
  | .fit .silent w =>
    let h := w.half
    let m := w.modulus
    let x := Tm.field 0
    some (.ite (isNumFn .int x)
      (dsubFn (imodFn (daddFn (imodFn (daddFn x (.lit (.int h))) (.lit (.int m))) (.lit (.int m)))
        (.lit (.int m))) (.lit (.int h))) x)
  | .fmath f =>
    (fmathGuard f).map fun g => .ite g (.raise "domain error" (.field 0)) (.self [.field 0])
  -- A negative value that rounds to zero is `0.0`, where DuckDB gives IEEE's
  -- `-0.0` (`round_zero_sign`): `Lowering.zeroTemplate`, written and proved by
  -- hand (`Lowering.fround_agree`), as the tactic's proof is slower.
  | .fround => some (.expr Lowering.froundTemplate (Lean.mkConst ``Lowering.froundTemplate)
      "round: 0.0 for a negative value that rounds to zero")
  | .froundEven => some (.expr Lowering.froundEvenTemplate
      (Lean.mkConst ``Lowering.froundEvenTemplate)
      "round_even: 0.0 for a negative value that rounds to zero")
  | .fceil => some (.expr Lowering.fceilTemplate (Lean.mkConst ``Lowering.fceilTemplate)
      "ceil: 0.0 for a negative value that rounds to zero")
  -- A `DECIMAL(p, p)` prints without its integer part (`.500`), so `dtextFull` has no native
  -- symbol: its only lowering is the text of the decimal widened by one digit (D72, ruling 245
  -- E2, `Lowering.dtextFull_agree`). The regen excludes it from the native search.
  | .dtextFull => some (.expr Lowering.dtextFullTemplate (Lean.mkConst ``Lowering.dtextFullTemplate)
      "dtext of the decimal widened by one digit")
  -- DuckDB's `CAST(x AS BIGINT)` of a double rounds half to even (duckdb-R9): the
  -- value is truncated first, `CEIL` below zero and `FLOOR` elsewhere
  -- (`Lowering.ftoi_agree`, ruling 284 D2).
  | .ftoi => some (.expr Lowering.ftoiTemplate (Lean.mkConst ``Lowering.ftoiTemplate)
      "CAST(x AS BIGINT) of x truncated first (DuckDB's cast rounds half to even)")
  | .ftoiOrNull => some (.expr Lowering.ftoiOrNullTemplate (Lean.mkConst ``Lowering.ftoiOrNullTemplate)
      "TRY_CAST(x AS BIGINT) of x truncated first (DuckDB's cast rounds half to even)")
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
      "CASE WHEN ((('-inf' < #0 AND #0 < 0) AND (('-inf' < #1 AND #1 < 'inf') AND NOT (ffloor(#1) = #1))) OR (#0 = '-inf' AND (('-inf' < #1 AND #1 < 'inf') AND NOT (ffloor(#1) = #1)))) THEN error('domain error', #1) ELSE fpow(#0, #1) END")
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
def duckdbSchemas : Schemas :=
  { un := schema?, bin := schemaBin?, entries := [(``UnFn.dtrunc, ``Lowering.dtruncEntry)] }

end Substrait.LoweringSearch
