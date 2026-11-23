import Sverify.Engines.LoweringGuards
import Sverify.Spark.LoweringLemmas

/-!
# Spark's hand-written template schemas (#271)

The constructs the lowering search does not reach on `Profile.spark`, for
`generate_lowering … hand_written sparkSchemas` (`scripts/RegenLoweringSpark.lean`):

* `+ - * / %` of doubles raise where the reference does: the operands of which
  IEEE 754 makes a NaN (`nanGuard`), where Spark gives NaN. A zero divisor
  raises on Spark under ANSI as in the reference.
* An elementary function raises outside its domain (`fmathGuard`), where
  Spark gives NaN or, for a logarithm, NULL.
* `<<` and `>>` raise outside `0`–`63` (`Spark.shiftTemplate`), and `date_add`
  past the reference's dates (`Spark.dateAddTemplate`), each proved by hand
  (`Spark.bit_shl_agree`, `Spark.dateAdd_agree`).
* `floor` and `ceil` give a `BIGINT` on Spark: hand-built entries exact on
  doubles' codes (`Spark.ffloorEntry`, `onDbl`, ruling 248).
* IEEE division: `/`'s entry, which raises at a zero divisor as Spark does under
  ANSI where IEEE gives `±∞` (`BinEntry.weaken`, `Spark.ref_fdiv_fdivIeee`, not
  exact, ruling 249).

`power` and `atan2` of doubles are Java's, within an ulp of C's: no exact
template, so the table has no entry for them (`refusing`), as the writer
refuses them today (`BinFn.sparkWritten`).
-/

namespace Substrait.LoweringSearch

open Lean

/-- **Spark's schemas.** -/
def sparkSchemas : Schemas where
  un
    | .fmath f => (fmathGuard f).map fun g => .ite g (.raise "domain error" (.field 0)) (.self [.field 0])
    | _ => none
  bin f :=
    let self := Tm.self [.field 0, .field 1]
    match f with
    | .fadd | .fsub | .fmul | .fdiv | .fmod =>
      (nanGuard f).map fun g => .ite g (.raise "domain error" (.field 1)) self
    | .bit .shl => some (.expr Spark.shlTemplate (mkConst ``Spark.shlTemplate) "shl: error outside 0-63")
    | .bit .shr => some (.expr Spark.shrTemplate (mkConst ``Spark.shrTemplate) "shr: error outside 0-63")
    | .dateAdd => some (.expr Spark.dateAddTemplate (mkConst ``Spark.dateAddTemplate)
        "date_add: error past the reference's dates")
    | _ => none
  proofs := `Substrait.Spark
  entries := [(``UnFn.ffloor, ``Spark.ffloorEntry), (``UnFn.fceil, ``Spark.fceilEntry)]
  derived := [(``BinFn.fdivIeee, ``BinFn.fdiv, ``Spark.ref_fdiv_fdivIeee)]

end Substrait.LoweringSearch
