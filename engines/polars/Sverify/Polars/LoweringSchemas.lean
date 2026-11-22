import Sverify.Engines.LoweringSearch
import Sverify.Polars.LoweringLemmas

/-!
# Polars's hand-written template schemas (#271)

The constructs the lowering search does not reach on `Profile.polars`, for
`generate_lowering … hand_written polarsSchemas`
(`scripts/RegenLoweringPolars.lean`): `round` and `ceil`, which give IEEE's
`-0.0` on Polars, and integer `//` and `%`, which floor. Each comes with its
proof, `Polars.<construct>_agree` (`Sverify.Polars.LoweringLemmas`,
`Sverify.Polars.Profile`), which the kernel checks. `%` of doubles floors too
and has no exact template from Polars's functions: the table has no entry
for it, and `Lowering.lowerRel?` refuses a plan that calls it.
-/

namespace Substrait.LoweringSearch

open Lean

/-- **Polars's schemas.** -/
def polarsSchemas : Schemas where
  un
    | .fround => some (.expr Lowering.froundTemplate (mkConst ``Lowering.froundTemplate)
        "round: 0.0 for a negative value that rounds to zero")
    | .froundEven => some (.expr Lowering.froundEvenTemplate (mkConst ``Lowering.froundEvenTemplate)
        "round(mode='half_to_even'): 0.0 for a negative value that rounds to zero")
    | .fceil => some (.expr Lowering.fceilTemplate (mkConst ``Lowering.fceilTemplate)
        "ceil: 0.0 for a negative value that rounds to zero")
    | _ => none
  bin
    | .idiv => some (.expr Polars.idivTemplate (mkConst ``Polars.idivTemplate)
        "a // b truncated, from Polars's floored // of operands of one sign")
    | .imod => some (.expr Polars.imodTemplate (mkConst ``Polars.imodTemplate)
        "a % b truncated: Polars's % by -b where the signs differ")
    | _ => none
  proofs := `Substrait.Polars

end Substrait.LoweringSearch
