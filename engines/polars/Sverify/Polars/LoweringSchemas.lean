import Sverify.Engines.LoweringSearch
import Sverify.Polars.LoweringLemmas

/-!
# Polars's hand-written template schemas (#271)

The constructs the lowering search does not reach on `Profile.polars`, for
`generate_lowering … hand_written polarsSchemas`
(`scripts/RegenLoweringPolars.lean`): `round` and `ceil`, which give IEEE's
`-0.0` on Polars, integer `//` and `%`, which floor, and a decimal cast to a
smaller scale, which rounds half to even (a hand-built entry, `Polars.droundEntry`,
whose template's literals depend on the scale), and `<<` and `>>`, which Polars
lacks (polars-int-shift). Each comes with its
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
    | .bit .and => some (.expr Polars.bitAndT (mkConst ``Polars.bitAndT) "native: #0 & #1")
    | .bit .or => some (.expr Polars.bitOrT (mkConst ``Polars.bitOrT) "native: #0 | #1")
    | .bit .xor => some (.expr Polars.bitXorT (mkConst ``Polars.bitXorT) "native: #0 ^ #1")
    | .bit .shl => some (.expr Polars.shlTemplate (mkConst ``Polars.shlTemplate)
        "shl: error outside 0-63, else the low 63-k bits of #0 & -1 times 2^k, the next bit the sign")
    | .bit .shr => some (.expr Polars.shrTemplate (mkConst ``Polars.shrTemplate)
        "shr: error outside 0-63, else (#0 & -1) // 2^#1 floored")
    | _ => none
  proofs := `Substrait.Polars
  entries := [(``UnFn.dround, ``Polars.droundEntry)]

end Substrait.LoweringSearch
