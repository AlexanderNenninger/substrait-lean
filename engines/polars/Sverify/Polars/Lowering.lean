import Sverify.Engines.LoweringExport
import Sverify.Polars.LoweringOn.Table

/-!
# The generated lowering to Polars (#271)

The table for Polars's profile, `polarsOn`, is generated: the search
(`generate_lowering`, `engines/Sverify/Engines/LoweringSearch.lean`) runs in
`scripts/RegenLoweringPolars.lean` (`poe regen-lowering`) and writes each entry
it found, with its proof, to `engines/polars/Sverify/Polars/LoweringOn`, which a
build checks without searching. Where `Profile.polars` differs from the
reference, an entry is a template over Polars's functions: `round` and `ceil`
without IEEE's `-0.0` (`Lowering.froundTemplate`), and the truncating `//` and
`%` from Polars's floored ones (`Polars.idivTemplate`, `Polars.imodTemplate`);
elsewhere the native function. `%` of doubles floors and has no exact
template: the table is partial, and `Lowering.lowerRel?` refuses a plan that
calls it, naming it.

Its correctness (`Lowering.polars_exact`, `Rel.polars_lowered_sound`) follows
from the generic theorems of `engines/Sverify/Engines/Lowering.lean`.
`polarsOn.coverage` lists how each construct is lowered; the golden test
`tests/lowering/polars.expected` records them (`substrait-check
--lowering-coverage-polars`). Nothing runs the table yet: the translation to
Polars still writes each function by hand (`Polars.written`), and
`engines/polars/tests/test_lowering_agrees.py` checks that the two agree, until
the table's interpreter replaces the hand-written hooks (#271, step 2).
-/

namespace Substrait

variable [Boxes.Ambient]

/-- The generated lowering to Polars. -/
def Lowering.polars : Lowering Profile.polars := polarsOn

theorem Lowering.polars_allExact : Lowering.polars.AllExact := polarsOn.allExact
theorem Lowering.polars_noneOnDbl : Lowering.polars.NoneOnDbl := polarsOn.noneOnDbl

/-- **A lowered expression is exact on Polars**, wherever the table lowers it
(every function but `%` of doubles). -/
theorem Lowering.polars_exact {e : Expr} (he : (Lowering.polars.lower e).isSome) :
    Expr.Exact Profile.polars (Lowering.polars.lowerE e) e :=
  Lowering.lowerE_exact_of _ Lowering.polars_noneOnDbl he

/-- **The lowered plan runs correctly on Polars, or raises.** A plan the table
lowers (`Lowering.lowerRel?`) gives `Rel.eval`'s rows under Polars's
functions, on every catalog, unless one of its expressions raises on a row
Polars evaluates it on. Trusted: that `Profile.polars` is Polars's, and that
the translation writes each template's functions as Polars's. -/
theorem Rel.polars_lowered_sound {cat : Catalog} {r r' : Rel}
    (hr : Lowering.polars.lowerRel? r = .ok r') (h : ¬r'.Raises Profile.polars cat) :
    r'.eval cat Profile.polars.impl = r.eval cat :=
  Lowering.lowerRel?_sound Lowering.polars_noneOnDbl hr h

/-- The Polars table, exported: its entries that are not the native call. -/
def Lowering.polarsTableJson : Lean.Json := LoweringExport.tableJson polarsOn

end Substrait
