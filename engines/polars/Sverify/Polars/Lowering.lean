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
without IEEE's `-0.0` (`Lowering.froundTemplate`), the truncating `//` and
`%` from Polars's floored ones (`Polars.idivTemplate`, `Polars.imodTemplate`),
and a decimal cast to a smaller scale rounded half away from zero from
Polars's truncation (`Polars.droundEntry`), `<<` and `>>` in Polars's 64-bit
functions (`Polars.shlTemplate`, `Polars.shrTemplate`), and a product of
decimals under a guard that raises before Polars's Int128 `*` could leave 128
bits (`Polars.dmulEntry`, the one entry that is not exact,
`Lowering.polars_exact_except`); elsewhere the native function. A
double cast to a decimal has no entry (ruling 278). `%` of doubles floors and has no exact
template: the table is partial, and `Lowering.lowerRel?` refuses a plan that
calls it, naming it.

Its correctness (`Lowering.polars_exact`, `Rel.polars_lowered_sound`) follows
from the generic theorems of `engines/Sverify/Engines/Lowering.lean`.
`polarsOn.coverage` lists how each construct is lowered; the golden test
`tests/lowering/polars.expected` records them (`substrait-check
--lowering-coverage-polars`). The translation runs the table through its
interpreter (`sverify_polars/lowering.py`), and `Engine.polars` lowers a plan
with it (`engines/polars/Sverify/Polars/Engine.lean`).
-/

namespace Substrait

variable [Boxes.Ambient]

/-- The generated lowering to Polars. -/
def Lowering.polars : Lowering Profile.polars := polarsOn

/-- **The entries that are not exact** (ruling 282): the product of decimals
alone (`Polars.dmulEntry`), whose guard raises where its Int128 product could
leave 128 bits. -/
theorem Lowering.polars_exact_except :
    (∀ f, (Lowering.polars.un f).all (·.exact) = true) ∧
      ∀ f, (Lowering.polars.bin f).all (·.exact) = true ∨ f = .dmul :=
  ⟨fun f => by cases f <;> repeat (first | rfl | (rename_i a; cases a)),
   fun f => by cases f <;> repeat (first | exact .inl rfl | exact .inr rfl | (rename_i a; cases a))⟩


/-- No entry is stated on doubles only (`Lowering.NoneOnDbl`). -/
theorem Lowering.polars_noneOnDbl : Lowering.polars.NoneOnDbl :=
  ⟨fun f => by cases f <;> repeat (first | rfl | (rename_i a; cases a)),
   fun f => by cases f <;> repeat (first | rfl | (rename_i a; cases a))⟩

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
