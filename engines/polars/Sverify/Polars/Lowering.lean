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
Polars's truncation (`Polars.droundEntry`); elsewhere the native function. A
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

/-- Every entry is exact (`Lowering.AllExact`): the generator's own proof, which
it leaves to a table with a hand-built entry (`Polars.droundEntry`). -/
theorem Lowering.polars_allExact : Lowering.polars.AllExact :=
  ⟨fun f => by cases f <;> repeat (first | rfl | (rename_i a; cases a)),
   fun f => by cases f <;> repeat (first | rfl | (rename_i a; cases a))⟩

-- The hand-written entries are in the table, not the native call: a regeneration
-- that drops `excluding [BinFn.bit]` (`scripts/RegenLoweringPolars.lean`) would
-- make Polars's shifts, which it lacks, native again, and fails here.
#guard letI := Boxes.Ambient.none
  (Lowering.polars.bin (.bit .shl)).any (·.tmpl == Polars.shlTemplate) &&
    (Lowering.polars.bin (.bit .shr)).any (·.tmpl == Polars.shrTemplate)

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

/-- **What Polars's rendering of a function asks for** (ruling 282's C8, M4): the
option and the behaviour its call states, written once. `round` is rendered
`round(0, mode="half_away_from_zero")`, Polars's own function with its mode
argument, which `Profile.polars` states (`Polars.negZeroT .fround`) and
`sverify_polars.lowering` reads from this list (`--lowering-table`'s
`"polars_asks"`). -/
def Polars.asks : List (Functions.Ctor × String × Behaviour) :=
  [(.un .fround, "rounding", "TIE_AWAY_FROM_ZERO")]

-- Each ask is a behaviour Polars gives when asked, and the reference's (M2): the
-- table and the rendering agree.
#guard Polars.asks.all fun (c, o, b) => match Functions.rowOf c with
  | some r => Profile.polars.table.allows r.group o [b] == [b] &&
      Profile.reference.table.allows r.group o [] == [b]
  | none => false

/-- `Polars.asks` for Python: each function's name as the templates write it. -/
def Lowering.polarsAsksJson : Lean.Json :=
  Lean.Json.arr (Polars.asks.toArray.map fun (c, o, b) => Lean.Json.mkObj [
    ("fn", Lean.Json.str (match c with
      | .un f => LoweringExport.unName f | .bin f => LoweringExport.binName f | _ => "")),
    ("option", Lean.Json.str o), ("behaviour", Lean.Json.str b)])

end Substrait
