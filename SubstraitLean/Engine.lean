import SubstraitLean.Obligations
import Sverify.DuckDB.Engine
import Sverify.Polars.Engine
import Sverify.Spark.Engine
import SubstraitLean.EngineTables

/-!
# The engines' Engine values, together (#900)

Each engine's `Engine` value and the proofs that its functions are within its
table and that its run is sound are in its package
(`engines/duckdb/Sverify/DuckDB/Engine.lean`,
`engines/polars/Sverify/Polars/Engine.lean`,
`engines/spark/Sverify/Spark/Engine.lean`); the structure and `Engine.Sound`
are engines-common (`engines/Sverify/Engines/Engine.lean`,
`engines/Sverify/Engines/Sound.lean`). This module checks them together.


`Engine.duckdb_noRaise_of_mayIssues` joins the two sides: an empty
`Rel.mayIssues` gives DuckDB's side condition (`Engine.NoRaiseSide`).
-/

namespace Substrait

-- No engine's certificate is empty: each but the reference has rows that
-- are not theorems (so `Refines` is a real hypothesis, which `#print axioms`
-- cannot show).
#guard letI := Boxes.Ambient.none; !(Engine.duckdb {} rfl).testedRows.isEmpty && !Engine.polars.testedRows.isEmpty &&
  !Engine.spark.testedRows.isEmpty && Engine.reference.testedRows.isEmpty

section
variable [Boxes.Ambient]

/-- **No issue, no raise on DuckDB**: where `Rel.mayIssues` finds no issue in
`r`, DuckDB's lowered plan does not raise (`Engine.NoRaiseSide`), so
`Engine.duckdb_sound` applies. It needs `Rel.looseSub`, as
`Rel.hasIssue_of_raises` does. A `SUM` that overflows is no `Rel.Raises` case:
`Rel.Raises` names the expressions evaluated on rows, and an aggregate's
overflow is `Rel.HasIssue`'s own `sumWraps` case. -/
theorem Engine.duckdb_noRaise_of_mayIssues {cat : Catalog} (hcat : cat.WF)
    {A : String → List AVal} {F : String → List Fact}
    (hA : ∀ t, ∀ row ∈ (cat t).rows, EnvMem (A t) row)
    (hF : ∀ t, ∀ row ∈ (cat t).rows, FactsHold (F t) row) {T : WindowKeys} (hT : T.SoundAll cat)
    {r : Rel} (hwf : r.WF cat) (hsm : r.Small cat) (hs : r.looseSub = true)
    (h : r.mayIssues cat A F T false = []) : (Engine.duckdb {} rfl).NoRaiseSide cat r := by
  intro r' hl hr
  cases hl
  obtain ⟨p, hp⟩ := Rel.hasIssue_of_raises false hs (Lowering.lowerRel_raises Lowering.duckdb_total hr)
  have := Rel.mayIssues_sound hcat hA hF hT hwf hsm p hp
  rw [h] at this
  cases this

end

end Substrait
