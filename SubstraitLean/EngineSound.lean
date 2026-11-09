import SubstraitLean.Engine
import Sverify.Engines.Sound

/-!
# DuckDB's and Spark's runs are sound (#900)

`Engine.Sound` and guard elimination's side condition are engines-common
(`engines/Sverify/Engines/Sound.lean`), with `Engine.reference_sound` and
the contract theorems; Polars's is `Engine.polars_sound`
(`SubstraitLean/PolarsEngine.lean`). Here:

* `Engine.duckdb_sound`: DuckDB at its default settings, through its lowering
  (`Rel.eval_okImpl`, then `Rel.duckdb_shim_allowed`).
* `Engine.spark_sound`: under `Engine.GuardFreeSide`, with Spark's functions
  faithful where the reference reports no issue
  (`Profile.sparkWritten_okImpl_faithful`).
-/

namespace Substrait

variable [Boxes.Ambient]

/-- DuckDB at its default settings: where the lowered plan does not raise,
`okImpl` computes DuckDB's run (`Rel.eval_okImpl`), which the reference
allows (`Rel.duckdb_shim_allowed`). -/
theorem Engine.duckdb_sound : (Engine.duckdb {} rfl).Sound fun _ _ => True := by
  intro cat r r' hl hr _
  cases hl
  show r.Allowed cat ((Lowering.duckdb.lowerRel r).eval cat (Profile.duckdb {}).okImpl)
  rw [Rel.eval_okImpl (p := Profile.duckdb {}) hr]; exact Rel.duckdb_shim_allowed hr

/-- Spark: its profile's functions where they do not raise give the
reference's value wherever the reference reports no issue
(`Profile.sparkWritten_okImpl_faithful`), so guard elimination applies. -/
theorem Engine.spark_sound : Engine.spark.Sound Engine.GuardFreeSide := by
  intro cat r r' hl _ ⟨_, _, _, ⟨hcat, hA, hF, hT, hsmall⟩, hwf, hs, hm⟩
  cases hl
  exact Rel.guardFree_allowed hcat hA hF hT hwf hsmall hs hm Profile.sparkWritten_okImpl_faithful

end Substrait
