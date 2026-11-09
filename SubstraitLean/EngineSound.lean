import SubstraitLean.Engine
import Sverify.Engines.Sound

/-!
# DuckDB's run is sound (#900)

`Engine.Sound` and guard elimination's side condition are engines-common
(`engines/Sverify/Engines/Sound.lean`), with `Engine.reference_sound` and
the contract theorems; Polars's and Spark's are `Engine.polars_sound` and
`Engine.spark_sound`, in their packages. Here `Engine.duckdb_sound`: DuckDB at
its default settings, through its lowering (`Rel.eval_okImpl`, then
`Rel.duckdb_shim_allowed`).
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

end Substrait
