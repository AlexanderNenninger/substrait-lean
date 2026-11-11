import Lake
open Lake DSL

/-! DuckDB's Lean half (#1189, step 5): `Profile.duckdb` under its settings,
the SQL printer's model and its soundness, the black boxes and the casts from
VARCHAR, its choice table, its lowering (the generated entries and the
lemmas they compute with), `Engine.duckdb`, and the lift from DuckDB's SQL
(its generator and generated entries). It imports only the core, the
analysis, the frontend and engines-common. A standalone `lake build --wfail`
here is the guard (CI runs it). -/

/-- `check_generated`, as in the root lakefile: `lake -R
-Kcheck_generated=true build` here, or the root's own option, which it passes
on (`require … with`), checks the generated entries' proofs; a plain build
takes them as proved (`engines/Sverify/Engines/Generated.lean`). -/
def checkGenerated : Bool := get_config? check_generated == some "true"

package «sverify-duckdb»

require «sverify-core» from "../../core"
require «sverify-analysis» from "../../analysis"
require «sverify-frontend» from "../../frontend"
require «sverify-engines» from "../../engines"

@[default_target]
lean_lib SverifyDuckDB where
  roots := #[`Sverify.DuckDB]

/-- The generated lowering and lift, which `check_generated` applies to. Declared after
`SverifyDuckDB`: Lake gives a module to the last library that contains it. -/
lean_lib SverifyDuckDBGenerated where
  roots := #[]
  globs := #[.submodules `Sverify.DuckDB.LoweringOn,
    .submodules `Sverify.DuckDB.Lift.Duckdb, .submodules `Sverify.DuckDB.Lift.Reference]
  leanOptions := #[⟨`weak.substrait.checkGenerated, checkGenerated⟩]
