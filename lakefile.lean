import Lake
open Lake DSL

/-- `lake -R -Kcheck_generated=true build` checks the proofs of the generated
lowering and lift entries; a plain `lake build` takes them as proved, which
saves most of a cold build (`engines/Sverify/Engines/Generated.lean`). CI, the Wheels
workflow, `poe qa` and the wheel's build hook set it, so every PR and every
release checks every entry. `-R` is needed whenever the value changes: Lake
keeps the configuration of the last `-R`. -/
def checkGenerated : Bool := get_config? check_generated == some "true"

package «substrait-lean»

require «sverify-core» from "core"
require «sverify-analysis» from "analysis"
require «sverify-frontend» from "frontend"
require «sverify-engines» from "engines"
require «sverify-polars» from "engines/polars"
require «sverify-spark» from "engines/spark"
/-- DuckDB's package holds the generated modules (`Sverify.DuckDB.LoweringOn`,
`Sverify.DuckDB.Lift`), and reads `check_generated` from the options it is
required with. -/
require «sverify-duckdb» from "engines/duckdb" with
  NameMap.empty.insert `check_generated (if checkGenerated then "true" else "false")

@[default_target]
lean_lib SubstraitLean

/- Across packages a library claims every module under its root's prefix,
which is why each package has a root of its own (`Sverify.Core`,
`Sverify.Analysis`, `Sverify.Frontend`, `Sverify.Engines`, `Sverify.DuckDB`,
`Sverify.Polars`, `Sverify.Spark`) and none is rooted at `Sverify` alone. The
generated modules (the lowering and the lift) are DuckDB's package's, which
applies `check_generated` to them. -/

/-- The checker's modes as a library, `Substrait.Checker.checkerMain`, so a
package with an engine profile of its own can build a checker over
`builtinEngines ++ [its profile]`. -/
lean_lib SubstraitCheck

/-- An engine profile added from outside, as another package adds one: a
test, built by `lake build`, not part of `substrait-check`. -/
@[default_target]
lean_lib SubstraitCheckExamples where
  globs := #[.submodules `SubstraitCheckExamples]

@[default_target]
lean_exe «substrait-check» where
  root := `Main
