import Lake
open Lake DSL

/-- `lake -R -Kcheck_generated=true build` checks the proofs of the generated
lowering and lift entries; a plain `lake build` takes them as proved, which
saves most of a cold build (`SubstraitLean/Generated.lean`). CI, the Wheels
workflow, `poe qa` and the wheel's build hook set it, so every PR and every
release checks every entry. `-R` is needed whenever the value changes: Lake
keeps the configuration of the last `-R`. -/
def checkGenerated : Bool := get_config? check_generated == some "true"

package «substrait-lean»

@[default_target]
lean_lib SubstraitLean

/-- The generated modules, which `check_generated` applies to. Declared after
`SubstraitLean`: Lake gives a module to the last library that contains it. -/
lean_lib SubstraitLeanGenerated where
  roots := #[]
  globs := #[.submodules `SubstraitLean.LoweringDuckDB.On,
    .submodules `SubstraitLean.LiftDuckDB.Duckdb, .submodules `SubstraitLean.LiftDuckDB.Reference]
  leanOptions := #[⟨`weak.substrait.checkGenerated, checkGenerated⟩]

@[default_target]
lean_exe «substrait-check» where
  root := `Main
