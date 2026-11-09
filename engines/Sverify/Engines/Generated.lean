import Lean

/-!
# Checking the generated tables (`check_generated`)

The DuckDB lowering (`SubstraitLean/LoweringDuckDB/On`) and the lift
(`SubstraitLean/LiftDuckDB/Duckdb`, `Reference`) are generated modules: each
entry is a theorem whose proof the generator wrote out, which takes most of a
cold build to check. The lakefile's `check_generated` option sets
`substrait.checkGenerated` for those modules only:

* `lake -R -Kcheck_generated=true build` (CI, the Wheels workflow, `poe qa`,
  the wheel's build hook) checks every proof;
* a plain `lake build` (the default for local builds) takes the entries as
  data and closes their proofs with `sorry`, so the tables, their templates and
  the staleness checks (`#guard`) are the same and a local build is quick.

A theorem proved this way depends on `sorryAx` (`#print axioms` shows it), so
a local build proves nothing about the generated entries; CI does. Outside
those modules the option is unset and every proof is checked, which is what
the regeneration scripts (`poe regen-lowering`, `poe regen-lift`) rely on.
-/

namespace Substrait.Generated

open Lean Elab Command Tactic Meta

register_option substrait.checkGenerated : Bool := {
  defValue := true
  descr := "check the proofs of the generated lowering and lift entries \
    (off: `lake build` without `-Kcheck_generated=true` takes them as proved)"
}

/-- Whether this module checks its generated entries' proofs. -/
def checked [Monad m] [MonadOptions m] : m Bool :=
  return substrait.checkGenerated.get (← getOptions)

/-- Run `tac`, or, with `check_generated` off, close the main goal unchecked. -/
def proveOrAdmit (tac : TacticM Unit) : TacticM Unit := do
  if ← checked then tac
  else
    let g ← getMainGoal
    g.assign (← mkSorry (← g.getType) (synthetic := true))
    replaceMainGoal []

/-- The first command of a generated module: with `check_generated` off, the
entries' unchecked proofs (`proveOrAdmit`) don't each warn that they use
`sorry`. It silences the warning for the rest of the module, which holds
generated entries only; outside the generated modules nothing changes. -/
syntax (name := generatedEntries) "generated_entries" : command

@[command_elab generatedEntries] def elabGeneratedEntries : CommandElab := fun _ => do
  unless ← checked do
    modifyScope fun s => { s with opts := s.opts.setBool `warn.sorry false }

/-- Fail in a search run with `check_generated` off: a search must check
every proof it finds. -/
def requireChecked [Monad m] [MonadOptions m] [MonadError m] (what : String) : m Unit := do
  unless ← checked do
    throwError "{what} needs substrait.checkGenerated on: a search checks every proof it writes"

end Substrait.Generated
