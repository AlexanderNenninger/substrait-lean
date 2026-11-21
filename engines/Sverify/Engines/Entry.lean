import Lean.Elab.Term
import Sverify.Engines.Sound
import Sverify.Engines.Tables

/-!
# The checker's registry entry for an engine (#1443)

The checker is built over a list of `EngineEntry`s (`checkerMain`). An entry
holds the engine (`Engine`), the side condition its run is sound under, and
the proof `Engine.Sound` of that: a term, so an entry whose theorem does not
state its engine's soundness does not type-check. `engine_entry% thm` writes
an entry from the theorem alone: the engine and the side condition are read
off its type, `soundName`, the name the checker reports (`--realizability`'s
`"theorem"`), from the same identifier, so the name and the proof cannot
differ, and `sideName` (`"side"`) from the side condition, which must be a
named predicate. The side condition is part of what an entry states: every
engine is sound under some side (`fun _ _ => False`), so the checker prints
which one.

The tables the checker reports are derived from the entry once
(`EngineEntry.rows`): the engine's choices and its rows with what reruns
give (`withReruns`). An engine and its proofs hold for every black-box
catalogue (`Boxes.Ambient`); its tables do not depend on one, and are read at
`Boxes.Ambient.none`.

A package with an engine of its own requires this repository, proves its
engine sound, and builds a checker over `builtinEntries ++ [its entry]`
(`SubstraitCheckExamples/DummyEngine.lean` is the file it copies).
-/

namespace Substrait

/-- An engine as the checker is built with it: the engine, the side
condition under which its run is sound, and the proof of that. -/
structure EngineEntry where
  engine : ∀ [Boxes.Ambient], Engine
  side : ∀ [Boxes.Ambient], Catalog → Rel → Prop
  sound : ∀ [Boxes.Ambient], engine.Sound side
  /-- The theorem `sound` is, by name: written by `engine_entry%` from the
  same identifier as the term. -/
  soundName : Lean.Name
  /-- The named predicate `side` is, applied or not (`Engine.NoRaiseSide`,
  `Engine.GuardFreeSide`): written by `engine_entry%` from `sound`'s type. -/
  sideName : Lean.Name
  /-- Each shim of the engine's rows, by name, with its cost. -/
  shims : List (String × ShimCost) := []
  /-- Where the engine executes, as `--options` reports it (`"streaming"`,
  `"batch"`), or empty. -/
  executes : String := ""
  /-- Do the engine's doubles call the reference's `libm`? (`EngineProfile.sameLibm`) -/
  sameLibm : Bool := true
  /-- The engine's elementary functions that are not the reference's, S + R in ulps
  (`EngineProfile.elemUlps`). -/
  elemUlps : List (String × Rat) := []

open Lean Elab Term Meta in
/-- `engine_entry% thm`: the entry whose proof is `thm`, with `soundName` the
constant `thm` resolves to and `sideName` the head of the side condition in
its type, which must be a named predicate. The engine and the side condition
are unified from `thm`'s type. -/
elab "engine_entry% " thm:ident : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo thm
  let side? ← forallTelescope (← getConstInfo n).type fun _ body => do
    let body ← whnfR body
    unless body.isAppOf ``Engine.Sound do
      throwError "engine_entry%: {n} does not state `Engine.Sound`"
    return body.getAppArgs.back!.getAppFn.constName?
  let some side := side? | throwError
    "engine_entry%: the side condition of {n} is no named predicate; state it as a definition"
  let stx ← `(EngineEntry.mk _ _ @$(mkCIdent n) $(quote n) $(quote side) [] "" true [])
  elabTermEnsuringType stx (some (mkConst ``EngineEntry))

/-- A name as the checker reports it, without the `Substrait` namespace. -/
def reportedName (n : Lean.Name) : String :=
  (n.replacePrefix `Substrait .anonymous).toString

/-- The tables the checker reports for `e`: the engine's choices, and its
observation rows with what reruns give. They are read at
`Boxes.Ambient.none`: an engine's table and rows do not depend on the
black-box catalogue (the built-in ones' do not), while its proof holds for
every catalogue. -/
def EngineEntry.rows (e : EngineEntry) : EngineProfile :=
  letI := Boxes.Ambient.none
  { table := e.engine.table, obs := withReruns e.engine.obs, shims := e.shims,
    executes := e.executes, sameLibm := e.sameLibm, elemUlps := e.elemUlps }

def EngineEntry.name (e : EngineEntry) : String := e.rows.name

end Substrait
