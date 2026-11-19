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
off its type, and `soundName`, the name the checker reports
(`--realizability`'s `"theorem"`), from the same identifier, so the name and
the proof cannot differ.

The tables the checker reports are derived from the entry once
(`EngineEntry.profile`): the engine's choices and its rows with what reruns
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
  /-- Each shim of the engine's rows, by name, with its cost. -/
  shims : List (String × ShimCost) := []
  /-- Where the engine executes, as `--options` reports it (`"streaming"`,
  `"batch"`), or empty. -/
  executes : String := ""

open Lean Elab Term in
/-- `engine_entry% thm`: the entry whose proof is `thm`, with `soundName` the
constant `thm` resolves to. The engine and its side condition are unified
from `thm`'s type. -/
elab "engine_entry% " thm:ident : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo thm
  let stx ← `(EngineEntry.mk _ _ @$(mkCIdent n) $(quote n) [] "")
  elabTermEnsuringType stx (some (mkConst ``EngineEntry))

/-- The theorem's name as the checker reports it, without the `Substrait`
namespace (`Engine.duckdb_sound`). -/
def EngineEntry.theoremName (e : EngineEntry) : String :=
  (e.soundName.replacePrefix `Substrait .anonymous).toString

/-- The tables the checker reports for `e`: the engine's choices, and its
observation rows with what reruns give. -/
def EngineEntry.profile (e : EngineEntry) : EngineProfile :=
  letI := Boxes.Ambient.none
  { table := e.engine.table, obs := withReruns e.engine.obs, shims := e.shims,
    executes := e.executes }

def EngineEntry.name (e : EngineEntry) : String := e.profile.name

end Substrait
