import Sverify.DuckDB.SQL

/-!
# Known lifts: the generator's cache (#268)

A hint tells `generate_lift` (`SubstraitLean/LiftSearch.lean`) which template
to try first for one DuckDB function under one semantics. It is only a hint:
the template is read by the parser, tested on the samples and proved by the
kernel like any candidate, and if it no longer proves, the search runs as
without it. So a stale hint can make a build slower, never an entry wrong.

`SubstraitLean/LiftCache.lean` holds the hints. `substrait-check --lift-cache`
prints a new one from the tables a build found: each entry's template, where
it came from (`searched`, or `seeded: …` for one written by hand where the
search does not reach), and, for a function without an entry, why its first
candidate failed (the breadcrumb to start from).
-/

namespace Substrait

/-- One known lift. `template` is the Substrait expression's JSON over the
arguments (field references `0`, `1`, …), with each call naming its function
(`"function": "divide:fp64_fp64"`) rather than an anchor, so that the hint
outlives a change to the generator's function list; empty if none is known. -/
structure LiftHint where
  semantics : String
  construct : String
  template : String
  source : String
  note : String := ""
  deriving Repr, Inhabited

end Substrait
