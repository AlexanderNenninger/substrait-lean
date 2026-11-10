import Sverify.Engines.Lowering

/-!
# Known lowerings: the generator's cache (#241, #242)

A hint tells `generate_lowering` (`engines/Sverify/Engines/LoweringSearch.lean`) which
template to try first for one construct of one table. It is only a hint: the
template is one of the generator's own candidates, found by how it prints, and
is tested on the samples and proved by the kernel like any other; if it no
longer proves, the hand-written schema and the search run as without it. So a
stale hint can make a build slower, never an entry wrong.

`engines/duckdb/Sverify/DuckDB/LoweringCache.lean` holds the hints, so that a build (CI's
included) proves each construct's known template at once instead of searching
for it. `substrait-check --lowering-cache` prints a new one from a build's
coverage: each construct's template as the coverage report shows it, and, for
one without an entry, why it failed (the breadcrumb to start from).
-/

namespace Substrait

/-- One known lowering: in table `table`, the construct `construct` (as the
coverage report labels it) is lowered to `template` (as it prints there:
`native`, or the template, a hand-written schema prefixed); empty if none is
known, with `note` saying why. -/
structure LoweringHint where
  table : String
  construct : String
  template : String
  note : String := ""
  deriving Repr, Inhabited

end Substrait
