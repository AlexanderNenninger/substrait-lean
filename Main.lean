import SubstraitCheck
import Sverify.DuckDB.Boxes

/-! `substrait-check`, over this repository's engine profiles. The modes are
`SubstraitCheck.lean`'s. -/

-- The checker runs with DuckDB's black boxes, the only engine package that has any (#1189).
open scoped Substrait.DuckDB in
def main (args : List String) : IO UInt32 :=
  Substrait.Checker.checkerMain Substrait.builtinEngines args
