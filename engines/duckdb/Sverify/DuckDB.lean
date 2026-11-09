import Sverify.DuckDB.Boxes
import Sverify.DuckDB.Functions
import Sverify.DuckDB.LoweringLemmas
import Sverify.DuckDB.Profile
import Sverify.DuckDB.SQL
import Sverify.DuckDB.Tables
import Sverify.DuckDB.VarcharCasts

/-! DuckDB's Lean half (#1189, step 5): its functions under its settings, the
SQL printer's model and its soundness, the black boxes, its table and the
lowering's lemmas. It imports only the core, the analysis and engines-common,
which the standalone build of this package checks. -/
