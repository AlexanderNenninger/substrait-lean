import SubstraitLean.LoweringSearch

/-!
# The generated lowering to DuckDB (#241)

`generate_lowering` builds a table for DuckDB's profile under each setting of
`error_on_division_by_zero`. Every function is native but division and modulus
by zero with the setting off, where the search finds the guard
`CASE WHEN x IS NOT NULL AND y = 0 THEN error() ELSE x / y END`.

Its correctness (`Lowering.duckdb_exact`, `Rel.duckdb_shim_sound`) follows
from the generic theorems of `SubstraitLean/Lowering.lean`. `duckdbOff.coverage`
and `duckdbOn.coverage` list how each construct is lowered; the golden test
`tests/lowering/duckdb.expected` records them (`substrait-check
--lowering-coverage`), so a change to the generator's output shows in review.
-/

namespace Substrait

generate_lowering duckdbOff : Profile.duckdb { errorOnDivZero := false }
  unfolding [Profile.duckdb, BinFn.divides, duckDivZero]

generate_lowering duckdbOn : Profile.duckdb { errorOnDivZero := true }
  unfolding [Profile.duckdb, BinFn.divides, duckDivZero]

/-- The generated lowering to DuckDB under settings `s`. -/
def Lowering.duckdb : (s : DuckDBSettings) → Lowering (Profile.duckdb s)
  | { errorOnDivZero := false } => duckdbOff
  | { errorOnDivZero := true } => duckdbOn

theorem Lowering.duckdb_total : ∀ s, (Lowering.duckdb s).Total
  | { errorOnDivZero := false } => duckdbOff.total
  | { errorOnDivZero := true } => duckdbOn.total

/-- **Every lowered expression is exact on DuckDB.** -/
theorem Lowering.duckdb_exact (s : DuckDBSettings) (e : Expr) :
    Expr.Exact (Profile.duckdb s) ((Lowering.duckdb s).lowerE e) e :=
  Lowering.lowerE_exact (Lowering.duckdb_total s) e

/-- **The lowered plan runs correctly on DuckDB, or raises.** Unless one of
its expressions raises on a row DuckDB evaluates it on, DuckDB's functions
give `Rel.eval`'s rows, on every catalog and under any settings: no contract
and no guard elimination needed. Trusted, as for `Rel.duckdb_sound`: that
`Profile.duckdb` is DuckDB's, and that the SQL printer is faithful. -/
theorem Rel.duckdb_shim_sound (s : DuckDBSettings) {cat : Catalog} {r : Rel}
    (h : ¬((Lowering.duckdb s).lowerRel r).Raises (Profile.duckdb s) cat) :
    ((Lowering.duckdb s).lowerRel r).evalI (Profile.duckdb s).impl cat = r.eval cat :=
  Lowering.lowerRel_sound (Lowering.duckdb_total s) h

end Substrait
