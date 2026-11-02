import SubstraitLean.LoweringSearch

/-!
# The generated lowering to DuckDB (#241)

`generate_lowering` builds a table for DuckDB's profile under each setting of
`error_on_division_by_zero`. Every function is native but two. Division and
modulus by zero with the setting off get the guard `CASE WHEN x IS NOT NULL AND
y = 0 THEN error() ELSE x / y END`, which the search finds. `overflow` =
`SATURATE` (`UnFn.fit`) gets a `CASE` clamping to the width's bounds, which the
search finds too, and `SILENT` the hand-written wrap-around schema
(`LoweringSearch.schema?`), proved per width.

Its correctness (`Lowering.duckdb_exact`, `Rel.duckdb_shim_sound`) follows
from the generic theorems of `SubstraitLean/Lowering.lean`. `duckdbOff.coverage`
and `duckdbOn.coverage` list how each construct is lowered; the golden test
`tests/lowering/duckdb.expected` records them (`substrait-check
--lowering-coverage`), so a change to the generator's output shows in review.
-/

namespace Substrait

/-! ### `overflow` = `SILENT` or `SATURATE` (#241)

DuckDB has no function for `UnFn.fit`: its profile computes it as the
reference does, but the SQL printer has nothing to print, so every template
must avoid it (`excluding`). These lemmas let the proofs compute it. -/

theorem Lowering.ref_fit (m : OverflowMode) (w : IntWidth) (x : Value) :
    Profile.reference.un (.fit m w) x = .ok (UnFn.apply (.fit m w) x) := by
  cases x <;> rfl

theorem Lowering.apply_fit_int (m : OverflowMode) (w : IntWidth) (i : Int) :
    UnFn.apply (.fit m w) (.int i) = .int (w.fit m i) := rfl
theorem Lowering.apply_fit_null (m : OverflowMode) (w : IntWidth) :
    UnFn.apply (.fit m w) .null = .null := rfl
theorem Lowering.apply_fit_bool (m : OverflowMode) (w : IntWidth) (b : Bool) :
    UnFn.apply (.fit m w) (.bool b) = .bool b := rfl
theorem Lowering.apply_fit_str (m : OverflowMode) (w : IntWidth) (s : String) :
    UnFn.apply (.fit m w) (.str s) = .str s := rfl
theorem Lowering.apply_fit_list (m : OverflowMode) (w : IntWidth) (vs : List Value) :
    UnFn.apply (.fit m w) (.list vs) = .list vs := rfl

generate_lowering duckdbOff : Profile.duckdb { errorOnDivZero := false }
  unfolding [Profile.duckdb, duckBin, duckUn, duckZero, duckShl, nanCase, isInfCode,
    FMath.inDomain, FMath.lo?, FMath.hi?, FMath.apply, domainIssue, nanIssue]
  using [Lowering.ref_fit, Lowering.apply_fit_int, Lowering.apply_fit_null, Lowering.apply_fit_bool,
    Lowering.apply_fit_str, Lowering.apply_fit_list, IntWidth.fit, IntWidth.lo, IntWidth.hi,
    IntWidth.half, IntWidth.modulus, Lowering.tmod_add_tmod, Profile.duckdb_imod_pos,
    Lowering.shl_apply, Lowering.shr_apply, Int.reduceToNat, Nat.reducePow,
    Lowering.apply_ffloor_int, Lowering.apply_ffloor_null, Lowering.apply_ffloor_bool,
    Lowering.apply_ffloor_str, Lowering.apply_ffloor_list]
  excluding [UnFn.fit]

generate_lowering duckdbOn : Profile.duckdb { errorOnDivZero := true }
  unfolding [Profile.duckdb, duckBin, duckUn, duckZero, duckShl, nanCase, isInfCode,
    FMath.inDomain, FMath.lo?, FMath.hi?, FMath.apply, domainIssue, nanIssue]
  using [Lowering.ref_fit, Lowering.apply_fit_int, Lowering.apply_fit_null, Lowering.apply_fit_bool,
    Lowering.apply_fit_str, Lowering.apply_fit_list, IntWidth.fit, IntWidth.lo, IntWidth.hi,
    IntWidth.half, IntWidth.modulus, Lowering.tmod_add_tmod, Profile.duckdb_imod_pos,
    Lowering.shl_apply, Lowering.shr_apply, Int.reduceToNat, Nat.reducePow,
    Lowering.apply_ffloor_int, Lowering.apply_ffloor_null, Lowering.apply_ffloor_bool,
    Lowering.apply_ffloor_str, Lowering.apply_ffloor_list]
  excluding [UnFn.fit]

/-- The generated lowering to DuckDB under settings `s`, with IEEE operations
(`ieee_floating_point_ops`, DuckDB's default). -/
def Lowering.duckdb : (s : DuckDBSettings) → s.ieeeOps = true → Lowering (Profile.duckdb s)
  | ⟨false, true⟩, _ => duckdbOff
  | ⟨true, true⟩, _ => duckdbOn

theorem Lowering.duckdb_total : ∀ s h, (Lowering.duckdb s h).Total
  | ⟨false, true⟩, _ => duckdbOff.total
  | ⟨true, true⟩, _ => duckdbOn.total

/-- **Every lowered expression is exact on DuckDB.** -/
theorem Lowering.duckdb_exact (s : DuckDBSettings) (h : s.ieeeOps = true) (e : Expr) :
    Expr.Exact (Profile.duckdb s) ((Lowering.duckdb s h).lowerE e) e :=
  Lowering.lowerE_exact (Lowering.duckdb_total s h) e

/-- **The lowered plan runs correctly on DuckDB, or raises.** Unless one of
its expressions raises on a row DuckDB evaluates it on, DuckDB's functions
give `Rel.eval`'s rows, on every catalog and under any settings: no contract
and no guard elimination needed. Trusted, as for `Rel.duckdb_sound`: that
`Profile.duckdb` is DuckDB's, and that the SQL printer is faithful. -/
theorem Rel.duckdb_shim_sound (s : DuckDBSettings) (hi : s.ieeeOps = true) {cat : Catalog} {r : Rel}
    (h : ¬((Lowering.duckdb s hi).lowerRel r).Raises (Profile.duckdb s) cat) :
    ((Lowering.duckdb s hi).lowerRel r).evalI (Profile.duckdb s).impl cat = r.eval cat :=
  Lowering.lowerRel_sound (Lowering.duckdb_total s hi) h

end Substrait
