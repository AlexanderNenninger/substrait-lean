import SubstraitLean.LoweringSearch
import SubstraitLean.LoweringCache
import SubstraitLean.LoweringDuckDB.Lemmas

/-!
# Regenerating the DuckDB lowering (`poe regen-lowering`)

Runs the lowering generator's search (`SubstraitLean/LoweringSearch.lean`)
for DuckDB's profile under each setting of `error_on_division_by_zero`, and
writes what it finds, entries and proofs, to `SubstraitLean/LoweringDuckDB/Off`
and `On`. A build checks those modules and never searches; run this when
`Profile.duckdb`, the generator or the model's functions change (a build that
fails in those modules, or `tests/lowering/duckdb.expected`, says so). Not part
of the library: `lake build` does not elaborate it.
-/

namespace Substrait

generate_lowering duckdbOff : Profile.duckdb { errorOnDivZero := false }
  unfolding [Profile.duckdb, duckBin, duckUn, duckZero, duckShl, nanCase, isInfCode,
    FMath.inDomain, FMath.lo?, FMath.hi?, FMath.apply, domainIssue, nanIssue]
  using [Lowering.ref_fit, Lowering.apply_fit_int, Lowering.apply_fit_null, Lowering.apply_fit_bool,
    Lowering.apply_fit_str, Lowering.apply_fit_list, IntWidth.fit, IntWidth.lo, IntWidth.hi,
    IntWidth.half, IntWidth.modulus, Lowering.tmod_add_tmod, Profile.duckdb_imod_pos,
    Lowering.shl_apply, Lowering.shr_apply, Int.reduceToNat, Nat.reducePow,
    Lowering.apply_ffloor_int, Lowering.apply_ffloor_null, Lowering.apply_ffloor_bool,
    Lowering.apply_ffloor_str, Lowering.apply_ffloor_list, Lowering.pow2Chain_eval, List.mem_range]
  excluding [UnFn.fit]
  cache loweringCache
  writing "SubstraitLean/LoweringDuckDB/Off"

generate_lowering duckdbOn : Profile.duckdb { errorOnDivZero := true }
  unfolding [Profile.duckdb, duckBin, duckUn, duckZero, duckShl, nanCase, isInfCode,
    FMath.inDomain, FMath.lo?, FMath.hi?, FMath.apply, domainIssue, nanIssue]
  using [Lowering.ref_fit, Lowering.apply_fit_int, Lowering.apply_fit_null, Lowering.apply_fit_bool,
    Lowering.apply_fit_str, Lowering.apply_fit_list, IntWidth.fit, IntWidth.lo, IntWidth.hi,
    IntWidth.half, IntWidth.modulus, Lowering.tmod_add_tmod, Profile.duckdb_imod_pos,
    Lowering.shl_apply, Lowering.shr_apply, Int.reduceToNat, Nat.reducePow,
    Lowering.apply_ffloor_int, Lowering.apply_ffloor_null, Lowering.apply_ffloor_bool,
    Lowering.apply_ffloor_str, Lowering.apply_ffloor_list, Lowering.pow2Chain_eval, List.mem_range]
  excluding [UnFn.fit]
  cache loweringCache
  writing "SubstraitLean/LoweringDuckDB/On"

end Substrait
