import SubstraitLean.LoweringSearch
import SubstraitLean.LoweringCache
import SubstraitLean.LoweringDuckDB.Lemmas
import SubstraitLean.LoweringDuckDB.Schemas

/-!
# Regenerating the DuckDB lowering (`poe regen-lowering`)

Runs the lowering generator's search (`SubstraitLean/LoweringSearch.lean`)
for DuckDB's profile under its default settings, and writes what it finds,
entries and proofs, to `SubstraitLean/LoweringDuckDB/On`. A build checks those
modules and never searches; run this when `Profile.duckdb`, the generator or
the model's functions change (a build that fails in those modules, or
`tests/lowering/duckdb.expected`, says so). Not part of the library: `lake
build` does not elaborate it.
-/

namespace Substrait

generate_lowering duckdbOn : Profile.duckdb { errorOnDivZero := true }
  unfolding [Profile.duckdb, BinFn.onFloats, duckBin, duckUn, duckZero, duckShl, nanCase, isInfCode,
    FMath.inDomain, FMath.lo?, FMath.hi?, FMath.apply, domainIssue, nanIssue, negInfPow,
    duckNegInfPow]
  using [Lowering.ref_fit, Lowering.apply_fit_int, Lowering.apply_fit_null, Lowering.apply_fit_bool,
    Lowering.apply_fit_str, Lowering.apply_fit_list, Lowering.apply_fit_struct,
    Lowering.apply_fit_float, Lowering.apply_fit_date, Lowering.apply_fit_ts, Lowering.apply_fit_tod,
    Lowering.apply_fit_dec, IntWidth.fit, IntWidth.lo, IntWidth.hi,
    IntWidth.half, IntWidth.modulus, Lowering.tmod_add_tmod, Profile.duckdb_imod_pos,
    Lowering.duck_imod_pos, Lowering.duck_dadd, Lowering.duck_dsub,
    Lowering.shl_apply, Lowering.shr_apply, Int.reduceToNat, Nat.reducePow,
    Lowering.apply_ffloor_int, Lowering.apply_ffloor_null, Lowering.apply_ffloor_bool,
    Lowering.apply_ffloor_str, Lowering.apply_ffloor_list, Lowering.apply_ffloor_float,
    Lowering.apply_ffloor_date, Lowering.apply_ffloor_ts, Lowering.apply_ffloor_tod,
    Lowering.apply_ffloor_dec, Lowering.apply_ffloor_struct, Lowering.pow2Chain_eval, List.mem_range]
  excluding [UnFn.fit]
  hand_written LoweringSearch.duckdbSchemas
  cache loweringCache
  writing "SubstraitLean/LoweringDuckDB/On"
  proving_guards

end Substrait
