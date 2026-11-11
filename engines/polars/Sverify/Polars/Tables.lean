import Sverify.Engines.Tables

/-!
# Polars's choice table and observation rows (#444, step 3a)

Polars's choices and observation rows, from its facts
(`engines/polars/facts/`), pinned to the version they were probed at (D14),
and the proof that the table refines the core (`Profile.polars_le_core`),
hence `Allowed_polars ⊆ Allowed_core`. The machinery is engines-common
(`engines/Sverify/Engines/Tables.lean`); `builtinEngines`
(`SubstraitLean/EngineTables.lean`) lists this table beside the others.
-/

namespace Substrait

/-- Polars 2.1.0 (its Python API). -/
def Profile.polars.table : ProfileTable where
  name := "polars"
  version := "2.1.0"
  choices := [
    (none, "overflow", .oneOf ["SILENT"]),
    (none, "on_division_by_zero", .oneOf ["NULL"]),
    (some "fp.div", "on_division_by_zero", .oneOf ["IEEE"]),
    (none, "on_domain_error", .oneOf ["NAN"]),
    (some "int.div", "on_domain_error", .any),
    (some "int.pow", "on_domain_error", .any),
    (none, "division_type", .oneOf ["FLOOR"]),
    (some "int.div", "division_type", .oneOf ["FLOOR"]),
    (some "int.mod", "division_type", .oneOf ["FLOOR"]),
    (none, "min_mod_neg_one", .oneOf ["ZERO"]),
    (none, "rounding", .asked ["TIE_TO_EVEN"] ["TIE_TO_EVEN"]),
    (some "fp.round", "rounding", .asked ["TIE_TO_EVEN"] ["TIE_TO_EVEN"]),
    -- By a length-1 divisor, `x * (1 / c)` (polars-scalar-divisor).
    (some "fp.div", "rounding", .oneOf ["TIE_TO_EVEN", "RECIPROCAL"]),
    (some "fp.mod", "division_type", .oneOf ["FLOOR"]),
    (none, "nan_creation", .oneOf ["NAN"]),
    (none, "float_overflow", .oneOf ["INFINITY"]),
    (none, "zero_sign", .oneOf ["IEEE"]),
    (none, "round_zero_sign", .oneOf ["IEEE"]),
    -- C's `pow`: `power(1, ±∞)` is 1 (D40).
    (none, "pow_one_inf", .oneOf ["ONE"]),
    (none, "nan_kind", .oneOf ["IEEE"]),
    (none, "nan_order", .oneOf ["GREATEST"]),
    -- `min` and `max` skip NaN unless every value is NaN (polars-min-max-nan).
    (some "agg.order", "nan_order", .oneOf ["IGNORED"]),
    (none, "nan_equality", .oneOf ["NAN_IS_NAN"]),
    -- Streaming: grouped, `+=` per value with pipelines merged by `+`;
    -- ungrouped, morsel sums added in scheduling order. In memory (not the
    -- target): pairwise, Kahan over groups.
    -- `COMPENSATED`: in memory, Kahan's sum over groups (polars-sum-float, #633).
    (none, "sum_order", .oneOf ["SEQUENTIAL", "ANY", "COMPENSATED"]),
    -- What Polars computes for the operations the lowering emits
    -- (polars-window-agg): a frame from UNBOUNDED PRECEDING reads
    -- `cum_sum().over(partition)` at its last row, a sequential `+=` from 0.0
    -- with no compensation (polars-cum-sum-float), so `RUNNING_ADD`; any
    -- other frame adds blocks of 2ᵏ rows with explicit IEEE `+`, each a
    -- balanced tree (polars-fp-ieee), so `TREE`. Not Polars's `sum`
    -- aggregate (Kahan in memory) and not `rolling_sum`, a sliding Kahan sum
    -- (polars-rolling-sum-float). A row is scoped by function group, not by
    -- frame kind, so both values stand for every frame: sound, as both sum
    -- the frame's own values. Evidence: the differential test
    -- (`test_polars_windows.py`); the lowering lemma under #271 later.
    (none, "window_sum_algo", .oneOf ["RUNNING_ADD", "TREE"]),
    (none, "stat_algo", .oneOf ["WELFORD_CHAN"]),
    -- Streaming falls back to the in-memory engine; the translation asks for
    -- `linear` (polars-quantile).
    (none, "quantile_interp", .oneOf ["LINEAR"]),
    (none, "avg_int_result", .oneOf ["FP64"]),
    (none, "empty_group_aggregates", .oneOf ["ZERO"]),
    (none, "null_order", .asked ["NULLS_FIRST", "NULLS_LAST"] ["NULLS_FIRST"]),
    (none, "clustered", .oneOf ["ADJACENT"]),
    (none, "tie_order", .oneOf ["ANY"]),
    (none, "tie_pick", .oneOf ["FIRST_READ"]),
    (none, "negative_start", .asked ["WRAP_FROM_END"] ["WRAP_FROM_END"]),
    (none, "case_sensitivity", .asked ["CASE_SENSITIVE"] ["CASE_SENSITIVE"]),
    (some "str.sub", "string_positions", .oneOf ["ZERO_BASED_CHARS"]),
    (some "str.match", "string_positions", .oneOf ["ZERO_BASED_BYTES"]),
    (none, "null_join_keys", .oneOf ["NO_MATCH"]),
    -- Decimals are `Decimal(38, max(s₁, s₂))`: they raise past 38 digits, and
    -- round a product, a quotient and a rescale half to even
    -- (polars-decimal-arith, polars-decimal-casts).
    (some "dec.arith", "overflow", .oneOf ["ERROR"]),
    (none, "decimal_rescale", .oneOf ["TIE_TO_EVEN"])] ++ uncharacterized prototypeSlice
  missing := (["md5", "sha256", "levenshtein", "repeat", "ascii", "like", "ilike"].map
    (·, ["polars-string-functions-missing"]))

def Profile.polars.obs : ObsTable := [
  (none, "overflow", (ObsRow.native ["polars-int-arith", "polars-int-divide"]).proved "Rel.polars_sound"),
  (some "agg.isum", "overflow", (ObsRow.native ["polars-sum-int"]).proved "Polars.sum_leaves_i64"),
  (none, "on_division_by_zero", (ObsRow.native ["polars-int-divide", "polars-int-modulus"]).proved "Rel.polars_sound"),
  (some "fp.div", "on_division_by_zero", (ObsRow.native ["polars-double-divide"]).proved "Rel.polars_sound"),
  (none, "on_domain_error", (ObsRow.native ["polars-double-divide"]).proved "Rel.polars_sound"),
  (none, "division_type", (ObsRow.shimmed "int_mod_trunc" ["polars-int-modulus"]).proved "Polars.int_mod_trunc"),
  (some "int.div", "division_type", (ObsRow.shimmed "int_div_trunc" ["polars-int-divide"]).proved "Polars.int_div_trunc"),
  (some "int.mod", "division_type", (ObsRow.shimmed "int_mod_trunc" ["polars-int-modulus"]).proved "Polars.int_mod_trunc"),
  (none, "min_mod_neg_one", (ObsRow.native ["polars-int-modulus"]).proved "Rel.polars_sound"),
  (none, "rounding", (ObsRow.native ["polars-fp-ieee", "polars-ieee-arith-macos-arm64", "polars-ieee-arith-linux-x86-64"]).tracking 271),
  (none, "nan_creation", (ObsRow.native ["polars-double-arith"]).proved "Rel.polars_sound"),
  -- Up to one zero; the shim `one_zero` makes it exact.
  (none, "zero_sign", ({ ObsRow.upTo { zeros := .canon } ["polars-zero-sign", "polars-zero-order"]
    with shim := some "one_zero" }).proved "Shim.one_zero"),
  -- `round` and `ceil` emit IEEE's `-0.0`; the shim `one_zero` makes it exact.
  (none, "round_zero_sign", ({ ObsRow.upTo { zeros := .canon } ["polars-round",
    "polars-round-digits"] with shim := some "one_zero" }).tracking 271),
  (none, "pow_one_inf", (ObsRow.native ["polars-pow-one-inf"]).tracking 271),
  (none, "nan_kind", (ObsRow.upTo { zeros := .canon } ["polars-nan-sign"]).tracking 271),
  (none, "nan_order", (ObsRow.native ["polars-nan-order"]).tracking 271),
  (none, "nan_equality", (ObsRow.native ["polars-nan-equality"]).tracking 271),
  -- Pairwise is a tree sum, one of the reference's; Kahan's compensated sum
  -- (groups) is not, so within #85's bound, which `float-bounds` proves for
  -- both (`StdModel.epsilon_sum_cr`, `Rnd.kahan_near`).
  -- Run to run the order varies (morsels, pipelines), within the plan's bound,
  -- whatever the input's size: a grouped sum of [1e16, 1, 1, -1e16] gave 2.0,
  -- 1.0 and 0.0 over 200 runs on 10 threads (always 0.0 with
  -- POLARS_MAX_THREADS ≤ 2).
  (none, "sum_order", ObsRow.fsumOrder ["polars-sum-float", "polars-mean-float"]
    ["polars-sum-float", "polars-sum-float-streaming", "polars-exec-row-order"]),
  (some "agg.fsum", "rounding", ObsRow.fsumRounding
    ["polars-fp-ieee", "polars-sum-float-streaming", "polars-mean-float-streaming",
      "polars-sum-float", "polars-mean-float"]
    "Each Float64 addition rounds to nearest, ties to even (polars-fp-ieee); streaming sums are sequential or pairwise trees of any shape, in-memory group sums Kahan's (polars-sum-float), and mean divides the f64 sum once: StdModel.Summed (a tree or Kahan's sum) and fl(s / n), which epsilon_sum_cr and epsilon_avg_cr bound for any rounding to nearest. Float32 sums run in single precision, which no bound covers: the checker marks their bound unproved (Epsilon.hasFp32)."),
  (none, "window_sum_algo", (ObsRow.approxWithin "plan"
    ["polars-window-agg", "polars-cum-sum-float", "polars-fp-ieee"]).tracking 900),
  -- Schubert and Gertz's merge: no theorem yet, a fuzzed bound of
  -- `1.03 · n·u·√(Q'S)` on the co-moment (polars-var-bound, #918).
  (none, "stat_algo", ({ ObsRow.approxWithin "plan" ["polars-var-std", "polars-cov", "polars-corr", "polars-var-bound"] with
    rerun := some { floats := .within "plan" } }).tracking 918),
  -- A one-row frame's streaming `group_by` gives 0 for a NaN (polars-var-pop-one-nan),
  -- where the reference gives NaN; the run returns NaN for a NaN among the values,
  -- as DuckDB's SQL does (`Stat.nanGuard_varStat` proves the guard; the bound
  -- around it is the row above's, fuzzed).
  (some "agg.var", "stat_algo", ({ ObsRow.approxWithin "plan"
      ["polars-var-std", "polars-var-std-streaming", "polars-var-bound", "polars-var-pop-one-nan"] with
    shim := some "nan_through",
    rerun := some { floats := .within "plan" },
    note := "Polars's streaming group_by of a one-row frame gives VAR and STDDEV 0 for NaN (polars-var-pop-one-nan); the run returns NaN where a value is NaN (_polars_shims.nan_through, the guard Stat.nanGuard_varStat proves), within the fuzzed bound of the row for every statistic (polars-var-bound)." }).tracking 918),
  (none, "quantile_interp", ({ ObsRow.native ["polars-quantile"] with engine := some "in-memory" }).tracking 900),
  -- `max` is NaN where the group holds one; `min`, which skips NaN, agrees
  -- with NaN as the greatest double (`Polars.min_ignore_nan`).
  (some "agg.order", "nan_order", ({ ObsRow.shimmed "max_nan_greatest" ["polars-min-max-nan"] with
    note := "MIN and MAX; QUANTILE_DISC sorts its values, NaN last (polars-nan-order)." }).proved
    "Polars.max_nan_greatest"),
  -- `min`/`max` of `-0.0` and `0.0`: up to one zero.
  (some "agg.order", "zero_sign", ({ ObsRow.upTo { zeros := .canon }
    ["polars-zero-order", "polars-min-max-zero"] with
    shim := some "one_zero" }).proved "Shim.one_zero"),
  (none, "avg_int_result", (ObsRow.shimmed "avg_int_declared" ["polars-avg-int"]).proved "Polars.avg_int_declared"),
  (none, "empty_group_aggregates", (ObsRow.shimmed "sum_empty_null" ["polars-sum-int"]).proved "Shim.sum_empty_null"),
  -- Every stated placement is native, by `nulls_last`; where a key leaves it
  -- open, Polars's default (first) is not the reference's (last), which the
  -- choices say (`transferB`), so the translation writes `nulls_last` on every
  -- key, a written argument. `Shim.null_order`: with it, Polars orders as
  -- `sortLe`.
  (none, "null_order", (ObsRow.shimmed "null_order" ["polars-null-order"]).proved "Shim.null_order"),
  (none, "clustered", (ObsRow.shimmed "sort on the keys" ["polars-clustered"]).tracking 271),
  -- A streaming sort of a large input does not keep ties in input order.
  (none, "tie_order", ({ ObsRow.native ["polars-sort-stability", "polars-first-last"] with
    rerun := some { rows := .tiesPermuted } }).proved "Polars.tie_order"),
  -- `first` and `last` follow input order on streaming, run after run.
  (none, "tie_pick", ({ ObsRow.native ["polars-first-last"] with rerun := some Obs.exact }).tracking 271),
  (some "fp.round", "rounding", (ObsRow.shimmed "round_half_away" ["polars-round"]).proved "Polars.round_half_away"),
  (some "fp.div", "rounding", ({ ObsRow.approxWithin "plan" ["polars-scalar-divisor"] with
    precondition := "every divisor of a double division is 0 or not subnormal: |y| ≥ 2⁻¹⁰²² (fp64), 2⁻¹²⁶ (fp32)",
    note := "By a scalar divisor Polars computes fl(x · fl(1 / y)): two roundings, a relative error of 2u per division where IEEE has u. Below the smallest normal, 1 / y overflows (0.0 / 1e-310 is NaN, 1e-300 / 1e-310 is inf), hence the precondition. Decided on #444: no exact-IEEE shim for `/`. The plan's bound still uses u per division; a per-engine bound (2u for Polars) is a follow-up." }).tracking 271),
  -- `log10` and `log2` are `ln x / ln b` (polars-log-base), where the
  -- reference takes the platform's `libm`: within 2.1 ulp (polars-ulp-libm),
  -- which the plan's bound adds per call (`Epsilon.opExtra`). Tested, not
  -- proved (#1270).
  (some "fp.log", "rounding", ({ ObsRow.approxWithin "plan" ["polars-log-base", "polars-ulp-libm"] with
    note := "Polars has no libm log10 or log2: both divide natural logarithms, log10 as x.log(10), log2 as x.log(2), within 2.1 ulp of libm's (polars-ulp-libm, measured). The translation runs them natively (#1270); the plan's bound adds 2.1 ulp per call (Epsilon.opExtra). A bound tested, not proved." }).tracking 1270),
  (some "fp.mod", "division_type", ({ ObsRow.shimmed "column_divisor"
      ["polars-double-modulus", "polars-scalar-divisor"] with
    note := "`%` and `//` floor the quotient, so the reciprocal's tiny error becomes a wrong result (49.0 % 49.0 is 49.0): the translation broadcasts the divisor to a column, where Polars divides as IEEE does." }).tracking 271),
  (some "fp.arith", "zero_sign", ({ ObsRow.upTo { zeros := .canon }
    ["polars-zero-sign", "polars-zero-add"] with shim := some "one_zero" }).proved "Shim.one_zero"),
  (none, "float_overflow", (ObsRow.native ["polars-double-arith"]).proved "Shim.makes_infinite"),
  (none, "negative_start", (ObsRow.native ["polars-substring"]).tracking 271),
  (none, "case_sensitivity", (ObsRow.native ["polars-match-functions"]).tracking 271),
  (some "str.sub", "string_positions", (ObsRow.shimmed "substring_wrap" ["polars-substring"]).proved "Polars.substring_wrap"),
  (some "str.match", "string_positions", (ObsRow.shimmed "strpos_chars" ["polars-strpos"]).proved "Polars.strpos_chars"),
  (none, "null_join_keys", (ObsRow.native ["polars-null-keys"]).tracking 271),
  -- Past 38 digits, where the reference raises past the result's precision,
  -- which the translation checks (`fit_decimal`).
  (some "dec.arith", "overflow", (ObsRow.native ["polars-decimal-arith"]).tracking 271),
  -- A product's scale is the sum of the operands' there, computed on the
  -- unscaled values; a cast to a smaller scale rounds half away from zero.
  (none, "decimal_rescale", (ObsRow.shimmed "decimal_round_half_away"
    ["polars-decimal-arith", "polars-decimal-casts"]).proved "Polars.decimal_round_half_away"),
  -- `AVG` of decimals and `sverify_decimal_div`: Polars's `mean` is a
  -- `Float64`, its `/` rounds half to even.
  (some "dec.div", "decimal_rescale", (ObsRow.shimmed "decimal_div_half_away"
    ["polars-decimal-arith"]).proved "Polars.decimal_div_half_away")]

theorem Profile.polars_leB : Profile.polars.table.leB Profile.core.table = true := by
  decide +kernel

theorem Profile.polars_le_core : Profile.polars.table.Le Profile.core.table :=
  ProfileTable.le_of_leB Profile.polars_leB

variable [Boxes.Ambient]

/-- `Allowed_polars ⊆ Allowed_core`. -/
theorem Rel.allowed_polars_core {cat : Catalog} {r : Rel} {out : Relation}
    (h : r.AllowedP Profile.polars.table cat out) : r.AllowedP Profile.core.table cat out :=
  Rel.AllowedP_mono Profile.polars_le_core h

end Substrait
