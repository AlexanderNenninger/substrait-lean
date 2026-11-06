import Lean.Data.Json
import SubstraitLean.Observations
import SubstraitLean.AllowedP
import SubstraitLean.Profile
import SubstraitLean.SubstraitProfile

/-!
# Engine profiles as choice tables (#444, step 3a, prototype slice)

DuckDB's, Polars's and Spark's choices and observation rows, from their facts
(`characterization/duckdb/facts/`, `characterization/polars/facts/`,
`characterization/spark/facts/`), pinned to
the versions those were probed at (D14). The rows cover the prototype slice:
integer `+ - × /` and `%`, `SUM` and `AVG` of integers and doubles, double
arithmetic, and an `ORDER BY`'s NULL order, clustering and ties, with what
these need (zeros, NaNs, rounding). Every other option is left as the core
has it (`loose` over its behaviours): not characterized, so anything.

Each table refines the core, by `decide` (`Profile.duckdb_le_core` for every
setting, `Profile.polars_le_core`), hence `Rel.AllowedP_mono` gives
`Allowed_E ⊆ Allowed_core`. `Profile.duckdb s`, the semantic profile the
lowering proves its shims against, stays as it is; its table names what it
models.

Each observation row says how the engine's behaviour relates to the
reference's: an error-side option refines on the reference's non-raising
domain, so a verified plan needs no shim there (`docs/core-semantics.md`,
"What strictness buys"); a value-side one names its shim. -/

namespace Substrait

/-- The core's rows at every option outside `slice`: not characterized. -/
def uncharacterized (slice : List String) : List (Option String × String × Choice) :=
  (options.filter fun o => !slice.contains o.id).map fun o => (none, o.id, .loose o.core)

/-- The options the prototype slice characterizes. -/
def prototypeSlice : List String :=
  ["overflow", "on_division_by_zero", "on_domain_error", "division_type", "min_mod_neg_one",
   "rounding", "nan_creation", "zero_sign", "nan_kind", "nan_order", "nan_equality",
   "sum_order", "avg_int_result", "empty_group_aggregates", "null_order", "clustered",
   "tie_order", "tie_pick", "negative_start", "case_sensitivity", "string_positions",
   "null_join_keys", "float_overflow", "stat_algo", "quantile_interp", "decimal_rescale"]

/-- The theorems of the package `float-bounds` (Mathlib, kept out of the core)
that rows name as evidence. The core cannot see them: the `run_cmd` at the
ends of `float-bounds/FloatBounds/Epsilon.lean` and `ChanCorr.lean` check
these names there, and `tests/test_float_bounds.py` that the two lists agree. -/
def floatBoundsTheorems : List String :=
  ["FloatBounds.StdModel.epsilon_sum", "FloatBounds.StdModel.epsilon_avg",
   "FloatBounds.StdModel.epsilon_sum_rel", "FloatBounds.StdModel.epsilon_avg_rel",
   "FloatBounds.StdModel.core_var_chan", "FloatBounds.StdModel.core_cov_chan",
   "FloatBounds.StdModel.core_corr_chan", "FloatBounds.StdModel.epsilon_sum_cr",
   "FloatBounds.StdModel.epsilon_avg_cr"]

/-- Evidence from the facts or tests `ids`, none where empty. -/
def Evidence.ofIds (ids : List String) : Evidence := if ids.isEmpty then .none else .tested ids

/-- The engine refines the reference as it is: natively, or, at an error-side
option, on the reference's non-raising domain. -/
def ObsRow.native (ids : List String) : ObsRow := { cls := .refines, evidence := .ofIds ids }

/-- The engine refines the reference after the shim. -/
def ObsRow.shimmed (shim : String) (ids : List String) : ObsRow :=
  { cls := .refines, shim := some shim, evidence := .ofIds ids }

/-- The engine refines the reference up to `q`. -/
def ObsRow.upTo (q : Obs) (ids : List String) : ObsRow :=
  { cls := .refinesUpTo, q, evidence := .ofIds ids }

/-- Within the bound named `b` of a result the reference allows. -/
def ObsRow.approxWithin (b : String) (ids : List String) : ObsRow :=
  { cls := .approx, q := { floats := .within b }, evidence := .ofIds ids }

/-- The row, proved by the theorem `thm` (`SubstraitLean/PolarsShims.lean`),
whose trusted model rests on the row's facts. -/
def ObsRow.proved (r : ObsRow) (thm : String) : ObsRow :=
  { r with evidence := .proved thm (match r.evidence with | .tested ids | .probed ids => ids | _ => []) }

/-! ## DuckDB -/

/-- DuckDB 2.0.0 under the settings `s`. -/
def Profile.duckdb.table (s : DuckDBSettings) : ProfileTable where
  name := "duckdb"
  version := "2.0.0"
  choices := [
    (none, "overflow", .asked ["ERROR"] ["ERROR"]),
    (none, "on_division_by_zero", .oneOf [if s.errorOnDivZero then "ERROR" else "NULL"]),
    (some "fp.div", "on_division_by_zero", .oneOf [if s.ieeeOps then "IEEE" else "ERROR"]),
    (none, "on_domain_error", .oneOf [if s.ieeeOps then "NAN" else "ERROR"]),
    (some "int.div", "on_domain_error", .any),
    (some "int.pow", "on_domain_error", .any),
    (none, "division_type", .asked ["TRUNCATE"] ["TRUNCATE"]),
    (some "int.div", "division_type", .asked ["TRUNCATE"] ["TRUNCATE"]),
    (some "int.mod", "division_type", .asked ["TRUNCATE"] ["TRUNCATE"]),
    (none, "min_mod_neg_one", .oneOf ["ERROR"]),
    (none, "rounding", .asked ["TIE_TO_EVEN"] ["TIE_TO_EVEN"]),
    (some "fp.round", "rounding", .asked ["TIE_AWAY_FROM_ZERO"] ["TIE_AWAY_FROM_ZERO"]),
    (none, "nan_creation", .oneOf ["NAN"]),
    (none, "float_overflow", .oneOf ["INFINITY"]),
    (none, "zero_sign", .oneOf ["IEEE"]),
    (none, "nan_kind", .oneOf ["IEEE"]),
    (none, "nan_order", .oneOf ["GREATEST"]),
    (none, "nan_equality", .oneOf ["NAN_IS_NAN"]),
    -- Sequential at one thread; partials merged in finishing order at more, or
    -- spilled; a constant vector as one `fl(k · x)` (#633).
    (none, "sum_order", .oneOf ["ANY", "SCALED_CONSTANT"]),
    (none, "avg_int_result", .oneOf ["EXACT_TRUNCATE"]),
    (none, "empty_group_aggregates", .oneOf ["NULL"]),
    (none, "null_order", .asked ["NULLS_FIRST", "NULLS_LAST"] ["NULLS_LAST"]),
    (none, "clustered", .oneOf ["ADJACENT"]),
    (none, "tie_order", .oneOf ["ANY"]),
    (none, "tie_pick", .oneOf ["FIRST_READ"]),
    (none, "negative_start", .asked ["WRAP_FROM_END"] ["WRAP_FROM_END"]),
    (none, "case_sensitivity", .asked ["CASE_SENSITIVE"] ["CASE_SENSITIVE"]),
    (none, "string_positions", .oneOf ["ONE_BASED_CHARS"]),
    (none, "null_join_keys", .oneOf ["NO_MATCH"]),
    (none, "stat_algo", .oneOf ["WELFORD_CHAN"]),
    (none, "quantile_interp", .oneOf ["LINEAR"]),
    -- Not characterized on DuckDB yet: the core's behaviours.
    (none, "decimal_rescale", .loose ["TIE_AWAY_FROM_ZERO", "TIE_TO_EVEN", "TRUNCATE"])] ++
    uncharacterized prototypeSlice

def Profile.duckdb.obs : ObsTable := [
  (none, "overflow", .native ["duckdb-R1", "duckdb-R15-int-arith"]),
  -- `SUM(BIGINT)` is a `HUGEINT`; the written plan casts it back, which raises
  -- where the reference does: a type, not a value, so no shim.
  (some "agg.isum", "overflow", .native ["duckdb-R6"]),
  (none, "on_division_by_zero", .native ["duckdb-R2"]),
  (some "fp.div", "on_division_by_zero", .native ["duckdb-R5"]),
  (none, "on_domain_error", .native ["duckdb-R15-double-arith"]),
  (none, "division_type", .native ["duckdb-R3"]),
  (none, "min_mod_neg_one", .shimmed "MIN % -1 written out" ["duckdb-R15-int-modulus"]),
  (none, "rounding", .native []),
  (none, "nan_creation", .native ["duckdb-R15-double-arith"]),
  -- Two zeros, as IEEE has them: the reference's up to one zero, or exactly
  -- after `Dialect.canon`.
  (none, "zero_sign", { ObsRow.upTo { zeros := .canon } ["duckdb-R14"] with
    shim := some "Dialect.canon" }),
  (none, "nan_kind", .upTo { zeros := .canon } ["duckdb-signbit"]),
  (none, "nan_order", .native ["duckdb-arg-min-nulls"]),
  (none, "nan_equality", .native []),
  -- Partials merged in finishing order are trees the reference allows, but a
  -- constant vector's `fl(k · x)` is not known to be one (#633): within #85's
  -- bound, which `float-bounds` proves for both (`StdModel.epsilon_sum`).
  -- Which order depends on the parallel plan, so at two threads or more runs
  -- vary (3 to 4 values in 5 runs), each within the bound. `fsum` (Kahan)
  -- does not vary.
  (none, "sum_order", ({ ObsRow.approxWithin "plan" ["duckdb-sum-double", "duckdb-avg-double"] with
    note := "Sequential only at one thread; partials merged in finishing order at more threads or when spilled (ANY); a constant vector, or a constant-compressed segment, is added as one fl(k · x), which is not known to be a tree sum (#633). Every one of them is within the plan's bound (StdModel.epsilon_sum).",
    rerun := some { floats := .within "plan" },
    rerunEvidence := .proved "FloatBounds.StdModel.epsilon_sum"
      ["duckdb-sum-double", "duckdb-avg-double", "duckdb-exec-row-order"] }).proved
    "FloatBounds.StdModel.epsilon_sum"),
  (none, "avg_int_result", .native ["duckdb-R6"]),
  (none, "empty_group_aggregates", .native []),
  (none, "null_order", .native ["duckdb-F2"]),
  -- The written `ORDER BY` is the model's sort, which `SortAllowed` allows for
  -- a clustered key (`Rel.duckdb_refines`; `test_realizability.py` runs it).
  (none, "clustered", (ObsRow.shimmed "ORDER BY the keys" []).proved "Rel.duckdb_refines"),
  -- Ties come in the order threads read the rows.
  -- `ORDER BY`, `row_number`, `ntile`, `lag` and `list` without a total order:
  -- ties, and a list's elements, come in a different order run to run.
  (none, "tie_order", { ObsRow.native ["duckdb-sort-ties", "duckdb-mode-ties"] with
    rerun := some { rows := .tiesPermuted, elements := .multiset },
    rerunEvidence := .probed ["duckdb-sort-ties", "duckdb-mode-ties", "duckdb-exec-row-order"] }),
  (none, "tie_pick", { ObsRow.native ["duckdb-mode-ties", "duckdb-arg-min-nulls"] with
    rerun := some { rows := .tiesPermuted },
    rerunEvidence := .probed ["duckdb-mode-ties", "duckdb-exec-row-order"] }),
  (some "fp.round", "rounding", .native ["duckdb-R15-round"]),
  (none, "float_overflow", .native ["duckdb-R15-double-arith"]),
  (none, "negative_start", .native ["duckdb-R13"]),
  (none, "case_sensitivity", .native []),
  (none, "string_positions", .native []),
  (none, "null_join_keys", .native []),
  -- Welford with Chan's merge meets the generic properties the reference allows:
  -- `float-bounds` proves `VAR_*`, `COVAR_*` and DuckDB's `CORR` formula within
  -- `StatProps` (`core_var_chan`, `core_cov_chan`, `core_corr_chan`; `STDDEV_*`
  -- by `core_stddev` of the variance), for IEEE rounding (`Mono`, `Grid`).
  (none, "stat_algo", ({ ObsRow.native ["duckdb-var-stddev", "duckdb-covar", "duckdb-corr"] with
    rerun := some { floats := .within "plan" } }).proved "FloatBounds.StdModel.core_var_chan"),
  (none, "quantile_interp", .native ["duckdb-quantile-cont-interpolation"])]

/-! ## Polars -/

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
  (none, "rounding", .native []),
  (none, "nan_creation", (ObsRow.native ["polars-double-arith"]).proved "Rel.polars_sound"),
  -- Up to one zero; the shim `one_zero` makes it exact.
  (none, "zero_sign", ({ ObsRow.upTo { zeros := .canon } ["polars-zero-sign", "polars-zero-order"]
    with shim := some "one_zero" }).proved "Polars.one_zero"),
  (none, "nan_kind", .upTo { zeros := .canon } ["polars-nan-sign"]),
  (none, "nan_order", .native ["polars-nan-order"]),
  (none, "nan_equality", .native ["polars-nan-equality"]),
  -- Pairwise is a tree sum, one of the reference's; Kahan's compensated sum
  -- (groups) is not, so within #85's bound, which `float-bounds` proves for
  -- both (`StdModel.epsilon_sum`, `Rnd.kahan_near`).
  -- Run to run the order varies (morsels, pipelines), within the plan's bound,
  -- whatever the input's size: a grouped sum of [1e16, 1, 1, -1e16] gave 2.0,
  -- 1.0 and 0.0 over 200 runs on 10 threads (always 0.0 with
  -- POLARS_MAX_THREADS ≤ 2).
  (none, "sum_order", ({ ObsRow.approxWithin "plan" ["polars-sum-float", "polars-mean-float"] with
    rerun := some { floats := .within "plan" },
    rerunEvidence := .proved "FloatBounds.StdModel.epsilon_sum"
      ["polars-sum-float", "polars-sum-float-streaming", "polars-exec-row-order"] }).proved
    "FloatBounds.StdModel.epsilon_sum"),
  (none, "stat_algo", { ObsRow.native ["polars-var-std", "polars-cov", "polars-corr"] with
    rerun := some { floats := .within "plan" } }),
  (none, "quantile_interp", { ObsRow.native ["polars-quantile"] with engine := some "in-memory" }),
  -- `max` is NaN where the group holds one; `min`, which skips NaN, agrees
  -- with NaN as the greatest double (`Polars.min_ignore_nan`).
  (some "agg.order", "nan_order", ({ ObsRow.shimmed "max_nan_greatest" ["polars-min-max-nan"] with
    note := "MIN and MAX; QUANTILE_DISC sorts its values, NaN last (polars-nan-order)." }).proved
    "Polars.max_nan_greatest"),
  -- `min`/`max` of `-0.0` and `0.0`: up to one zero.
  (some "agg.order", "zero_sign", ({ ObsRow.upTo { zeros := .canon }
    ["polars-zero-order", "polars-min-max-zero"] with
    shim := some "one_zero" }).proved "Polars.one_zero"),
  (none, "avg_int_result", (ObsRow.shimmed "avg_int_declared" ["polars-avg-int"]).proved "Polars.avg_int_declared"),
  (none, "empty_group_aggregates", (ObsRow.shimmed "sum_empty_null" ["polars-sum-int"]).proved "Polars.sum_empty_null"),
  -- Every stated placement is native, by `nulls_last`; where a key leaves it
  -- open, Polars's default (first) is not the reference's (last), which the
  -- choices say (`transferB`), so the translation writes `nulls_last` on every
  -- key, a written argument. `Polars.null_order`: with it, Polars orders as
  -- `sortLe`.
  (none, "null_order", (ObsRow.shimmed "null_order" ["polars-null-order"]).proved "Polars.null_order"),
  (none, "clustered", .shimmed "sort on the keys" ["polars-clustered"]),
  -- A streaming sort of a large input does not keep ties in input order.
  (none, "tie_order", ({ ObsRow.native ["polars-sort-stability", "polars-first-last"] with
    rerun := some { rows := .tiesPermuted } }).proved "Polars.tie_order"),
  -- `first` and `last` follow input order on streaming, run after run.
  (none, "tie_pick", { ObsRow.native ["polars-first-last"] with rerun := some Obs.exact }),
  (some "fp.round", "rounding", (ObsRow.shimmed "round_half_away" ["polars-round"]).proved "Polars.round_half_away"),
  (some "fp.div", "rounding", { ObsRow.approxWithin "plan" ["polars-scalar-divisor"] with
    precondition := "every divisor of a double division is 0 or not subnormal: |y| ≥ 2⁻¹⁰²² (fp64), 2⁻¹²⁶ (fp32)",
    note := "By a scalar divisor Polars computes fl(x · fl(1 / y)): two roundings, a relative error of 2u per division where IEEE has u. Below the smallest normal, 1 / y overflows (0.0 / 1e-310 is NaN, 1e-300 / 1e-310 is inf), hence the precondition. Decided on #444: no exact-IEEE shim for `/`. The plan's bound still uses u per division; a per-engine bound (2u for Polars) is a follow-up." }),
  (some "fp.mod", "division_type", { ObsRow.shimmed "column_divisor"
      ["polars-double-modulus", "polars-scalar-divisor"] with
    note := "`%` and `//` floor the quotient, so the reciprocal's tiny error becomes a wrong result (49.0 % 49.0 is 49.0): the translation broadcasts the divisor to a column, where Polars divides as IEEE does." }),
  (some "fp.arith", "zero_sign", ({ ObsRow.upTo { zeros := .canon }
    ["polars-zero-sign", "polars-zero-add"] with shim := some "one_zero" }).proved "Polars.one_zero"),
  (none, "float_overflow", (ObsRow.native ["polars-double-arith"]).proved "Polars.makes_infinite"),
  (none, "negative_start", .native ["polars-substring"]),
  (none, "case_sensitivity", .native ["polars-match-functions"]),
  (some "str.sub", "string_positions", (ObsRow.shimmed "substring_wrap" ["polars-substring"]).proved "Polars.substring_wrap"),
  (some "str.match", "string_positions", (ObsRow.shimmed "strpos_chars" ["polars-strpos"]).proved "Polars.strpos_chars"),
  (none, "null_join_keys", .native ["polars-null-keys"]),
  -- Past 38 digits, where the reference raises past the result's precision,
  -- which the translation checks (`fit_decimal`).
  (some "dec.arith", "overflow", .native ["polars-decimal-arith"]),
  -- A product's scale is the sum of the operands' there, computed on the
  -- unscaled values; a cast to a smaller scale rounds half away from zero.
  (none, "decimal_rescale", (ObsRow.shimmed "decimal_round_half_away"
    ["polars-decimal-arith", "polars-decimal-casts"]).proved "Polars.decimal_round_half_away"),
  -- `AVG` of decimals and `sverify_decimal_div`: Polars's `mean` is a
  -- `Float64`, its `/` rounds half to even.
  (some "dec.div", "decimal_rescale", (ObsRow.shimmed "decimal_div_half_away"
    ["polars-decimal-arith"]).proved "Polars.decimal_div_half_away")]

/-! ## Spark -/

/-- Spark 4.3.0 under `sverify.sql.spark.SPARK_CONF`: ANSI mode on, `TIMESTAMP`
as `TIMESTAMP_NTZ`, the session time zone UTC (spark-exec-settings). -/
def Profile.spark.table : ProfileTable where
  name := "spark"
  version := "4.3.0"
  choices := [
    -- ANSI raises past the width (spark-int-arith, spark-int-abs).
    (none, "overflow", .asked ["ERROR"] ["ERROR"]),
    -- ANSI raises: `DIVIDE_BY_ZERO`, `REMAINDER_BY_ZERO`, for doubles too.
    (none, "on_division_by_zero", .oneOf ["ERROR"]),
    (some "fp.div", "on_division_by_zero", .oneOf ["ERROR"]),
    -- `sqrt(-1)`, `asin(2)` are NaN; the logarithms of `x ≤ 0` are NULL
    -- (spark-math-domain, ST-16).
    (none, "on_domain_error", .oneOf ["NAN", "NULL"]),
    (some "int.div", "on_domain_error", .any),
    (some "int.pow", "on_domain_error", .any),
    (none, "division_type", .asked ["TRUNCATE"] ["TRUNCATE"]),
    (some "int.div", "division_type", .asked ["TRUNCATE"] ["TRUNCATE"]),
    (some "int.mod", "division_type", .asked ["TRUNCATE"] ["TRUNCATE"]),
    (none, "min_mod_neg_one", .oneOf ["ZERO"]),
    (none, "rounding", .asked ["TIE_TO_EVEN"] ["TIE_TO_EVEN"]),
    -- `round(x)` rounds halves away from zero; `round(x, d)` rounds the
    -- shortest decimal text, which the writer never calls (spark-round).
    (some "fp.round", "rounding", .asked ["TIE_AWAY_FROM_ZERO"] ["TIE_AWAY_FROM_ZERO"]),
    (none, "nan_creation", .oneOf ["NAN"]),
    (none, "float_overflow", .oneOf ["INFINITY"]),
    (none, "zero_sign", .oneOf ["IEEE"]),
    (none, "nan_kind", .oneOf ["IEEE"]),
    (none, "nan_order", .oneOf ["GREATEST"]),
    (none, "nan_equality", .oneOf ["NAN_IS_NAN"]),
    -- Partials per task, merged in the order the tasks finish.
    (none, "sum_order", .oneOf ["ANY"]),
    (none, "stat_algo", .oneOf ["WELFORD_CHAN"]),
    (none, "quantile_interp", .oneOf ["LINEAR"]),
    (none, "avg_int_result", .oneOf ["FP64"]),
    (none, "empty_group_aggregates", .oneOf ["NULL"]),
    -- First for an ascending key, last for a descending one.
    (none, "null_order", .asked ["NULLS_FIRST", "NULLS_LAST"] ["NULLS_FIRST"]),
    (none, "clustered", .oneOf ["ADJACENT"]),
    (none, "tie_order", .oneOf ["ANY"]),
    -- `first` after a shuffle: the first row of whichever partition comes
    -- first (spark-first-last).
    (none, "tie_pick", .oneOf ["ANY_ROW"]),
    (none, "negative_start", .asked ["WRAP_FROM_END"] ["WRAP_FROM_END"]),
    (none, "case_sensitivity", .asked ["CASE_SENSITIVE"] ["CASE_SENSITIVE"]),
    (none, "string_positions", .oneOf ["ONE_BASED_CHARS"]),
    (none, "null_join_keys", .oneOf ["NO_MATCH"]),
    -- Decimals raise past their type under ANSI (spark-decimal-arith).
    (some "dec.arith", "overflow", .oneOf ["ERROR"]),
    -- `ROUND_HALF_UP` on `BigDecimal` (spark-decimal-arith).
    (none, "decimal_rescale", .oneOf ["TIE_AWAY_FROM_ZERO"])] ++ uncharacterized prototypeSlice

def Profile.spark.obs : ObsTable := [
  (none, "overflow", (ObsRow.native ["spark-int-arith", "spark-int-abs"]).proved "Rel.spark_sound"),
  -- A `BIGINT` partial sum raises by the order of the rows; the writer sums
  -- exact `DECIMAL(38,0)` values (`Spark.partial_sums_fit`).
  (some "agg.isum", "overflow", (ObsRow.shimmed "int_sum_decimal" ["spark-sum-int", "spark-exec-parallel"]).proved
    "Spark.int_sum_decimal"),
  (some "int.div", "overflow", (ObsRow.native ["spark-int-divide"]).proved "Rel.spark_sound"),
  (none, "on_division_by_zero", (ObsRow.native ["spark-int-divide", "spark-int-modulus"]).proved "Rel.spark_sound"),
  (some "fp.div", "on_division_by_zero", .native ["spark-double-divide"]),
  (none, "on_domain_error", (ObsRow.native ["spark-math-domain"]).proved "Rel.spark_sound"),
  (none, "division_type", .native ["spark-int-modulus"]),
  (some "int.div", "division_type", .native ["spark-int-divide"]),
  (some "int.mod", "division_type", .native ["spark-int-modulus"]),
  (none, "min_mod_neg_one", .native ["spark-int-modulus"]),
  (none, "rounding", .native ["spark-double-arith"]),
  (some "fp.round", "rounding", { ObsRow.native ["spark-round"] with
    note := "round(x) rounds halves away from zero; round(x, d) rounds the double's shortest decimal text (round(2.675, 2) is 2.68), so the writer computes ROUND(x · 10ᵈ) / 10ᵈ as the reference does (FloatCode.roundTo) and never calls it." }),
  (none, "nan_creation", (ObsRow.native ["spark-double-arith", "spark-nonfinite-aggregates"]).proved "Rel.spark_sound"),
  (none, "float_overflow", (ObsRow.native ["spark-double-arith"]).proved "Polars.makes_infinite"),
  -- Two zeros, as IEEE has them: the reference's up to one zero, or exactly
  -- after `Dialect.canon`.
  (none, "zero_sign", ({ ObsRow.upTo { zeros := .canon } ["spark-zero-sign", "spark-zero-order"] with
    shim := some "Dialect.canon" }).proved "Spark.one_zero"),
  (none, "nan_kind", .upTo { zeros := .canon } ["spark-nan-sign"]),
  (none, "nan_order", .native ["spark-nan-order"]),
  (none, "nan_equality", .native ["spark-nan-equality"]),
  -- Partial sums merged in the order the tasks finish: trees the reference
  -- allows, within #85's bound, varying run to run with the partitioning.
  (none, "sum_order", ({ ObsRow.approxWithin "plan" ["spark-sum-double", "spark-avg-double"] with
    rerun := some { floats := .within "plan" },
    rerunEvidence := .proved "FloatBounds.StdModel.epsilon_sum"
      ["spark-sum-double", "spark-avg-double", "spark-exec-parallel"] }).proved
    "FloatBounds.StdModel.epsilon_sum"),
  (none, "avg_int_result", (ObsRow.shimmed "int_avg_decimal" ["spark-avg-int"]).proved "Spark.int_avg_decimal"),
  (none, "empty_group_aggregates", .native ["spark-sum-int", "spark-sum-double"]),
  -- Unstated, Spark puts NULLs first in an ascending key; the writer states
  -- each key's placement (`Spark.null_order`).
  (none, "null_order", (ObsRow.shimmed "null_order" ["spark-null-order"]).proved "Spark.null_order"),
  (none, "clustered", .shimmed "sort on the keys" ["spark-clustered"]),
  -- After a shuffle, ties come in the order the partitions' rows arrive.
  (none, "tie_order", { ObsRow.native ["spark-sort-stability", "spark-window-values", "spark-rank"] with
    rerun := some { rows := .tiesPermuted, elements := .multiset },
    rerunEvidence := .probed ["spark-sort-stability", "spark-exec-parallel"] }),
  (none, "tie_pick", { ObsRow.native ["spark-first-last"] with
    rerun := some { rows := .tiesPermuted },
    rerunEvidence := .probed ["spark-first-last", "spark-exec-parallel"] }),
  -- Only starts from 1 reach Spark's `substring`, whose start 0 reads as 1
  -- (`Dialect.substring` of the writer).
  (none, "negative_start", .native ["spark-substring"]),
  (none, "case_sensitivity", .native ["spark-match-functions"]),
  (none, "string_positions", .native ["spark-strpos", "spark-substring"]),
  (none, "null_join_keys", .native ["spark-null-keys"]),
  (none, "stat_algo", ({ ObsRow.native ["spark-var-stddev", "spark-covar", "spark-corr"] with
    rerun := some { floats := .within "plan" } }).proved "FloatBounds.StdModel.core_var_chan"),
  (none, "quantile_interp", .native ["spark-quantile"]),
  (none, "decimal_rescale", .native ["spark-decimal-arith"]),
  -- `-x` and `abs` round past 34 digits (SP-1); the writer's `0 - x` is exact
  -- where its type keeps the scale, and a type past 38 digits at a scale
  -- above 6, which Spark would round, is refused.
  (some "dec.arith", "overflow", (ObsRow.shimmed "decimal_negate_sub"
    ["spark-decimal-negate", "spark-decimal-arith"]).proved "Spark.decimal_negate_sub")]

/-! ## The engines -/

/-- The options whose functions an engine computes row by row, or exactly
whatever the order (integer sums, a placement a key fixes, a sorted
quantile): every run gives the same result, as each row's facts were probed
to give, where `rerun` is not set already. The others stay unknown. -/
def rerunExact : List String :=
  ["overflow", "on_division_by_zero", "on_domain_error", "division_type", "min_mod_neg_one",
   "rounding", "nan_creation", "float_overflow", "negative_start", "case_sensitivity",
   "string_positions", "avg_int_result", "empty_group_aggregates", "null_order",
   "null_join_keys", "quantile_interp", "decimal_rescale"]

/-- Each row with what reruns give: exact where `rerunExact` says so, with the
row's facts as evidence; a variation keeps its own. -/
def withReruns (obs : ObsTable) : ObsTable :=
  obs.map fun (g, o, r) =>
    -- A row's correctness theorem is no evidence for its reruns: keep its facts.
    let ev := match r.evidence with
      | .tested ids | .proved _ ids => Evidence.tested ids | e => e
    match r.rerun with
    | some _ => (g, o, if r.rerunEvidence == .none then { r with rerunEvidence := ev } else r)
    | none =>
      -- A sum's sign of zero is the row's own; a group key's or `min`'s zero is
      -- the one seen first, or the platform's: not settled here.
      -- Exact only with evidence: a row without facts stays unknown.
      if ev != .none && (rerunExact.contains o || (o == "zero_sign" && g == some "fp.arith")) then (g, o, { r with rerun := some Obs.exact, rerunEvidence := ev })
      else (g, o, r)

/-- The engine profiles, under DuckDB's default settings. -/
def engineTables : List (ProfileTable × ObsTable) :=
  [(Profile.duckdb.table {}, withReruns Profile.duckdb.obs),
   (Profile.polars.table, withReruns Profile.polars.obs),
   (Profile.spark.table, withReruns Profile.spark.obs)]

/-- **Every DuckDB setting refines the core.** -/
theorem Profile.duckdb_le_core (s : DuckDBSettings) : (Profile.duckdb.table s).Le Profile.core.table := by
  obtain ⟨e, i⟩ := s
  apply ProfileTable.le_of_leB
  cases e <;> cases i <;> decide +kernel

theorem Profile.polars_le_core : Profile.polars.table.Le Profile.core.table :=
  ProfileTable.le_of_leB (by decide +kernel)

theorem Profile.spark_le_core : Profile.spark.table.Le Profile.core.table :=
  ProfileTable.le_of_leB (by decide +kernel)

/-- `Allowed_duckdb ⊆ Allowed_core`, for every setting. -/
theorem Rel.allowed_duckdb_core (s : DuckDBSettings) {cat : Catalog} {r : Rel} {out : Relation}
    (h : r.AllowedP (Profile.duckdb.table s) cat out) : r.AllowedP Profile.core.table cat out :=
  Rel.AllowedP_mono (Profile.duckdb_le_core s) h

/-- `Allowed_polars ⊆ Allowed_core`. -/
theorem Rel.allowed_polars_core {cat : Catalog} {r : Rel} {out : Relation}
    (h : r.AllowedP Profile.polars.table cat out) : r.AllowedP Profile.core.table cat out :=
  Rel.AllowedP_mono Profile.polars_le_core h

/-- `Allowed_spark ⊆ Allowed_core`. -/
theorem Rel.allowed_spark_core {cat : Catalog} {r : Rel} {out : Relation}
    (h : r.AllowedP Profile.spark.table cat out) : r.AllowedP Profile.core.table cat out :=
  Rel.AllowedP_mono Profile.spark_le_core h

/-- An engine's observation rows: well-formed, at options of the catalogue,
one per group and option. -/
def ObsTable.wf (t : ObsTable) : Bool :=
  t.all (fun (_, o, r) => r.wf && (OptionSpec.find? o).isSome) &&
    nodupB (t.map fun (g, o, _) => (g, o))

example : engineTables.all (·.2.wf) := by decide +kernel
/-- Each observation row is at an option the slice characterizes. -/
example : engineTables.all fun (_, obs) => obs.all fun (_, o, _) => prototypeSlice.contains o := by
  decide +kernel

/-- How many of an engine's rows at `option` need a shim. -/
def shimCount (obs : ObsTable) (option : String) : Nat :=
  (obs.filter fun (_, o, r) => o == option && r.shim.isSome).length

/-! ## For Python -/

open Lean (Json toJson) in
def choicesJson (t : ProfileTable) : Json :=
  Json.arr <| (t.choices.map fun (g, o, c) => Json.mkObj [
    ("group", toJson g), ("option", toJson o), ("choice", c.json)]).toArray

open Lean (Json toJson) in
/-- The tool table, with each engine's shim count per option. -/
def toolsJson : Json :=
  Json.arr <| (Profile.reference.tools.map fun r => Json.mkObj [
    ("option", toJson r.option),
    ("tool", toJson (match r.tool with
      | .raise => "raise" | .choose => "choose" | .leaveOpen => "leave_open")),
    ("precondition", toJson r.precondition),
    ("shims", Json.mkObj (engineTables.map fun (t, obs) => (t.name, toJson (shimCount obs r.option))))
  ]).toArray

open Lean (Json toJson) in
/-- A profile's rows as the Python side reads them: per group (or `null`) and
option, the choice, and where the observation table has a row for it its
class, observation (only the components that are not exact), shim and
evidence; for the reference also D9's tool, the precondition of a raise and
the observation a contract must keep at an option left open. -/
def profileRowsJson (t : ProfileTable) (obs : ObsTable) (reference : Bool) : Json :=
  let keys := (t.choices.map fun (g, o, _) => (g, o)) ++
    ((obs.map fun (g, o, _) => (g, o)).filter fun k => !(t.choices.any fun (g, o, _) => (g, o) == k))
  Json.arr <| (keys.map fun (g, o) =>
    let choice := match g with
      | some g => t.choice? g o
      | none => t.dflt? o
    let row := match g with
      | some g => obs.row? g o
      | none => (obs.find? fun (x : Option String × String × ObsRow) =>
          x.1.isNone && x.2.1 == o).map fun (x : Option String × String × ObsRow) => x.2.2
    let base : List (String × Json) := [("group", toJson g), ("option", toJson o),
      ("choice", match choice with | some c => c.json | none => Json.null)]
    let obsFields : List (String × Json) := match row with
      | none => []
      | some r =>
        -- A refinement only after a shim is the class `shim` (#568's fourth).
        [("class", toJson (match r.cls, r.shim with
          | .refines, some _ => "shim"
          | .refines, none => "refines" | .refinesUpTo, _ => "refines_up_to"
          | .approx, _ => "approx" | .refused, _ => "refused")),
         ("shim", toJson r.shim)] ++
        [("q", r.q.sparseJson)] ++
        (match r.rerun with
          | none => []
          | some q =>
            [("rerun", q.sparseJson), ("deterministic", toJson (q == Obs.exact))] ++
            match r.rerunEvidence with
            | .proved thm _ => [("rerun_evidence", toJson "proved"), ("rerun_theorem", toJson thm)]
            | .tested ids => [("rerun_evidence", toJson "tested"), ("rerun_facts", toJson ids)]
            | .probed ids => [("rerun_evidence", toJson "probe"), ("rerun_facts", toJson ids)]
            | .none => []) ++
        (match r.engine with | some e => [("engine", toJson e)] | none => []) ++
        (if r.precondition == "" then [] else [("precondition", toJson r.precondition)]) ++
        (if r.note == "" then [] else [("note", toJson r.note)]) ++
        (match r.evidence with
          | .proved thm ids => [("evidence", toJson "proved"), ("theorem", toJson thm), ("facts", toJson ids)]
          | .tested ids => [("evidence", toJson "tested"), ("facts", toJson ids)]
          | .probed ids => [("evidence", toJson "probe"), ("facts", toJson ids)]
          | .none => [("facts", toJson ([] : List String))])
    let toolFields : List (String × Json) := if !reference then [] else
      match Profile.reference.tools.find? (·.option == o) with
      | none => []
      | some tr =>
        [("tool", toJson (match tr.tool with
          | .raise => "raise" | .choose => "choose" | .leaveOpen => "open"))] ++
        (if tr.precondition == "" then [] else [("precondition", toJson tr.precondition)]) ++
        (match tr.q with | some q => [("q", q.sparseJson)] | none => [])
    -- At an option the reference leaves open, `q` is what a contract keeps.
    let obsFields := if toolFields.any (·.1 == "q") then obsFields.filter (·.1 != "q") else obsFields
    Json.mkObj (base ++ obsFields ++ toolFields)).toArray

open Lean (Json toJson) in
/-- `substrait-check --options`: the options, the groups' options, each
profile's choices and observation rows, the profiles' versions, and the tool
table. -/
def tablesJson : Json :=
  optionsJson
    |>.setObjVal! "choices" (Json.mkObj ([
        ("reference", profileRowsJson Profile.reference.table Profile.reference.obs true),
        ("core", choicesJson Profile.core.table),
        ("substrait", profileRowsJson Profile.substrait.table Profile.substrait.obs false)] ++
      engineTables.map fun (t, obs) => (t.name, profileRowsJson t obs false)))
    |>.setObjVal! "profiles" (Json.mkObj ([
        ("reference", Json.mkObj [("engine", Json.null)]),
        ("core", Json.mkObj [("engine", Json.null)]),
        ("substrait", Json.mkObj [("engine", Json.null), ("yaml", toJson Profile.substrait.table.version)])] ++
      engineTables.map fun (t, _) => (t.name, Json.mkObj [
        ("engine", toJson t.name), ("versions", toJson [t.version]),
        ("executes", toJson (if t.name == "polars" then "streaming" else if t.name == "spark" then "batch" else "")),
        ("missing", Json.arr <| (t.missing.map fun (f, ids) =>
          Json.mkObj [("function", toJson f), ("facts", toJson ids)]).toArray)])))
    |>.setObjVal! "observations" (Json.mkObj ([("reference", obsTableJson Profile.reference.obs),
        ("substrait", obsTableJson Profile.substrait.obs)] ++
      engineTables.map fun (t, obs) => (t.name, obsTableJson obs)))
    |>.setObjVal! "versions" (Json.mkObj (engineTables.map fun (t, _) => (t.name, toJson t.version)))
    |>.setObjVal! "tools" toolsJson

end Substrait
