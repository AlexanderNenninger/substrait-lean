import Sverify.Engines.Tables

/-!
# Spark's choice table and observation rows (#444, step 3a)

Spark's choices and observation rows, from its facts
(`engines/spark/facts/`), pinned to the version they were probed at (D14),
and the proof that the table refines the core (`Profile.spark_le_core`),
hence `Allowed_spark ⊆ Allowed_core`. The machinery is engines-common
(`engines/Sverify/Engines/Tables.lean`); `builtinEngines`
(`SubstraitLean/EngineTables.lean`) lists this table beside the others.
-/

namespace Substrait

/-- Spark 4.3.0 under `sverify_spark.dialect.SPARK_CONF`: ANSI mode on, `TIMESTAMP`
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
    (none, "round_zero_sign", .oneOf ["POSITIVE"]),
    -- `StrictMath.pow(1, ±∞)` is NaN (spark-math-domain, D40).
    (none, "pow_one_inf", .oneOf ["NAN"]),
    (none, "nan_kind", .oneOf ["IEEE"]),
    (none, "nan_order", .oneOf ["GREATEST"]),
    (none, "nan_equality", .oneOf ["NAN_IS_NAN"]),
    -- Partials per task, merged in the order the tasks finish.
    (none, "sum_order", .oneOf ["ANY"]),
    -- A whole partition at once, a growing frame by a running sum, any other
    -- frame anew; a segment tree only with `segmentTree.enabled` (spark-window-agg).
    (none, "window_sum_algo", .oneOf ["RECOMPUTE", "RUNNING_ADD", "TREE"]),
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
    "Shim.sum_empty_null"),
  (some "int.div", "overflow", (ObsRow.native ["spark-int-divide"]).proved "Rel.spark_sound"),
  (none, "on_division_by_zero", (ObsRow.native ["spark-int-divide", "spark-int-modulus"]).proved "Rel.spark_sound"),
  (some "fp.div", "on_division_by_zero", (ObsRow.native ["spark-double-divide"]).tracking 271),
  (none, "on_domain_error", (ObsRow.native ["spark-math-domain"]).proved "Rel.spark_sound"),
  (none, "division_type", (ObsRow.native ["spark-int-modulus"]).tracking 271),
  (some "int.div", "division_type", (ObsRow.native ["spark-int-divide"]).tracking 271),
  (some "int.mod", "division_type", (ObsRow.native ["spark-int-modulus"]).tracking 271),
  (none, "min_mod_neg_one", (ObsRow.native ["spark-int-modulus"]).tracking 271),
  (none, "rounding", (ObsRow.native ["spark-double-arith"]).tracking 271),
  (some "fp.round", "rounding", ({ ObsRow.native ["spark-round"] with
    note := "round(x) rounds halves away from zero; round(x, d) rounds the double's shortest decimal text (round(2.675, 2) is 2.68), so the writer computes ROUND(x · 10ᵈ) / 10ᵈ as the reference does (FloatCode.roundTo) and never calls it." }).tracking 271),
  (none, "nan_creation", (ObsRow.native ["spark-double-arith", "spark-nonfinite-aggregates"]).proved "Rel.spark_sound"),
  (none, "float_overflow", (ObsRow.native ["spark-double-arith"]).proved "Shim.makes_infinite"),
  -- Two zeros, as IEEE has them: the reference's up to one zero, or exactly
  -- after `Dialect.canon`.
  (none, "zero_sign", ({ ObsRow.upTo { zeros := .canon } ["spark-zero-sign", "spark-zero-order"] with
    shim := some "Dialect.canon" }).proved "Shim.one_zero"),
  -- `round` emits `+0.0` through a decimal; `ceil` is a `BIGINT`, which the
  -- written plan casts back to a double.
  (none, "round_zero_sign", (ObsRow.native ["spark-round", "spark-floor-ceil-bigint"]).tracking 271),
  -- `StrictMath.pow(1, ±∞)` is NaN; the writer refuses double `power`
  -- (spark-elem-rounding).
  (none, "pow_one_inf", ({ ObsRow.native ["spark-math-domain", "spark-elem-rounding"] with
    cls := .refused }).tracking 271),
  (none, "nan_kind", (ObsRow.upTo { zeros := .canon } ["spark-nan-sign"]).tracking 271),
  (none, "nan_order", (ObsRow.native ["spark-nan-order"]).tracking 271),
  (none, "nan_equality", (ObsRow.native ["spark-nan-equality"]).tracking 271),
  -- Partial sums merged in the order the tasks finish: trees the reference
  -- allows, within #85's bound, varying run to run with the partitioning.
  (none, "sum_order", ObsRow.fsumOrder ["spark-sum-double", "spark-avg-double"]
    ["spark-sum-double", "spark-avg-double", "spark-exec-parallel"]),
  (some "agg.fsum", "rounding", ObsRow.fsumRounding
    ["spark-double-arith", "spark-sum-double", "spark-avg-double"]
    "Each addition is the JVM's, rounded to nearest, ties to even (spark-double-arith); the sum is plain additions in an order the partitioning sets (spark-sum-double), a FLOAT column summed in DOUBLE, and AVG divides it once by the count (spark-avg-double): StdModel.TreeSum and fl(s / n), which epsilon_sum_cr and epsilon_avg_cr bound for any rounding to nearest."),
  (none, "avg_int_result", (ObsRow.shimmed "int_avg_decimal" ["spark-avg-int"]).proved "Shim.avg_trunc"),
  (none, "empty_group_aggregates", (ObsRow.native ["spark-sum-int", "spark-sum-double"]).tracking 271),
  -- Unstated, Spark puts NULLs first in an ascending key; the writer states
  -- each key's placement (`Shim.null_order`).
  (none, "null_order", (ObsRow.shimmed "null_order" ["spark-null-order"]).proved "Shim.null_order"),
  (none, "clustered", (ObsRow.shimmed "sort on the keys" ["spark-clustered"]).tracking 271),
  -- After a shuffle, ties come in the order the partitions' rows arrive.
  (none, "tie_order", ({ ObsRow.native ["spark-sort-stability", "spark-window-values", "spark-rank"] with
    rerun := some { rows := .tiesPermuted, elements := .multiset },
    rerunEvidence := .probed ["spark-sort-stability", "spark-exec-parallel"] }).tracking 900),
  (none, "tie_pick", ({ ObsRow.native ["spark-first-last"] with
    rerun := some { rows := .tiesPermuted },
    rerunEvidence := .probed ["spark-first-last", "spark-exec-parallel"] }).tracking 900),
  -- Only starts from 1 reach Spark's `substring`, whose start 0 reads as 1
  -- (`Dialect.substring` of the writer).
  (none, "negative_start", (ObsRow.native ["spark-substring"]).tracking 271),
  (none, "case_sensitivity", (ObsRow.native ["spark-match-functions"]).tracking 271),
  (none, "string_positions", (ObsRow.native ["spark-strpos", "spark-substring"]).tracking 271),
  (none, "null_join_keys", (ObsRow.native ["spark-null-keys"]).tracking 271),
  (none, "window_sum_algo", (ObsRow.approxWithin "plan" ["spark-window-agg"]).tracking 900),
  (none, "stat_algo", ({ ObsRow.approxWithin "plan" ["spark-var-stddev", "spark-covar", "spark-corr"] with
    rerun := some { floats := .within "plan" } }).proved "FloatBounds.StdModel.core_var_chan"),
  -- `var_pop` and `stddev_pop` of one NaN are NaN (spark-var-pop-one-nan): Spark's
  -- variance needs no NaN guard, where DuckDB's does (DD-3). The SQL writer reads
  -- this row (`Dialect.var_nan`): without a shim, it writes Spark's own `VAR_*`.
  (some "agg.var", "stat_algo", ({ ObsRow.approxWithin "plan" ["spark-var-stddev", "spark-var-pop-one-nan"] with
    rerun := some { floats := .within "plan" },
    note := "Welford's update with Chan's merge meets StatProps on finite values (FloatBounds.StdModel.core_var_chan); a NaN among the values gives NaN, one NaN included (spark-var-pop-one-nan), so the written plan carries no NaN guard; an infinity raises first (#257)." }).proved
    "FloatBounds.StdModel.core_var_chan"),
  (none, "quantile_interp", (ObsRow.native ["spark-quantile"]).tracking 900),
  (none, "decimal_rescale", (ObsRow.native ["spark-decimal-arith"]).tracking 739),
  -- `-x` and `abs` round past 34 digits (SP-1); the writer's `0 - x` is exact
  -- where its type keeps the scale, and a type past 38 digits at a scale
  -- above 6, which Spark would round, is refused.
  (some "dec.arith", "overflow", (ObsRow.shimmed "decimal_negate_sub"
    ["spark-decimal-negate", "spark-decimal-arith"]).proved "Spark.decimal_negate_sub")]

theorem Profile.spark_leB : Profile.spark.table.leB Profile.core.table = true := by
  decide +kernel

theorem Profile.spark_le_core : Profile.spark.table.Le Profile.core.table :=
  ProfileTable.le_of_leB Profile.spark_leB

variable [Boxes.Ambient]

/-- `Allowed_spark ⊆ Allowed_core`. -/
theorem Rel.allowed_spark_core {cat : Catalog} {r : Rel} {out : Relation}
    (h : r.AllowedP Profile.spark.table cat out) : r.AllowedP Profile.core.table cat out :=
  Rel.AllowedP_mono Profile.spark_le_core h

end Substrait
