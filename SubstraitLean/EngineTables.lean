import Sverify.Engines.Transfer
import SubstraitLean.DuckDBFunctions
import SubstraitLean.SubstraitProfile
import Sverify.Polars.Tables

/-!
# Engine profiles as choice tables (#444, step 3a, prototype slice)

DuckDB's and Spark's choices and observation rows, from their facts
(`engines/duckdb/facts/`, `engines/spark/facts/`), pinned to
the versions those were probed at (D14). The rows cover the prototype slice:
integer `+ - × /` and `%`, `SUM` and `AVG` of integers and doubles, double
arithmetic, and an `ORDER BY`'s NULL order, clustering and ties, with what
these need (zeros, NaNs, rounding). Every other option is left as the core
has it (`loose` over its behaviours): not characterized, so anything.

Each table refines the core, by `decide` (`Profile.duckdb_le_core` for every
setting, `Profile.spark_le_core`), hence `Rel.AllowedP_mono` gives
`Allowed_E ⊆ Allowed_core`. `Profile.duckdb s`, the semantic profile the
lowering proves its shims against, stays as it is; its table names what it
models.

The rows' constructors (`ObsRow.native`, `ObsRow.shimmed`, …), `EngineProfile`
and the JSON the checker reports them in are engines-common
(`engines/Sverify/Engines/Tables.lean`); this module holds DuckDB's and
Spark's rows, Polars's are in `engines/polars/Sverify/Polars/Tables.lean`, and
`builtinEngines` lists all three.

Each observation row says how the engine's behaviour relates to the
reference's: an error-side option refines on the reference's non-raising
domain, so a verified plan needs no shim there (`docs/core-semantics.md`,
"What strictness buys"); a value-side one names its shim. -/

namespace Substrait

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
    (none, "round_zero_sign", .oneOf ["IEEE"]),
    -- C's `pow`: `power(1, ±∞)` is 1 (D40).
    (none, "pow_one_inf", .oneOf ["ONE"]),
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
    -- A segment tree of fanout 16 for framed windows, per-thread partials
    -- for a whole-partition frame, a running sum for a streaming running
    -- total, each frame anew without the optimizer (duckdb-window-sum-order).
    (none, "window_sum_algo", .oneOf ["TREE", "RUNNING_ADD", "RECOMPUTE"]),
    (none, "stat_algo", .oneOf ["WELFORD_CHAN"]),
    (none, "quantile_interp", .oneOf ["LINEAR"]),
    -- Not characterized on DuckDB yet: the core's behaviours.
    (none, "decimal_rescale", .loose ["TIE_AWAY_FROM_ZERO", "TIE_TO_EVEN", "TRUNCATE"])] ++
    uncharacterized prototypeSlice

def Profile.duckdb.obs : ObsTable := [
  (none, "overflow", (ObsRow.native ["duckdb-R1", "duckdb-R15-int-arith"]).tracking 241),
  -- `SUM(BIGINT)` is a `HUGEINT`; the written plan casts it back, which raises
  -- where the reference does: a type, not a value, so no shim.
  (some "agg.isum", "overflow", (ObsRow.native ["duckdb-R6"]).tracking 241),
  (none, "on_division_by_zero", (ObsRow.native ["duckdb-R2"]).tracking 241),
  (some "fp.div", "on_division_by_zero", (ObsRow.native ["duckdb-R5"]).tracking 241),
  (none, "on_domain_error", (ObsRow.native ["duckdb-R15-double-arith"]).tracking 241),
  (none, "division_type", (ObsRow.native ["duckdb-R3"]).tracking 241),
  (none, "min_mod_neg_one", (ObsRow.shimmed "MIN % -1 written out" ["duckdb-R15-int-modulus"]).proved "Lowering.duckdb_exact"),
  (none, "rounding", (ObsRow.native ["duckdb-float-ieee", "duckdb-ieee-arith-macos-arm64", "duckdb-ieee-arith-linux-x86-64"]).tracking 241),
  (none, "nan_creation", (ObsRow.native ["duckdb-R15-double-arith"]).tracking 241),
  -- Two zeros, as IEEE has them: the reference's up to one zero, or exactly
  -- after `Dialect.canon`.
  (none, "zero_sign", ({ ObsRow.upTo { zeros := .canon } ["duckdb-R14"] with
    shim := some "Dialect.canon" }).tracking 241),
  -- `round` and `ceil` emit IEEE's `-0.0`: the reference's up to one zero, or
  -- exactly after `Dialect.canon`.
  (none, "round_zero_sign", ({ ObsRow.upTo { zeros := .canon } ["duckdb-R15-round",
    "duckdb-R15-round-digits"] with shim := some "Dialect.canon" }).tracking 271),
  (none, "pow_one_inf", (ObsRow.native ["duckdb-pow-one-inf"]).tracking 271),
  (none, "nan_kind", (ObsRow.upTo { zeros := .canon } ["duckdb-signbit"]).tracking 241),
  (none, "nan_order", (ObsRow.native ["duckdb-arg-min-nulls"]).tracking 241),
  (none, "nan_equality", (ObsRow.native ["duckdb-nan-equality"]).tracking 241),
  -- Partials merged in finishing order are trees the reference allows, but a
  -- constant vector's `fl(k · x)` is not known to be one (#633): within #85's
  -- bound of the reference's correctly rounded sum (`StdModel.epsilon_sum_cr`).
  -- Which order depends on the parallel plan, so at two threads or more runs
  -- vary (3 to 4 values in 5 runs), each within the bound. `fsum` (Kahan)
  -- does not vary.
  (none, "sum_order", ObsRow.fsumOrder ["duckdb-sum-double", "duckdb-avg-double"]
    ["duckdb-sum-double", "duckdb-avg-double", "duckdb-exec-row-order"]
    "Sequential only at one thread; partials merged in finishing order at more threads or when spilled (ANY); a constant vector, or a constant-compressed segment, is added as one fl(k · x), which is not known to be a tree sum (#633). Every one of them is within the plan's bound of the reference's correctly rounded sum (StdModel.epsilon_sum_cr, D25)."),
  (some "agg.fsum", "rounding", ObsRow.fsumRounding
    ["duckdb-float-ieee", "duckdb-sum-double", "duckdb-avg-double"]
    "Each addition rounds to nearest, ties to even (duckdb-float-ieee); the sum is sequential runs merged in any tree, with a constant run as one fl(k · x) (duckdb-sum-double), and AVG divides it once by the count (duckdb-avg-double): StdModel.TreeSum (its const case) and fl(s / n), which epsilon_sum_cr and epsilon_avg_cr bound for any rounding to nearest."),
  (none, "avg_int_result", (ObsRow.native ["duckdb-R6"]).tracking 241),
  (none, "empty_group_aggregates", (ObsRow.native ["duckdb-sum-double", "duckdb-avg-int"]).tracking 241),
  (none, "null_order", (ObsRow.native ["duckdb-F2"]).tracking 241),
  -- The written `ORDER BY` is the model's sort, which `SortAllowed` allows for
  -- a clustered key (`Rel.duckdb_refines`; `test_realizability.py` runs it).
  (none, "clustered", (ObsRow.shimmed "ORDER BY the keys" []).proved "Rel.duckdb_refines"),
  -- Ties come in the order threads read the rows.
  -- `ORDER BY`, `row_number`, `ntile`, `lag` and `list` without a total order:
  -- ties, and a list's elements, come in a different order run to run.
  (none, "tie_order", ({ ObsRow.native ["duckdb-sort-ties", "duckdb-mode-ties"] with
    rerun := some { rows := .tiesPermuted, elements := .multiset },
    rerunEvidence := .probed ["duckdb-sort-ties", "duckdb-mode-ties", "duckdb-exec-row-order"] }).tracking 900),
  (none, "tie_pick", ({ ObsRow.native ["duckdb-mode-ties", "duckdb-arg-min-nulls"] with
    rerun := some { rows := .tiesPermuted },
    rerunEvidence := .probed ["duckdb-mode-ties", "duckdb-exec-row-order"] }).tracking 900),
  (some "fp.round", "rounding", (ObsRow.native ["duckdb-R15-round"]).tracking 241),
  (none, "float_overflow", (ObsRow.native ["duckdb-R15-double-arith"]).tracking 241),
  (none, "negative_start", (ObsRow.native ["duckdb-R13"]).tracking 241),
  (none, "case_sensitivity", (ObsRow.native ["duckdb-string-match-case"]).tracking 241),
  (none, "string_positions", (ObsRow.native ["duckdb-string-match-case", "duckdb-R13"]).tracking 241),
  (none, "null_join_keys", (ObsRow.native ["duckdb-null-keys"]).tracking 241),
  (none, "window_sum_algo", (ObsRow.approxWithin "plan" ["duckdb-window-sum-order"]).tracking 900),
  -- Welford with Chan's merge meets the generic properties the reference allows:
  -- `float-bounds` proves `VAR_*`, `COVAR_*` and DuckDB's `CORR` formula within
  -- `StatProps` (`core_var_chan`, `core_cov_chan`, `core_corr_chan`; `STDDEV_*`
  -- by `core_stddev` of the variance), for IEEE rounding (`Mono`, `Grid`).
  -- D30: the reference's statistics are the exact moments rounded once, so
  -- DuckDB's are within the plan's bound of them (`Epsilon.statEps`).
  (none, "stat_algo", ({ ObsRow.approxWithin "plan" ["duckdb-var-stddev", "duckdb-covar", "duckdb-corr"] with
    rerun := some { floats := .within "plan" } }).proved "FloatBounds.StdModel.core_var_chan"),
  -- `VAR_POP` and `STDDEV_POP` of one value are 0 on DuckDB, NaN included
  -- (DD-3), where the reference gives NaN; sverify's SQL returns NaN for a
  -- NaN among the values. `core_var_chan` covers finite values, the guard
  -- the rest (`Stat.nanGuard_varStat`).
  (some "agg.var", "stat_algo", ({ ObsRow.approxWithin "plan" ["duckdb-var-stddev", "duckdb-var-pop-one-value"] with
    shim := some "nan_through",
    rerun := some { floats := .within "plan" },
    note := "Welford with Chan's merge meets StatProps on finite values (FloatBounds.StdModel.core_var_chan); DuckDB's VAR_POP and STDDEV_POP of one value are 0 even for NaN (DD-3), so the written plan returns NaN where a value is NaN (nan_through), which meets StatProps everywhere without an infinity (Stat.nanGuard_varStat); an infinity raises first (#257)." }).proved
    "Stat.nanGuard_varStat"),
  (none, "quantile_interp", (ObsRow.native ["duckdb-quantile-cont-interpolation"]).tracking 900)]

/-! ## Spark -/

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

/-! ## The engines -/

/-- The engine profiles of this repository, DuckDB under its default
settings. Each one's shims are named as its rows name them; Polars's are
`engines/polars/src/sverify_polars/shims.py`'s `SHIMS` (named as their lemmas
`Polars.<name>`), which `tests/test_realizability.py` checks against these. -/
def builtinEngines : List EngineProfile := [
  { table := Profile.duckdb.table {}, obs := withReruns Profile.duckdb.obs,
    translationTheorem := "Rel.duckdb_refines",
    shims := [("MIN % -1 written out", .expression), ("Dialect.canon", .expression),
      ("ORDER BY the keys", .sort), ("nan_through", .expression)] },
  { table := Profile.polars.table, obs := withReruns Profile.polars.obs,
    translationTheorem := "Rel.polars_sound", executes := "streaming", asReference := true,
    shims := [("null_order", .argument), ("round_half_away", .argument),
      ("int_div_trunc", .expression), ("int_mod_trunc", .expression),
      ("sum_empty_null", .expression), ("avg_int_declared", .expression),
      ("one_zero", .expression), ("strpos_chars", .expression),
      ("substring_wrap", .expression), ("column_divisor", .expression),
      ("decimal_round_half_away", .expression), ("decimal_div_half_away", .expression),
      ("max_nan_greatest", .expression), ("nan_through", .expression),
      ("sort on the keys", .sort)] },
  { table := Profile.spark.table, obs := withReruns Profile.spark.obs,
    translationTheorem := "Rel.spark_sound", executes := "batch",
    shims := [("int_sum_decimal", .expression), ("int_avg_decimal", .expression),
      ("Dialect.canon", .expression), ("null_order", .argument), ("sort on the keys", .sort),
      ("decimal_negate_sub", .expression)] }]

/-! Each table's test against the core (`ProfileTable.leB`), decided once in
the kernel: the refinements below and `builtinEngines_leCore` both use it. -/

theorem Profile.duckdb_leB (s : DuckDBSettings) :
    (Profile.duckdb.table s).leB Profile.core.table = true := by
  obtain ⟨e, i⟩ := s
  cases e <;> cases i <;> decide +kernel

theorem Profile.spark_leB : Profile.spark.table.leB Profile.core.table = true := by
  decide +kernel

/-- **Every DuckDB setting refines the core.** -/
theorem Profile.duckdb_le_core (s : DuckDBSettings) : (Profile.duckdb.table s).Le Profile.core.table :=
  ProfileTable.le_of_leB (Profile.duckdb_leB s)

theorem Profile.spark_le_core : Profile.spark.table.Le Profile.core.table :=
  ProfileTable.le_of_leB Profile.spark_leB

variable [Boxes.Ambient]
/-- `Allowed_duckdb ⊆ Allowed_core`, for every setting. -/
theorem Rel.allowed_duckdb_core (s : DuckDBSettings) {cat : Catalog} {r : Rel} {out : Relation}
    (h : r.AllowedP (Profile.duckdb.table s) cat out) : r.AllowedP Profile.core.table cat out :=
  Rel.AllowedP_mono (Profile.duckdb_le_core s) h

/-- `Allowed_spark ⊆ Allowed_core`. -/
theorem Rel.allowed_spark_core {cat : Catalog} {r : Rel} {out : Relation}
    (h : r.AllowedP Profile.spark.table cat out) : r.AllowedP Profile.core.table cat out :=
  Rel.AllowedP_mono Profile.spark_le_core h

example : builtinEngines.all (·.rowsWf) := by decide +kernel

open Lean (Json toJson) in
/-- `substrait-check --options`: the options, the groups' options, each
profile's choices and observation rows (the engines `es`), the profiles'
versions, and the tool table. -/
def tablesJson (es : List EngineProfile) : Json :=
  optionsJson
    |>.setObjVal! "choices" (Json.mkObj ([
        ("reference", profileRowsJson Profile.reference.table Profile.reference.obs true),
        ("core", choicesJson Profile.core.table),
        ("substrait", profileRowsJson Profile.substrait.table Profile.substrait.obs false)] ++
      es.map fun e => (e.name, profileRowsJson e.table e.obs false)))
    |>.setObjVal! "profiles" (Json.mkObj ([
        ("reference", Json.mkObj [("engine", Json.null)]),
        ("core", Json.mkObj [("engine", Json.null)]),
        ("substrait", Json.mkObj [("engine", Json.null), ("yaml", toJson Profile.substrait.table.version)])] ++
      es.map fun e => (e.name, Json.mkObj [
        ("engine", toJson e.name), ("versions", toJson [e.table.version]),
        ("executes", toJson e.executes),
        ("missing", Json.arr <| (e.table.missing.map fun (f, ids) =>
          Json.mkObj [("function", toJson f), ("facts", toJson ids)]).toArray)])))
    |>.setObjVal! "observations" (Json.mkObj ([("reference", obsTableJson Profile.reference.obs),
        ("substrait", obsTableJson Profile.substrait.obs)] ++
      es.map fun e => (e.name, obsTableJson e.obs)))
    |>.setObjVal! "versions" (Json.mkObj (es.map fun e => (e.name, toJson e.table.version)))
    |>.setObjVal! "tools" (toolsJson es)
    |>.setObjVal! "levels" obsLevelsJson

/-! ## The dependency and transfer reports, over these profiles (`engines/Sverify/Engines/Transfer.lean`) -/

/-- The profiles a report compares. -/
def reportProfiles (es : List EngineProfile) : List (ProfileTable × ObsTable) :=
  (Profile.reference.table, Profile.reference.obs) ::
    (Profile.substrait.table, Profile.substrait.obs) :: es.map fun e => (e.table, e.obs)

open Lean (Json toJson) in
/-- `substrait-check --dependencies`: the options the plan meets, each with
every profile's choice and observation row; per pair of profiles whether a
proof under the first holds under the second (`transferB`); and per engine
the shims its translation from the reference needs for this plan. -/
def Rel.dependenciesJson (es : List EngineProfile) (r : Rel) : Json :=
  let reads := r.reads.eraseDups
  let choiceAt (t : ProfileTable) (p : Read) : Json :=
    match t.choice? p.1 p.2.1 with | some c => c.json | none => Json.null
  let rowAt (obs : ObsTable) (p : Read) : Json :=
    match obs.row? p.1 p.2.1 with | some row => row.json | none => Json.null
  Json.mkObj [
    ("options", Json.arr <| (reads.map fun p => Json.mkObj ([
      ("group", toJson p.1), ("option", toJson p.2.1), ("preferences", toJson p.2.2),
      ("tool", toJson ((Profile.reference.tools.find? (·.option == p.2.1)).map fun t =>
        match t.tool with | .raise => "raise" | .choose => "choose" | .leaveOpen => "leave_open"))] ++
      (reportProfiles es).map fun (t, obs) => (t.name, Json.mkObj [
        ("choice", choiceAt t p), ("allows", toJson (t.allows p.1 p.2.1 p.2.2)),
        ("row", rowAt obs p), ("version", toJson t.version)]))).toArray),
    ("transfer", Json.mkObj ((reportProfiles es).map fun (t, _) => (t.name,
      Json.mkObj ((reportProfiles es).map fun (u, _) => (u.name, toJson (transferB r t u)))))),
    ("functions", toJson r.functions),
    ("missing", Json.mkObj (es.map fun e => (e.name,
      Json.arr <| ((e.table.missingIn r.functions).map fun (f, ids) =>
        Json.mkObj [("function", toJson f), ("facts", toJson ids)]).toArray))),
    -- A shim the plan needs at an option, unless every read there states a
    -- preference the engine gives as stated (a key's `NULLS LAST` on Polars):
    -- the shim is for the reference's default (#444, step 3b).
    ("shims", Json.mkObj (es.map fun e => (e.name,
      Json.arr <| ((reads.map fun p => (p.1, p.2.1)).eraseDups.filterMap fun (g, o) =>
        let stated := reads.filter fun p => p.1 == g && p.2.1 == o
        if stated.all (fun p => !p.2.2.isEmpty &&
            (e.table.allows g o p.2.2).all (Profile.reference.table.allows g o p.2.2).contains) then none
        else (e.obs.row? g o).bind fun row => row.shim.map fun sh =>
          Json.mkObj [("group", toJson g), ("option", toJson o), ("shim", toJson sh)]).toArray)))]

/-- The profiles by name: the reference, the core, Substrait, and the engines
(DuckDB under its default settings). -/
def profileNamed (es : List EngineProfile) (name : String) : Option (ProfileTable × ObsTable) :=
  ((Profile.reference.table, Profile.reference.obs) :: (Profile.core.table, []) ::
    (Profile.substrait.table, Profile.substrait.obs) :: es.map fun e => (e.table, e.obs)).find?
    (·.1.name == name)

open Lean (Json toJson) in
/-- `substrait-check --transfer`, on stdin `{"from": P, "to": E, "depends":
[{"group", "option", "preferences"?, "behaviours"?}], "functions"?: [...]}`:
whether a proof under `P` that uses only `depends` holds under `E`. Each row
fails where `E` allows a behaviour not below one the proof used (`behaviourLe`;
`behaviours`, or else all `P` allows there), and each function `E` lacks fails. With
`depends` = `Rel.reads` and no `behaviours`, this is `transferB`, which
`Rel.transfer_of_transferB` proves sound. -/
def transferJson (es : List EngineProfile) (input : Json) : Except String Json := do
  let name (k : String) : Except String (ProfileTable × ObsTable) := do
    let n ← input.getObjValAs? String k
    match profileNamed es n with
    | some p => pure p
    | none => throw s!"unknown profile {n}"
  let (P, _) ← name "from"
  let (E, obsE) ← name "to"
  let rows := (input.getObjValAs? (Array Json) "depends").toOption.getD #[]
  let mut failures : Array Json := #[]
  for row in rows do
    let group := (row.getObjValAs? String "group").toOption
    let option ← row.getObjValAs? String "option"
    let ps := (row.getObjValAs? (List String) "preferences").toOption.getD []
    let used := (row.getObjValAs? (List String) "behaviours").toOption.getD (P.allowsAt group option ps)
    let target := E.allowsAt group option ps
    unless target.all (fun b => used.any (behaviourLe option b ·)) do
      failures := failures.push (Json.mkObj [("group", toJson group), ("option", toJson option),
        ("from", toJson used), ("to", toJson target), ("facts", toJson (obsE.factsAt group option))])
  let fns := (input.getObjValAs? (List String) "functions").toOption.getD []
  for (f, ids) in E.missingIn fns do
    failures := failures.push (Json.mkObj [("function", toJson f), ("facts", toJson ids)])
  return Json.mkObj [("ok", toJson failures.isEmpty), ("failures", Json.arr failures)]

end Substrait
