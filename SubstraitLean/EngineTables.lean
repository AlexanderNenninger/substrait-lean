import Sverify.Engines.Transfer
import SubstraitLean.DuckDBProfile
import SubstraitLean.SubstraitProfile

/-!
# Engine profiles as choice tables (#444, step 3a, prototype slice)

DuckDB's, Polars's and Spark's choices and observation rows, from their facts
(`engines/duckdb/facts/`, `engines/polars/facts/`,
`engines/spark/facts/`), pinned to
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

The rows' constructors (`ObsRow.native`, `ObsRow.shimmed`, …), `EngineProfile`
and the JSON the checker reports them in are engines-common
(`engines/Sverify/Engines/Tables.lean`); this module holds each engine's rows.

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
    (none, "round_zero_sign", .oneOf ["IEEE"]),
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
    translationTheorem := "Rel.spark_sound", executes := "batch", asReference := true,
    shims := [("int_sum_decimal", .expression), ("int_avg_decimal", .expression),
      ("Dialect.canon", .expression), ("null_order", .argument), ("sort on the keys", .sort),
      ("decimal_negate_sub", .expression)] }]

/-! Each table's test against the core (`ProfileTable.leB`), decided once in
the kernel: the refinements below and `builtinEngines_leCore` both use it. -/

theorem Profile.duckdb_leB (s : DuckDBSettings) :
    (Profile.duckdb.table s).leB Profile.core.table = true := by
  obtain ⟨e, i⟩ := s
  cases e <;> cases i <;> decide +kernel

theorem Profile.polars_leB : Profile.polars.table.leB Profile.core.table = true := by
  decide +kernel

theorem Profile.spark_leB : Profile.spark.table.leB Profile.core.table = true := by
  decide +kernel

/-- **Every DuckDB setting refines the core.** -/
theorem Profile.duckdb_le_core (s : DuckDBSettings) : (Profile.duckdb.table s).Le Profile.core.table :=
  ProfileTable.le_of_leB (Profile.duckdb_leB s)

theorem Profile.polars_le_core : Profile.polars.table.Le Profile.core.table :=
  ProfileTable.le_of_leB Profile.polars_leB

theorem Profile.spark_le_core : Profile.spark.table.Le Profile.core.table :=
  ProfileTable.le_of_leB Profile.spark_leB

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
