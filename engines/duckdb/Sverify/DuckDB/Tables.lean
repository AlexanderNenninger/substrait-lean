import Sverify.Engines.Tables
import Sverify.DuckDB.Functions

/-!
# DuckDB's choice table and observation rows (#444, step 3a)

DuckDB's choices and observation rows, from its facts
(`engines/duckdb/facts/`), pinned to the version they were probed at (D14).
The rows cover the prototype slice: integer `+ - × /` and `%`, `SUM` and
`AVG` of integers and doubles, double arithmetic, and an `ORDER BY`'s NULL
order, clustering and ties, with what these need (zeros, NaNs, rounding).
Decimal rows state the SQL the printer writes, which `Profile.duckdb` models,
so they are tested and never proved until DuckDB's own decimal functions are
in the profile (#1985).
Every other option is left as the core has it (`loose` over its behaviours):
not characterized, so anything.

The table refines the core for every setting, by `decide`
(`Profile.duckdb_le_core`), hence `Rel.AllowedP_mono` gives
`Allowed_duckdb ⊆ Allowed_core`. `Profile.duckdb s`, the semantic profile the
lowering proves its shims against, stays as it is; its table names what it
models.

Each observation row says how the engine's behaviour relates to the
reference's: an error-side option refines on the reference's non-raising
domain, so a verified plan needs no shim there (`docs/core-semantics.md`,
"What strictness buys"); a value-side one names its shim. The machinery is
engines-common (`engines/Sverify/Engines/Tables.lean`); `builtinEngines`
(`SubstraitLean/EngineTables.lean`) lists this table beside the others.
-/

namespace Substrait

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
    (none, "zero_sign", .oneOf ["ONE_ZERO"]),
    (none, "round_zero_sign", .oneOf ["IEEE"]),
    -- C's `pow`: `power(1, ±∞)` is 1 (D40).
    (none, "pow_one_inf", .oneOf ["ONE"]),
    (none, "nan_kind", .oneOf ["IEEE"]),
    (none, "nan_order", .oneOf ["GREATEST"]),
    (none, "nan_equality", .oneOf ["NAN_IS_NAN"]),
    -- A NULL element sorts above every value, in `<` and in MIN and MAX (duckdb-R11).
    (none, "list_null_order", .oneOf ["GREATEST"]),
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
  -- A default row covers every group that takes its option: `proved` where the
  -- listed facts support the model at each of them; a group they do not cover
  -- has a row of its own (ruling 185).
  (none, "overflow", (ObsRow.native ["duckdb-R1", "duckdb-R15-int-arith", "duckdb-R1-min",
    "duckdb-R15-int-modulus"]).proved "Lowering.duckdb_exact"),
  -- DuckDB's `power` is of doubles (duckdb-int-pow): sverify writes an integer
  -- power as checked products, a shim, tested; integer powers are After 1.0
  -- (ruling 227). Decimals are as the printer writes them (`Profile.duckdb`
  -- states that SQL, not DuckDB's own functions): tested, not proved.
  (some "int.pow", "overflow", (ObsRow.shimmed "integer power as checked products"
    ["duckdb-int-pow"]).tracking 1985),
  (some "dec.arith", "overflow", (ObsRow.native ["duckdb-decimal-arith"]).tracking 1985),
  -- Decimal `%` truncates and raises by zero as the reference (D62); its type
  -- is wider, and the written plan casts it back (duckdb-decimal-modulus).
  (some "dec.mod", "division_type", (ObsRow.native ["duckdb-decimal-modulus"]).tracking 1985),
  (some "dec.mod", "on_division_by_zero", (ObsRow.native ["duckdb-decimal-modulus"]).tracking 1985),
  -- `SUM(BIGINT)` is a `HUGEINT`; the written plan casts it back, which raises
  -- where the reference does: a type, not a value, so no shim.
  (some "agg.isum", "overflow", (ObsRow.native ["duckdb-R6"]).tracking 1985),
  (none, "on_division_by_zero", (ObsRow.native ["duckdb-R2", "duckdb-R15-int-divide", "duckdb-R3",
    "duckdb-R4", "duckdb-R15-double-modulus"]).proved "Lowering.duckdb_exact"),
  (some "fp.div", "on_division_by_zero", (ObsRow.native ["duckdb-R5", "duckdb-R15-double-arith"]).proved
    "Lowering.duckdb_exact"),
  (none, "on_domain_error", (ObsRow.native ["duckdb-R15-double-arith", "duckdb-int-div-domain",
    "duckdb-R15-math-domain", "duckdb-R15-atan2"]).proved "Lowering.duckdb_exact"),
  (some "int.pow", "on_domain_error", (ObsRow.shimmed "integer power as checked products"
    ["duckdb-int-pow"]).tracking 1985),
  -- DuckDB's `log(b, x)` is `ln x / ln b`, NaN or `±inf` outside the domain with
  -- `ieee_floating_point_ops` on (duckdb-R15-math-domain). `Profile.duckdb` has no
  -- `flogb` case, so the lowering's entry is native and the reference's raise comes
  -- from the writer's guard (`float_logb` under `domain`), tested. #1985 states
  -- DuckDB's quotient in the profile and generates the guard.
  (some "fp.log", "on_domain_error", (ObsRow.shimmed "log(b, x) domain guard"
    ["duckdb-R15-math-domain"]).tracking 1985),
  -- `//`, `%` and `%` of doubles truncate (duckdb-R2, duckdb-int-div-domain,
  -- duckdb-R3, duckdb-R15-double-modulus), as `Profile.duckdb` states them.
  (none, "division_type", (ObsRow.native ["duckdb-R2", "duckdb-int-div-domain", "duckdb-R3",
    "duckdb-R15-double-modulus"]).proved "Lowering.duckdb_exact"),
  (none, "min_mod_neg_one", (ObsRow.shimmed "MIN % -1 written out" ["duckdb-R15-int-modulus"]).proved "Lowering.duckdb_exact"),
  (none, "rounding", (ObsRow.native ["duckdb-float-ieee", "duckdb-ieee-arith-macos-arm64", "duckdb-ieee-arith-linux-x86-64"]).tracking 1985),
  (none, "nan_creation", (ObsRow.native ["duckdb-R15-double-arith", "duckdb-R15-double-modulus",
    "duckdb-nonfinite-aggregates"]).proved "Rel.duckdb_shim_sound"),
  -- Values are raw (D31), and the zeros are one at `=`, `<`, keys and
  -- partitions, as the reference has them. A group's MIN, MAX and QUANTILE_DISC
  -- return a member of the class (D31, D45); quantiles print canonical too.
  -- DuckDB's pick among equal zeros depends on row order (duckdb-minmax-zero-sign),
  -- so the writer prints the class's canonical value for them and for keys
  -- (`Dialect.zero_rep`): a rerun gives the same sign. A frame's value prints
  -- canonical, and the reference pins it until D45's window amendment.
  (none, "zero_sign", ({ ObsRow.native ["duckdb-R14", "duckdb-float-signs", "duckdb-minmax-zero-sign"] with
    rerun := some Obs.exact,
    rerunEvidence := .probed ["duckdb-minmax-zero-sign", "duckdb-R14", "duckdb-float-signs"] }).tracking 1985),
  -- `round` and `ceil` emit IEEE's `-0.0`: the reference's up to one zero, or
  -- exactly through the proved template (`Lowering.zeroTemplate`).
  (none, "round_zero_sign", ({ ObsRow.upTo { zeros := .canon } ["duckdb-R15-round"]
    with shim := some "round: 0.0 for a negative value that rounds to zero" }).proved
    "Lowering.duckdb_exact"),
  (none, "pow_one_inf", (ObsRow.native ["duckdb-pow-one-inf"]).proved "Lowering.duckdb_exact"),
  (none, "nan_kind", (ObsRow.upTo { zeros := .canon } ["duckdb-signbit"]).tracking 1985),
  (none, "nan_order", (ObsRow.native ["duckdb-arg-min-nulls"]).tracking 1985),
  (none, "nan_equality", (ObsRow.native ["duckdb-nan-equality"]).proved "Lowering.duckdb_exact"),
  -- `<` of lists is NULL where a NULL element decides it, which DuckDB gives as FALSE or TRUE:
  -- the written `list_lt` finds the first distinct position (`Dialect.list_lt`). MIN and MAX
  -- of lists order a NULL element greatest, as the reference does at `agg.order`.
  (none, "list_null_order", (ObsRow.shimmed "list_lt" ["duckdb-R11"]).tracking 1484),
  (some "agg.order", "list_null_order", (ObsRow.native ["duckdb-R11"]).tracking 1484),
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
  (none, "avg_int_result", (ObsRow.native ["duckdb-R6"]).tracking 1985),
  (none, "empty_group_aggregates", (ObsRow.native ["duckdb-sum-double", "duckdb-avg-int"]).tracking 1985),
  -- The printer writes every key's placement (`NULLS FIRST`/`LAST`).
  (none, "null_order", (ObsRow.shimmed "null_order" ["duckdb-F2"]).proved "Shim.null_order"),
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
  (some "fp.round", "rounding", (ObsRow.native ["duckdb-R15-round"]).proved "Lowering.duckdb_exact"),
  (none, "float_overflow", (ObsRow.native ["duckdb-R15-double-arith"]).tracking 1985),
  -- The string functions are the reference's in `Profile.duckdb`, as the facts
  -- find DuckDB's (`substring` wraps from the end, `LIKE` is case-sensitive).
  (none, "negative_start", (ObsRow.native ["duckdb-R13"]).proved "Lowering.duckdb_exact"),
  (none, "case_sensitivity", (ObsRow.native ["duckdb-string-match-case"]).proved
    "Lowering.duckdb_exact"),
  (none, "string_positions", (ObsRow.native ["duckdb-string-match-case", "duckdb-R13"]).proved
    "Lowering.duckdb_exact"),
  (none, "null_join_keys", (ObsRow.native ["duckdb-null-keys"]).tracking 1985),
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
  -- `LINEAR` is DuckDB's own `quantile_cont`: the neighbours of its double
  -- position, an ulp past them where the lower neighbour is first (findings A
  -- and B, #900). The written plan guards both (`Dialect.quantile`, #1502), which
  -- the shim names, and meets `BETWEEN`.
  (none, "quantile_interp", ({ ObsRow.shimmed "quantile_guard" ["duckdb-quantile-cont-interpolation", "tests/test_duckdb_quantile_900.py::test_the_whole_positions_the_double_misses_give_the_model_value", "tests/test_duckdb_quantile_900.py::test_a_random_group_stays_between_the_neighbours"] with
    precondition := "(COUNT(x) − 1)·10^scale < 2^52 for the decimal fraction's scale, checked on the data (the written plan raises past it)",
    note := "`LINEAR` states DuckDB's own `quantile_cont`, which leaves the model's neighbours at a whole exact position its double misses and where the lower neighbour is first; the written plan takes `quantile_disc` at a whole exact position and bounds the first lower neighbour by the second smallest value (python/tests/test_duckdb_quantile_900.py)." }).tracking 900)]

-- No decimal row is proved: `Profile.duckdb` states decimals as the printer
-- writes them, not DuckDB's own functions (ruling 185, #1985).
#guard Profile.duckdb.obs.all fun (g, _, r) =>
  !(g.any (·.startsWith "dec.")) || match r.evidence with | .proved _ _ => false | _ => true

/-- What each shim DuckDB's rows name costs at run time. -/
def Profile.duckdb.shimCosts : List (String × ShimCost) :=
  [("MIN % -1 written out", .expression), ("round: 0.0 for a negative value that rounds to zero", .expression),
   ("ORDER BY the keys", .sort), ("nan_through", .expression), ("quantile_guard", .expression),
   ("null_order", .argument), ("list_lt", .expression), ("log(b, x) domain guard", .expression),
   ("integer power as checked products", .expression)]

/-- The table's test against the core (`ProfileTable.leB`), decided once in
the kernel for every setting. -/
theorem Profile.duckdb_leB (s : DuckDBSettings) :
    (Profile.duckdb.table s).leB Profile.core.table = true := by
  obtain ⟨e, i⟩ := s
  cases e <;> cases i <;> decide +kernel

/-- **Every DuckDB setting refines the core.** -/
theorem Profile.duckdb_le_core (s : DuckDBSettings) : (Profile.duckdb.table s).Le Profile.core.table :=
  ProfileTable.le_of_leB (Profile.duckdb_leB s)

variable [Boxes.Ambient]

/-- `Allowed_duckdb ⊆ Allowed_core`, for every setting. -/
theorem Rel.allowed_duckdb_core (s : DuckDBSettings) {cat : Catalog} {r : Rel} {out : Relation}
    (h : r.AllowedP (Profile.duckdb.table s) cat out) : r.AllowedP Profile.core.table cat out :=
  Rel.AllowedP_mono (Profile.duckdb_le_core s) h

end Substrait
