# Proved theorems

The theorems behind each guarantee, with the Lean names they go by, moved here from
[how-it-works.md](how-it-works.md#what-is-proved) so that the explanation keeps the user's terms. [proofs.md](proofs.md#the-guarantees-and-their-theorems) names
every guarantee with its theorem, its layer and its module; the sections below explain the main ones.

## Contracts

[Contracts.lean](../analysis/Sverify/Analysis/Contracts.lean) is an abstract interpreter
over `Rel`. Each column gets an `AVal`, a set of possible values: whether it can be NULL, an integer
interval, possible booleans, and whether it can be a string, with the strings
it can be when they are few: at most `strCap` (64) of them, past that any string.

* `Expr.abs_sound`: abstract evaluation of expressions is sound, including SQL's
  three-valued `AND`/`OR`, NULL-propagating arithmetic and comparisons.
* `Expr.refine_sound`: a row that passes a filter satisfies what the condition
  says about its columns.
* `Expr.factsOf_sound`, `Rel.facts_sound`: relational facts (`x − y ∈ [lo, hi]`,
  `x ≠ k`) taken from filter and join conditions hold on every output row. They
  survive projections, emits, joins, NULL padding and unions.
  A fact `holds e` keeps a whole condition, a conjunct of a precondition or
  of a filter or inner join condition (`Expr.conjuncts_sound`): projections
  rename its columns (`Expr.eval_mapFields`), and a left join drops those of
  its right side, which NULL padding may break.
* `Expr.refineOr_sound`, `useFacts_sound`: a row on which `p OR q` is TRUE,
  and `p` cannot be TRUE under the columns' description, has `q` TRUE, so
  `q` refines the columns; a `CASE` whose condition is decided is its branch.
  `Rel.aeval` applies the whole conditions at each table and filter, and
  `Expr.absD` in each `CASE` branch and on the right of each `OR`.
  `Expr.absF_sound`: a projected condition that is a `holds` fact is TRUE.
* `Expr.absD_sound`: evaluating expressions with those facts (sharpening
  `x − y`, `x < y`, `x = y` and `x = k`) is sound. Each `CASE` branch is
  evaluated knowing whether its condition is TRUE: `Expr.cstr_sound` turns
  `IS NULL` and comparisons with constants into constraints on the tested
  expression (or its negation), and `Expr.refineNeg_sound` refines columns
  where a condition is not TRUE. This is how `clip`, `abs`, `greatest` and
  `least` get their bounds. `Expr.refine_sound` also covers `OR` and
  `IS NULL`, so a filter `x IN (1, 2, 3)` gives `x ∈ [1, 3]` and
  `x IS NULL OR x >= 0` gives "NULL or ≥ 0". `p OR q` is evaluated with `q`
  refined where `p` is not TRUE, also when `p` may be NULL (`orSplitNull`),
  which proves `x >= 0 OR x IS NULL` for a nullable `x`.
  A string constant is that one string, `s = 'k'` and `s IN ('a', 'b')`
  narrow a column to those strings, `s <> 'k'` and `NOT IN` take them out,
  and `CASE`, `COALESCE` and `UNION ALL` join the sets (`AVal.strs`),
  so a filter `status <> 'cancelled'` over a source whose `status` is one of
  four strings proves `status IN ('placed', 'shipped', 'returned')`.
* `Rel.keys_sound` ([Keys.lean](../analysis/Sverify/Analysis/Keys.lean)): derived keys hold. No two
  output rows agree on them.
* `Rel.optimize_sound` ([Semantic.lean](../SubstraitLean/Semantic.lean)): the
  rewrites a contract's keys and facts allow keep a plan's rows, on data that
  meets the preconditions. A `DISTINCT` or measure-less `GROUP BY` over a key
  goes, and so does the `DISTINCT` of `COUNT(DISTINCT id)` with `id` a key.
  A filter the preconditions imply goes; one they rule out empties the plan.
  A left join on a NOT NULL foreign key (`sv.references`) becomes an inner
  join, and so does one under a filter that rejects its padded rows. A join
  whose condition hits a key of the right side goes when nothing reads the
  right side's columns (for an inner join, given a NOT NULL foreign key).
  A `GROUP BY` column that the other grouping columns determine (functional
  dependencies from keys and equalities, `Rel.fds_sound`) moves into a `MIN`.
  A `GROUP BY` of left columns over a join on a key of the right side is
  computed before the join (eager aggregation).
  `sv.verify(...).optimized` is the rewritten plan.
* Key rules for ASOF (all in `Rel.keys_sound`): `ROW_NUMBER()` with the partition
  columns is a key (`windowRows_rowNumber_key`); a column `$i + c` of a non-NULL
  integer column can stand in for it in a key; a filter `$i = k` drops `i` from
  keys; join keys drop right-key columns the condition ties to the left side
  (`a.device = b.device`), for inner and left joins. A key of each branch of
  a `UNION ALL`, with a column whose values the branches cannot share (a
  constant tag, a `GROUPING` level), is a key of the union (`AVal.disjoint_ne`).
* `window_tiebreak`, `Rel.window_deterministic` ([Keys.lean](../analysis/Sverify/Analysis/Keys.lean)):
  when a window's partition and sort columns contain a key of its input, every
  arrangement of the input sorted by the window's keys gives the same rows as
  `Rel.eval`. So the proofs describe what an engine computes, however it breaks ties.
* `orderFact_sound`, `winFacts_sound`, `WinFn.abs_sound`: what is known about
  `LAG`/`LEAD`/`ROW_NUMBER` columns holds. Strict order uses an oracle saying
  which windows have a key (`WindowKeys`); `Rel.keyedWindows_soundAll` proves the
  one computed from `Rel.keys` right, which is what `contract_sound` asks for.
* `IoT.window_complete` ([Completeness.lean](../SubstraitLean/Completeness.lean)): the
  converse of the contracts. If both sensors have valid readings at `t` and `t + 60`,
  the window at `t` is in the output, so no window is lost. It's built from one
  membership lemma per operator.

Doubles are modelled as exact integer codes (each double is a multiple of 2⁻¹⁰⁷⁴),
`-0.0` and the negative NaN included, and timestamps as microseconds; see
[Float.lean](../core/Sverify/Core/Float.lean) and
[FloatFormat.lean](../core/Sverify/Core/FloatFormat.lean). `+ − × ÷` compute on the
codes, the exact result rounded once
([exact, rounded once](reference-semantics.md#floating-point),
[FloatArith.lean](../core/Sverify/Core/FloatArith.lean)). The conversions between
codes and native floats, which `pow`, `log` and the other libm functions use,
are trusted code.

* `Rel.aeval_sound`: every row a well-formed plan produces is described by `Rel.aeval`.
* `Rel.colExprs_eval`: a precondition plan (`orders.select(cond, ...)`) computes its
  conditions row by row, so "all its columns are TRUE" is the precondition.
* `contract_sound`: suppose every input row matches its schema and satisfies its
  preconditions. If every column of the postcondition plan is certainly TRUE,
  then every output row satisfies every postcondition.

Trusted: the schema description taken from `baseSchema` types and nullability, and
the JSON plumbing.

## Composition

[Compose.lean](../SubstraitLean/Compose.lean) builds on `contract_sound`,
`Rel.keys_sound` and `Rel.delta_correct`, with no induction over plans:

* `Triple.compose`: Hoare triples over queries compose, `{P} g {Q}` and
  `{Q} f {S}` give `{P} f ∘ g {S}`, where `f ∘ g` reads `g`'s output as one of
  its tables. `Triple.of_contract`, `Triple.of_keys` and `Triple.of_aeval` turn
  what the checker proves into triples; `Triple.compose_spec` is the rule as
  `sverify` applies it.
* `RowsSat.update`, `KeyOn.update`, `Spec.update`: a table's contract survives a
  batch if the inserted rows satisfy the row conditions and their keys clash
  with neither each other nor the kept rows. `Triple.maintained`: a contracted
  view's guarantees then hold in the new state.
* `Rel.chain_sound`: when a view reads another view's materialized result and
  gets that view's delta-plan output as its change table, its own delta plan is
  correct (DBSP's chain rule). `Rel.stack_sound` holds for any upstream change;
  `ZSet.diff_correct` shows a recomputed view's `new − old` is one.

## Runtime errors

[Safety.lean](../analysis/Sverify/Analysis/Safety.lean) proves that a transformation runs without
runtime errors, or reports what may go wrong. `sverify` reports these as
`may fail: …` (a `VerificationError` from `@sv.transform`). A `SUM` that
may overflow is assumed to fit, `assumes: SUM of … fits 64 bits in every
group (checked at run time: the job raises if it does not …)` (or
`fits DECIMAL(38, 2)` for a decimal `SUM`), and is an error with
`on_inferred="off"`.

* Errors, where the engines fail: integer division or remainder by zero, `MIN / -1`,
  integer `POWER` with a negative exponent or a result outside 64 bits,
  `CAST(double AS BIGINT)` of NaN, ±∞ or an out-of-range value, a regular expression
  that may not compile, and calendar functions (`date_part`, `date_trunc` to a week or
  longer, `date_bin`, `strftime`, adding months) outside the reference's timestamps,
  0001-01-01 to 9999-12-31.
* `+`, `-`, `*` and negation leaving their declared width (64 bits, or narrower
  integers), and `date_trunc` to a day or less below `-2⁶³` µs, are errors too: the
  reference raises.
* An integer `SUM` leaving 64 bits, or a decimal `SUM` leaving its precision
  (`Measure.sumOk`), is ruled out where the plan bounds a group's
  rows (`Rel.maxRows`: a `VALUES` list, a `FETCH` count) and the argument's range
  bounds each value (`Measure.sumFits`). Row caps on the inputs count too
  ([Rows.lean](../analysis/Sverify/Analysis/Rows.lean)): a capped read is a `FETCH`
  (`Rel.capReads`), and a join on a key of its right side is capped by its
  left side (`Rel.capJoins_eval`). Its `SUM`s are decided on the capped plan
  and every other issue on the plan as it is (`Rel.issuesCapped_sound`).
  Elsewhere it is an inferred assumption
  (`Rel.SumsFit`, `Rel.noIssue_of_sumsFit`) that the SQL checks on the data while
  the job runs.
* Bounds that rule out overflow are inferred
  ([Infer.lean](../SubstraitLean/Infer.lean)): the range analysis run
  backwards from each overflow `Rel.mayIssues` reports, through projections,
  filters, joins and `MIN`/`MAX` down to base-table columns. So are the
  ranges of codes that rule out domain errors, casts out of range, string
  lengths and decimal precision, and the value a divisor's column must not
  hold. The inference is
  untrusted and has no proofs. Its bounds are added to the preconditions and
  the contract is proved again (`contract_sound`, `Rel.mayIssues_sound`), so a
  wrong bound only makes that proof fail; on the data they are checked like
  any precondition.
* `Rel.mayIssues_sound`: every issue that can happen on any input is reported. Guards
  are understood where every engine respects them: in a `CASE` branch (and so
  `NULLIF(b, 0)`), or in a filter below a *projection*. They are not respected in the
  same `AND`, nor in an earlier *filter*: an engine may merge filters (`Rel.loose`),
  so `t.filter(n != 0).filter(q % n > 1)` can fail.
* `FloatCode.floor_mono`, `round_mono`, `toInt?_mono`, `toInt?_of_range`
  ([Rounding.lean](../core/Sverify/Core/Rounding.lean)): `FLOOR`, `CEIL`, `ROUND` and the cast
  to `BIGINT` are exact on double codes and monotone, so `amount ∈ [0, 100]` proves
  `amount.round()` is an integer in `[0, 100]`, and the cast safe.
* Abstract rules for truncating `/` and `%` (`divBound_sound`, `modBound_sound`) and
  for squares (`powAbs_sound`).
* `Time.monthIndex_spec`, `Time.trunc_mono`, `Time.year_mono`
  ([Time.lean](../core/Sverify/Core/Time.lean)): every day lies in the month the calendar
  arithmetic computes, so years and truncations grow with the timestamp, and
  `ts ∈ [2024-01-01, 2025-01-01)` proves `ts.year() == 2024` and
  `ts.truncate("M") >= 2024-01-01`. The other parts have proved ranges (`day` in
  `[1, 31]`, …); `date_part` is `NULL` outside the years ±262142.

Trusted: *when* an engine evaluates an expression (`Rel.HasIssue`: `CASE` is lazy,
`AND`/`OR` are not, filter and join conditions may run before the filters below
them; [What is trusted](proofs.md#what-is-trusted)). `python/tests/test_numeric.py`
runs the plans on DuckDB on random data and checks
they only fail where an error was reported. `BIGINT` and timestamp columns are taken to
hold 64-bit values (from the schema); arithmetic on narrower integers is
checked at their declared width.

## Incremental view maintenance

Table updates are Z-sets: rows with signed weights, where a deletion has weight `-1` and an
update is a delete plus an insert. This follows DBSP (Budiu et al., VLDB 2023).
The linear fragment, `Rel.Incremental`, covers every operator except left,
semi and anti joins, `DISTINCT`, aggregates, fetch and windows; semi and anti
joins, `DISTINCT` and `COUNT`, `SUM`, `AVG`, `MIN` and `MAX` per group have
delta rules of their own ([section 6 of the optimizations note](optimizations.md#6-incremental-maintenance);
what refresh maintains is in [the guide](tasks.md#nodes-composing-storing-refreshing)):

* `Rel.zeval_add`: `Q(D + ΔD) ~ Q(D) + ΔQ`. Filter, project, emit, sort and union
  are linear (a sort only orders the bag), and cross and inner join use the bilinear rule
  `Δ(A×B) = ΔA×(B+ΔB) + A×ΔB`.
* `Rel.delta`: compiles a plan into a delta plan, an ordinary `Rel` that reads the
  old tables and the change tables (`δ t`, e.g. `orders$delta`).
  `Rel.delta_correct` proves it computes exactly `ΔQ`.
* `Rel.incremental_sound`: combines the two, so old result + delta-plan output =
  full recomputation.
* `Rel.zeval_lift`: with all weights 1, Z-set evaluation equals the bag
  semantics `Rel.eval`, so the two models agree.
* `Rel.zeval_terms`: a plan's result is the concatenation of its union-free
  terms' results (`Rel.terms`), for an engine that runs the terms one by one.
* `Rel.weighted_eval`: running the weight-column encoding (`Rel.weighted`) on an
  ordinary bag engine gives exactly the Z-set result, with each weight as a
  trailing column. Old tables get weight 1, and joins multiply weights.

Equivalence is `List.Perm`, which never cancels `+1` against `-1`. That makes it
stronger than Z-set equality, so the results also hold under consolidation.
`Examples.lean` runs a delete, an insert and an update through a filter/project
plan and an inner join where both sides change.

## Table formats

[TableFormat.lean](../SubstraitLean/TableFormat.lean) covers what `sverify.io`
takes from Delta Lake and Iceberg, with the format's part as explicit
hypotheses:

* `Rel.zeval_weight_congr`: on the incremental fragment, Z-set evaluation only
  depends on the tables' weights. A change feed deletes and re-inserts rows,
  so the old table plus the feed is not a permutation of the new table, only
  equal in weights.
* `Rel.cdf_sound`: if the feed turns each old snapshot into the new one up to
  weights (`ChangeFeed`, trusted) and is loaded as the change tables (`hδ` of
  `Rel.delta_correct`), the old view plus the delta plan's output has the
  weights of the view on the new snapshot. `ChangeFeed.of_diff`: the diff of
  two snapshots is such a feed, so the fallback needs no trust in the feed.
  `ChangeFeed.of_changed_files`: so is the diff of only the files that
  changed, if the unchanged files are the same rows in both snapshots.
* `stats_table`: with correct per-file statistics (`ColStats.Correct`,
  trusted), every row of the table lies in the join of the files' bounds;
  `stats_append`: the files an append added bound its rows; `stats_bounds`:
  that bound is the `IS NOT NULL AND c >= lo AND c <= hi` fact handed to the
  contract checker; `stats_fact`: with NULLs or a missing side it is
  `c IS NULL OR (…)`; `stats_all_null`: files that are all NULL give `c IS NULL`.
* `prune_sound`: filtering only the files that are not skipped gives the
  same rows as filtering the whole table, if no row of a skipped file makes
  the filter TRUE (which the checker proves from the file's statistics).

All proofs depend only on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) and the trusted facts below. The bounds of `SUM` and `AVG` of doubles need none: they are theorems about the correctly rounded sum (`floatSumCR_mem`, `floatAvgCR_mem`, `floatSumCR_sign`), and the bound of a sharded `SUM` too (`floatSplit_sum`). The statistical aggregates need none: they are the exact moments rounded once. The bounds of one double `+`, `-`, `*` and `/` need none: they are the exact result rounded once, and `add_scaled`, `sub_scaled`, `mul_scaled`, `div_scaled`, `div_scaled_err` and the signs `add_nonneg`, `mul_nonneg`, `div_nonneg` are theorems in `FloatArith.lean`, so a sharded `AVG`'s division rests on none either. The one axiom left is `exp_fin` in `Safety.lean` (libm's `exp`). [`float-bounds/`](float-bounds.md) also proves the bounds over the reals with Mathlib, kept out of the core build (`div_scaled_err` is `core_div`'s statement).
