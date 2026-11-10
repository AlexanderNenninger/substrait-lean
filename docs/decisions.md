# Decisions

The decision log of sverify's semantics, for contributors: each choice the
reference, the core and the profiles make, with when and why it was made.
[core-semantics.md](core-semantics.md) is the design they apply to, and
[reference-semantics.md](reference-semantics.md) states the resulting
behaviour for users, without the history.


Decided on [#562](https://github.com/AlexanderNenninger/substrait-lean/pull/562):
D6 as the first draft's alternative, the others as it recommended.
D9 and the decisions after it were made after #568's classes and #577's translation policy.

### D1. Where the tables live

Lean is the source; Python mirrors it, and a test compares the two, as
`tests/test_black_box.py` does for the black boxes. Lean proves the
refinement by `decide` on its own table, so the proof depends on no parser
and no generated module.

### D2. Raises in the core

The core allows raising everywhere, as the reference's correctness does
today, and each profile states its raise set. It keeps principle 4 and
admits each engine's extra raises (`MIN % -1`, `<<` of a negative number)
without new options.

### D3. Behaviours outside the YAML

An option's core set is the YAML's values and the behaviours the engine
facts record, each extra one tagged with its fact. Every engine profile then
refines the core by construction, and the facts say why each extra is there.

Each such gap, where Substrait could state the behaviour (an option, an
option's value, a default) and does not, is also an entry of the upstream
ledger with `kind: "spec-gap"` ([upstream/README.md](../upstream/README.md)).
This design pass found seven, each checked against Substrait's `main` at
`a4d8e00`:

| Entry | The gap | Options here |
|---|---|---|
| [ST-1](../upstream/bugs/ST-1.json) | a shift by a count outside the width, bits shifted out | `shift_range` |
| [ST-2](../upstream/bugs/ST-2.json) | whether `atan2(0, 0)` is a domain error | `on_domain_error` |
| [ST-3](../upstream/bugs/ST-3.json) | `corr`, `variance`, `std_dev` of one pair, a constant side, or non-finite values | `stat_degenerate` |
| [ST-4](../upstream/bugs/ST-4.json) | NaN and `-0.0` in equality, grouping and sorting | `nan_equality`, `nan_order`, `zero_sign`, `nan_kind` |
| [ST-5](../upstream/bugs/ST-5.json) | `inf - inf` and `0 * inf` in `add`, `subtract`, `multiply` | `nan_creation` |
| [ST-6](../upstream/bugs/ST-6.json) | how a cast to an integer rounds; `FAILURE_BEHAVIOR_UNSPECIFIED` | `float_to_int`, `cast_failure` |
| [ST-7](../upstream/bugs/ST-7.json) | what `SORT_DIRECTION_UNSPECIFIED` means | `null_order` (D6) |
| [ST-9](../upstream/bugs/ST-9.json) | a result of finite doubles beyond the largest double: `±inf` or an error | double overflow to `±∞` (#575) |
| [ST-10](../upstream/bugs/ST-10.json) | `upper`, `lower` with `char_set: UTF8`: Unicode's simple or full case mapping | `char_set` |
| [ST-11](../upstream/bugs/ST-11.json) | integer `power` with a negative exponent | none: the reference raises (`Issue.negExponent`), D2 |
| [ST-16](../upstream/bugs/ST-16.json) | a logarithm of zero that is NULL (Spark's), which `on_log_zero` cannot state | `on_log_zero` |

`CLUSTERED` needs no entry: Substrait's `relations/basics.md` defines it.

### D4. NaN payloads

A NaN is one of two codes, by its sign. No function sverify models reads a
payload, and `signbit` reads the sign
([duckdb-signbit](../engines/duckdb/facts/duckdb-signbit.json)).
WebAssembly treats a NaN's sign as a choice too, and IEEE 754 only
recommends that payloads propagate ([Prior work](core-semantics.md#loose-specifications-and-profiles)).

### D5. Rounding of doubles where the plan omits it

The core leaves the YAML's five modes open, and the reference and every
engine profile fix `TIE_TO_EVEN`. This is what Substrait says, and #85's
error bounds become theorems of the profiles that fix the mode.

### D6. Sort keys without a NULL order

The core reads a key's `UNSPECIFIED` direction as `null_order` open, and
`CLUSTERED` as an order relation of its own: rows with equal keys adjacent,
the groups in any order. `Profile.substrait` accepts both, and the reference
and each engine profile fix the NULL order (DuckDB: `NULLS_LAST`,
[F2](../engines/duckdb/facts/duckdb-F2.json)). Substrait's sort
directions include both, so a faithful profile has to read them. The parser
keeps refusing them until step 1c lands the choice point and the relation.

Amended (2026-11-07): step 1c landed, and the parser reads both in a sort
relation's keys: an `UNSPECIFIED` or missing direction leaves the NULL order
open, which the reference fixes as NULLs last (D8), and `CLUSTERED` is its
own order relation. A window's or a measure's key must state its direction
(`parseSortKey`).

### D7. Per-plan checks

Translators are proved once, entry by entry, as the lowering and the lift are
today, and single plans are checked only for translations sverify does not
own (another producer's plan, an engine's own SQL). No plan pays for a proof
at run time, and the generated tables already carry the proofs.

### D8. The reference's NULL order

Where a key's direction is `UNSPECIFIED`, the reference puts NULLs last in
both directions: DuckDB's default ([F2](../engines/duckdb/facts/duckdb-F2.json))
and the default of the model's `SortKey` for hand-built values.

### D9. One tool per option

Each option gets one of three tools in the reference ([D21](#d21-tighten-the-reference-where-it-stays-practical)): raise, choose a value,
or leave it open. One table, a row per option, records the tool, the
precondition it creates, and the shim count per engine. The reference raises
only where that precondition is usually provable from the bounds or cheap to
check on the data; otherwise it chooses a value or leaves the option open.
Each strict choice creates a precondition for every plan that meets it, so
the table makes that cost visible next to the shims it saves
([What a proof under the reference guarantees](core-semantics.md#what-a-proof-under-the-reference-guarantees)).

### D10. Determinism

Whether a plan's result is determined up to row order is reported by
default, and required where the output's consumer states it needs it:
incremental refreshes and idempotent sink epochs. Those consumers state
their own observation, `q_det`, separate from the postcondition's
([D20](#d20-two-observations-per-output)); elsewhere the report names the
open choice.

### D11. Postconditions name the equivalence

Each output can carry a postcondition that names the equivalence its
consumer expects: rows as a multiset (the default) or as a sequence; floats
within the plan's proved bound `ε` (`floats="plan"`, the default, #689),
exact, or within a stated tolerance, absolute, relative or in ulps, which
`verify` checks against `ε` on each engine; timestamps up to a precision;
strings up to NFC. Verification then
means that every engine result the route allows is equivalent, under the
stated relation, to a result the reference allows. A tolerance means "proved
within the stated tolerance", with #568's propagation of `ε` checking that
the tolerance holds; it is no verdict of its own. The user states what they
need, so the classes of [Classes of an engine's functions](core-semantics.md#classes-of-an-engines-functions)
become one question: does the route meet the stated relation.

### D12. Contracts and the observation

The same postconditions settle whether a contract can tell `q`-equal
results apart. The user states the observation `q`, and each other
`ensures` is either checked on the canonical representative (`q`'s
canonical map: sort the rows, `canon` the floats, truncate, normalise) or
falls in a syntactic class invariant under `q` (uniqueness, references,
bounds, aggregates for the multiset). Otherwise the checker reports which
`ensures` depends on what `q` ignores.

### D13. Choosing the route

`verify` and `run` choose the route by default: native under the engine's
profile, then translated from the reference (`translated`), then by the option-wise transfer check
([Which plans run on an engine](core-semantics.md#which-plans-run-on-an-engine)). The result
names the route taken. `semantics=` and an explicit route override the
choice. The default keeps a plan that verifies somewhere running without the
user knowing the profiles; the override keeps the choice inspectable.

Amended (2026-11-07): a fourth route, `recheck`, added in
[#586](https://github.com/AlexanderNenninger/substrait-lean/pull/586), comes
after the transfer check: the checker proves the contract again under the
engine's profile (`python/src/sverify/routes.py`).

Each route ends in `Engine.contract_sound` (#900): the contract holds on the
rows the engine's model computes for the translated plan, unless it raises.
The engine's actual output rests on `Engine.Runs` and the transfer check
(`Engine.contract_sound_runs`); it fails today at `sum_order`, `stat_algo`, `quantile_interp` and `zero_sign` on every engine, `null_order` without a preference on Polars and Spark, and integer overflow on Polars ([#900](https://github.com/AlexanderNenninger/substrait-lean/issues/900), PR 3).

### D14. Engine versions

An engine profile is tied to the engine's versions: it records the version,
or range, its facts were probed at. A run on another version warns, and a
run on another major version is refused until the probes are re-run. A new
version that changes a fact gets a new fact with `supersedes` (the `engine-fact`
skill) and a new row in the profile. Facts hold for the version they
were probed at, and the profile is only as good as its facts.

### D15. Where the observations live

The choices table holds, next to each choice, its class, its observation
`q` and its shim: each (profile, group, option) row reads choice, class,
`q`, shim, so an engine's realizability row comes from one table. This
extends step 1a's `ProfileTable` (#578, `core/Sverify/Core/Options.lean`): a
column for the class and `q`, one for the run-to-run variation
([D20](#d20-two-observations-per-output)) and one for the shim, filled for
engines in step 3a, and read by step 1c.

### D16. Engine correctness

An engine runs a plan correctly when it returns a result the reference
allows, or raises only where the reference may raise. Resource errors, such
as running out of memory, are excluded. The guarantee of no error
([What a proof under the reference guarantees](core-semantics.md#what-a-proof-under-the-reference-guarantees))
needs this stricter definition: under partial correctness, an engine could
raise anywhere and still be correct. Partial correctness is what
`Rel.duckdb_shim_sound` proves today for every lowered plan; for a plan
proved to never raise the two agree (`Rel.duckdb_sound`).

Amended (2026-11-08): `Engine.contract_sound` (`engines/Sverify/Engines/Sound.lean`,
[#900](https://github.com/AlexanderNenninger/substrait-lean/issues/900)) proves
a proved contract on the rows each engine's model computes for the
translated plan, unless it raises, through each engine's `Engine.Sound`. That the engine's actual
result is one its table allows stays trusted, as `Engine.Runs`, resting on the
tested rows `Engine.Refines` lists ([What is trusted](proofs.md#what-is-trusted)).

### D17. Changing the reference

While sverify is on 0.x, the reference changes where the design needs it. A
change to the reference ships in a minor version bump, with a
`changelog.d/` fragment that says what changed. Bumping the minor version
costs little, and the fragment tells users which proofs may change.

### D18. Observations ordered by refinement

An observation `q'` refines `q` when `q'` observes everything `q` observes:
`q` factors through `q'` (`q = f ∘ q'` for some `f`), or equivalently
`ker q' ⊆ ker q`. Equality up to `q'` then implies equality up to `q`, so
the finer guarantee refines the coarser one, as `Allowed_P' ⊆ Allowed_P`
does for profiles. The identity is the finest observation, a constant the
coarsest. In Lean, equality up to `q` is `Relation.Equiv q`
(`core/Sverify/Core/ObsEquiv.lean`), and `Relation.Equiv_mono` proves that
`Obs.le q' q` gives it: equality up to `q'` implies equality up to `q`. Five
consequences:

1. The check. An engine function equal to the reference's up to `q_E`
   meets a postcondition that asks for `q_post` ([D11](#d11-postconditions-name-the-equivalence))
   exactly when `q_E` refines `q_post`. Otherwise a canonicalising shim
   makes the function's `q` finer, or the call is refused.
2. Components. `q` is a product of components (rows, floats, zeros and
   NaNs, timestamps, strings, errors), each a short chain from exact to
   coarse. Refinement is componentwise, so it is a partial order: rows as a
   multiset and strings up to case folding are incomparable.
3. Through a plan. Each operation keeps a component or coarsens it (a
   `LIMIT` without `ORDER BY` coarsens the multiset of rows), and the plan's
   output `q` must refine the postcondition's.
4. Tolerances join the floats chain: a tolerance `ε' ≤ ε` refines `ε`, with
   exact equality at the top.
5. The finest `q` is computable. The valid observations of a function, those
   with `q ∘ f_E = q ∘ f_reference`, are closed under meet (if two
   observations each agree on both functions, the pair of them does), so
   within the library of components there is one finest valid `q`. Sverify
   finds it per component by trying candidates from fine to coarse: probes
   give counterexamples that rule candidates out cheaply, and the finest
   candidate left is confirmed by a Lean proof against the engine's
   modelled behaviour (the search-and-prove machinery of the lowering
   search, `engines/Sverify/Engines/LoweringSearch.lean`), or by fuzzing where the
   engine is not modelled.

This makes D11 and D12 one comparison: the route's `q`, carried through the
plan, against the `q` the postcondition names. The finest valid `q` is the
`q` column of the choices table ([D15](#d15-where-the-observations-live)).

### D19. `AND` and `OR` raise eagerly

An error in either operand of `AND` or `OR` may raise, whatever the other
operand's value (#604). `p AND q` is not a guard for `q`: in
`x <> 0 AND 10 // x > 1`, the division may run on the rows where `x = 0`.
The reference has always evaluated both operands (`Expr.issues` of `.bin`,
`analysis/Sverify/Analysis/Safety.lean`); D19 states it as a decision.

- It is what the engines do. DuckDB evaluates `AND` and `OR` as values,
  both operands first
  (fact `duckdb-exec-short-circuit`, #602),
  and Polars evaluates every operand and every `when`/`then` branch
  (fact `polars-exec-when-eager`, #603).
  An eager reference needs no shim on either.
- It is strict. A plan that relies on the short-circuit is not proved; the
  report says the operation sits inside an `AND` or `OR` and suggests the
  fix: guard the operation itself with a `CASE` whose value is not
  boolean, `(CASE WHEN x <> 0 THEN 10 // x END) > 1`, or state the guard
  as a precondition. A boolean `CASE` is evaluated whole, as `AND` and `OR`
  are, since an optimizer may rewrite it into them (`Parse.eagerly`).
- A non-boolean `CASE` stays lazy: DuckDB's is, and the Polars translation
  guards each branch's inputs where Polars computes every branch.

A filter above a join is analysed on the cross product of the join's loose
inputs (`Rel.loose`), so DuckDB pushing a raising `WHERE` into one side of an
inner or left join
(fact `duckdb-exec-filter-pushdown`, #602)
evaluates it on rows the analysis covers. The one exception is a join whose
other side is empty: `Rel.HasIssue` then has no pairs, while DuckDB still
evaluates the pushed filter on the side's rows. `Rel.mayIssues` reports
the error anyway, since it describes each side's columns by that side's own
bounds; `Rel.HasIssue` does not model the case yet.

DuckDB 2.0.0 also evaluates a `CASE`'s constant `WHEN` conditions when it
plans the query, with the evaluator that raises:
`SELECT CASE WHEN x > 0 THEN 1 WHEN 1 // 0 = 1 THEN 2 END FROM t` raises on
an empty `t`, and on a `t` whose rows all take the first branch (probed;
a constant `THEN` or `ELSE` that raises, `ELSE 1 // 0`, and a constant
`WHERE 1 // 0 = 1` on an empty table do not). A constant subexpression of a
condition that raises therefore raises whatever the data. The reference's
`CASE` evaluates a condition only on the rows that reach it, so a plan with
such a constant was proved and raised on DuckDB
([#609](https://github.com/AlexanderNenninger/substrait-lean/issues/609)).
Under D21 the reference now counts every constant subexpression that raises
as raising for the whole plan, whatever the data and whichever branch a row
takes (`Rel.constIssues` in `analysis/Sverify/Analysis/Safety.lean`): stricter than
DuckDB, which leaves a constant `ELSE` or `WHERE` alone, and constants that
raise are rare in real queries. No precondition rules one out; the report
names the constant.


### D20. Two observations per output

Each output has two observations, checked independently.

- `q_post`, for correctness, is stated by the postcondition
  (`sv.equivalent`, [D11](#d11-postconditions-name-the-equivalence)), by
  default the multiset of rows with doubles within the plan's `ε` and other
  values exact. Every engine result must
  equal, up to `q_post`, some result the reference allows. The check is
  D18's: the class `q` of each engine row must refine `q_post`.
- `q_det`, for reproducibility, is stated by whoever consumes the output.
  An idempotent sink or an incremental refresh declares its own: a sink
  that overwrites partitions may tolerate `ε`, one that compares checksums
  needs exact bits. A plain run declares none, so determinism is only
  reported ([D10](#d10-determinism)). The check: the engine's run-to-run
  variation, carried through the plan as D18 carries `q`, must refine
  `q_det`.

The two are independent, and `q_det` is often the finer one. Polars's
streaming float `SUM` varies in the last bits between runs, and grouped
float sums vary between runs on both of Polars's engines (the
characterization pipeline's probes), so such a plan passes a sink whose
`q_det` allows `ε` and fails one that needs exact bits, with the same
`q_post`. A `LIMIT` without `ORDER BY` can be correct under a multiset
`q_post` and still fail every `q_det`, since which rows it keeps can change
between runs.


### D21. Tighten the reference where it stays practical

Sverify tightens the reference when that costs little in practicality. Where
an engine differs from the reference on an edge case, the reference raises
there, and the engine needs no shim, as long as the precondition that
excludes the edge case rarely bites real queries: it is proved from the
bounds or checked on the data by a guard. A guard costs a check where the
precondition is not proved; a shim costs a rewrite on every run. D9's table
records the tool for each option. This is how D9 chooses between raising and
choosing a value.

Example: `power(-∞, y)` for a non-integer `y` raises in the reference.
IEEE 754 gives `+∞`, and Polars's `** 0.5` gives NaN through `sqrt`, so
Polars needs a guard for such plans and no shim.

A second example: a constant subexpression that raises (`1 // 0 = 1`)
counts as raising for the whole plan (#609, under D19), since DuckDB may
evaluate it when it plans the query.

### D22. Four route classes, and tolerances are observations

A route's class is one of four: `exact` (every result the engine gives is one
the reference allows), `observed` (equal to such a result under an
observation the postcondition states), `shim` (either of those after the
translation's shim) and `refused`. The classes `refines`, `refines` up to an
observation and `approx` of [Classes of an engine's functions](core-semantics.md#classes-of-an-engines-functions)
map to `exact`, `observed` and `observed`. User-facing docs say
"observation", or "observation model" in prose, and never `q`.

Why: a tolerance is an observation of doubles. `sv.within` is already a
component of `sv.equivalent` (`floats=sv.within(...)`), ordered by
refinement with the other components (D18, item 4). Tolerances differ from
the other observations only in how they compose, by adding their `ε`, and
the checker's propagation of `ε` through a plan handles that. A separate
`approx` class told the user nothing the observation did not.

### D23. Inferred preconditions are errors by default

A precondition sverify infers to rule out a runtime error (`total // qty`
needs `qty != 0`, `amount * 2` needs `amount < 2**62`) is a checking error by
default: `verify` reports the plan as not proved and names the precondition,
where it came from, and the fixes, which are to declare it in `requires` or
to rewrite the plan so no row needs it (filter those rows first, or a `CASE`).
`on_inferred=` chooses: `"error"` (the default), `"warn"` (assumed, checked
on the data before each run, with a warning), `"ignore"` (assumed and
checked, as before #655) or `"off"` (nothing inferred or assumed: a `SUM`
that may overflow is an error too; `infer=False` before 0.6, #690).

Why: an assumed precondition is checked on each batch, and a batch that
breaks one is refused before the run (#604). An inferred precondition is
therefore a run-time error the user never asked for: a job that refuses
data because of a bound nobody wrote down. Declaring it puts the decision
with the user, and the declared form documents it.

`SUM`s assumed to fit 64 bits and operations on doubles assumed to stay
finite (`Report.assumed`) are not inferred preconditions: they keep their
checks on the data.

### D24. Tie order belongs to the deterministic profile

The reference leaves `tie_order` and `tie_pick` open. Rows that tie in an
`ORDER BY` or in a window's order come in any order, a `FETCH` takes the
first rows of any order the plan allows, and `FIRST`, `LAST`,
`ARG_MIN`/`ARG_MAX`, `STRING_AGG`, `collect` and `MODE` take the rows that
tie in their own order in any order. `Rel.OrderAllowed`
(`core/Sverify/Core/OrderAllowed.lean`) holds the results of every such order, and a
contract holds on all of them: `contract_sound_all` for postconditions,
`Rel.keys_sound_all` for keys. An engine's own pick is one of these orders,
so it runs natively.

The deterministic profile is the reference with one order fixed: a stable
sort (`List.mergeSort`) and rows in list order, as `Rel.eval` computes them
(`Rel.eval_orderAllowed`). A consumer that needs a rerun to give the same
rows asks for it, through `run(reproducible=sv.equivalent())` or a sink's
`reproducible=` ([D10](#d10-determinism),
[D20](#d20-two-observations-per-output)). Engines read tables in an order of
their own, so no shim reproduces list order on them. The deterministic
profile needs a plan whose order is total, by a tie-break key or a
uniqueness precondition (`Rel.windowsTotal`, `Rel.fetchesTotal`), and
refuses a plan without one. The refusal names each place where ties stay
open (`str(report)`, with the keys that would close them in `Report.ties`).

An order-sensitive operator reads one sorted enumeration of its input, and
its meaning is the set over all of them (`Lin` and `Sem`,
`SubstraitLean/Seam.lean`, #928). Below an unordered operator, as with a
`FETCH` without a total `ORDER BY` under a join, the order is forgotten and
the result is a set of multisets (`Rel.Bags`): this is where the tie order's
nondeterminism lives. `verify` and `run` allow such a plan, and the proofs
hold for every member; `refresh` commits one member and refuses it unless
the plan has one (`Rel.bags_iff_perm_eval`, `Rel.bags_fetch_two`).

Why: `Rel.eval`'s one order leaked into four places
([#679](https://github.com/AlexanderNenninger/substrait-lean/issues/679)).
Theorems about `FETCH`, ties and windows held for that order only. The
catalogue and the oracles compared each engine with it, and reported
legitimate picks as `tie_order` differences. Shims imitated
`List.mergeSort` on engines, and Polars refused or shimmed picks it could
run natively.

### D25. Float aggregates are correctly rounded exact sums

In the reference, a `SUM`, `AVG`, `VAR_*`, `STDDEV_*`, `COVAR_*` and `CORR`
of doubles is the correctly rounded value of the exact sum or moments. Every
finite double is an integer multiple of 2⁻¹⁰⁷⁴, so the sum of the values is
an exact dyadic rational; the result is the double nearest to it, ties to
even (`floatSumCR`, `core/Sverify/Core/FloatExact.lean`), and `AVG` is the exact
sum divided by the count, rounded once (`floatAvgCR`). NaN and infinities
follow IEEE 754: a NaN, or `+∞` with `-∞`, gives NaN, and one kind of
infinity gives it. The value is a function of the multiset of values, so it
is one value and order-free (`floatSumCR_perm`).

Engines add in an order of their own: DuckDB in the order values reach each
thread's state (`duckdb-sum-double`), Polars pairwise in blocks of 128
(`polars-sum-float`), Spark per partition (`spark-sum-double`). Each refines the reference up to the
plan's bound, the distance of any order of additions from the exact sum
(`StdModel.epsilon_sum` in [`float-bounds/`](float-bounds.md)) plus half an
ulp of the final rounding (`epsilon_sum_cr`). Their `sum_order` rows stay
`approxWithin "plan"`, so a double `SUM` or `AVG` on an engine is
`observed (tolerance)`, as it was. Their `agg.fsum` `rounding` rows are
`approxWithin "plan"` too, proved by the same theorem (#929): its standard
model holds of every rounding to nearest, whatever the tie rule, so the
engine's rounded additions stay within the plan's bound.

Three consequences:

- `sum_order` and `stat_algo` are no longer choices of the reference. They
  stay choices of the engines, and the reference's row is `EXACT`.
- `Rel.detPlan` is true of float aggregates, so `contract_sound_all` covers
  every result the reference allows for them.

  Amended (2026-11-07, #1017): this holds of closed plans (`Rel.closedB`); a
  plan with open measures (`Measure.openB`) goes through
  `contract_sound_allowed` and `Rel.FloatOpenSafe`.
- A tolerance is a metric: bounds add along a pipeline
  (`Near ε₁ a b → Near ε₂ b c → Near (ε₁ + ε₂) a c`), and no tolerance passes
  through a filter, group key or sort on a double column.

Why: the reference added doubles one by one in list order (`floatSum`) and
allowed every order and grouping (`FloatSums`). The engines' results were
then the reference's only in DuckDB, which emulated Lean's order with
`list_reduce`; Spark and Snowflake refused double sums for want of a row
order; five facts about `floatSum` were axioms. The correctly rounded sum
turns them into theorems, lets every engine run `SUM` and `AVG` natively,
and gives incremental maintenance an exact state with no drift. A
postcondition at a rounding boundary can move by an ulp, which `sv.approx`
absorbs. The epic is
[#919](https://github.com/AlexanderNenninger/substrait-lean/issues/919).
Precedents: Müller et al. ("Reproducible Floating-Point Aggregation in
RDBMSs", ICDE 2018, [arXiv:1802.09883](https://arxiv.org/abs/1802.09883)) make `SUM` order-free in a database; Neal's
superaccumulator ([arXiv:1505.05571](https://arxiv.org/abs/1505.05571))
computes the correctly rounded sum at less than twice the cost of a naive
one.

Note ([#1032](https://github.com/AlexanderNenninger/substrait-lean/issues/1032)):
window aggregates of doubles take the same per-measure profile choice as
grouped aggregates; the reference is unchanged. An engine's window sum is
within the plan's bound where its window algorithm sums the frame's own
values (`window_sum_algo`: each frame anew, a tree, or a running sum).

### D26. Two equalities for NULL

In a predicate (`WHERE`, a join's `ON`, `IN`, a `CASE` condition)
`NULL = NULL` is unknown, so a NULL never matches, never equals and never
compares: three-valued logic, `and3`/`or3`, `UnFn.apply .not` and `BinFn.apply .eq` in
`core/Sverify/Core/Expr.lean`. In `GROUP BY`, `DISTINCT`, `UNION` (distinct),
`EXCEPT`, `INTERSECT`, a window's `PARTITION BY` and `IS NOT DISTINCT FROM`,
all NULLs are one value: syntactic equality, `Value.decEq` in
`core/Sverify/Core/Value.lean`, as `dedup` and `groupKey` use it. A key
(`sv.unique`, `KeyOn`) uses the second, so two rows with NULL in a key column
collide, which is stricter than SQL's `UNIQUE` (`Keys.lean`'s header). The
anti part of a left join and a semi or anti join use the first.

Nothing in the core changes. The decision names what it does, so that an
encoding of difference or provenance
([#905](https://github.com/AlexanderNenninger/substrait-lean/issues/905))
keeps the two apart.

### D27. The size hypothesis is the only size assumption

`Rel.Small` (`analysis/Sverify/Analysis/Safety.lean`): every string has fewer than 2³²
characters, every relation a window reads fewer than 2⁶² rows, and every
relation an aggregate reads fewer than 2⁶³. It is a hypothesis of every
soundness theorem over windows and aggregates, never an axiom, and no other
size bound is assumed anywhere. [reference-semantics.md](reference-semantics.md)'s
"Overrides" table states it. A new theorem that needs another bound adds it
to `Rel.Small`, beside the others.

### D28. Lambdas have lexical scope

A lambda in a higher-order call (`Expr.hof`: `any_match`, `all_match`,
`transform`, `filter`) sees the enclosing row, as DuckDB's lambdas can read
outer columns (`list_transform(l, x -> x + col)`). Its body is evaluated on
`x :: row`: field 0 is the parameter and the row's column `i` is field
`i + 1`; a nested lambda's body reads its own parameter as 0, the outer
parameter as 1 and the row from 2 (de Bruijn order). #922's draft
numbered the row first; with the parameter first a body keeps its meaning
when columns are appended to the row, so `Expr.eval_append`, the lemma
behind every pushdown, holds of bodies unchanged, and a closed body (field 0
only) means what it meant before.

The parser reads Substrait's references this way (`Parse.openBody`:
`lambdaParameterReference` with `steps_out` `k` inside `k` nested lambdas,
`rootReference` one further per lambda) and the writer writes them back
(`Write.closeRefs`). Every function that renumbers a row's columns renumbers
a body under one binder (`liftIdx`, `liftPred`, `Expr.shift` with a cutoff,
`Expr.subst` with a shifted substitution), and the kind checker types a body
under its element's kind in front of the row's (`Expr.kindT`). Accepted plans
keep their meaning: before D28 the parser refused a body that read the row.

Why: a closed lambda cannot express `contains` of a column or a filter by an
outer value, and the review of the core (#893) found the restriction in
`Expr.eval`, `Expr.refsLt` and the parser, none of it needed by a proof.

### D29. A value has its kind

Decided 2026-11-07 (#923).

`Value` has a constructor per kind (#923): `int`, `float` (a double's code),
`date` (days), `ts` (microseconds, with or without a time zone), `tod`
(microseconds since midnight), `dec s m` (scale and unscaled integer) and
`struct`, beside `null`, `bool`, `str` and `list`. Intervals stay `int`. A
function of one kind gives NULL on another, so a double can no longer pass
for an integer or a timestamp for a date. Comparisons (`Value.numPair`) take
two numbers of one constructor, decimals of one scale: `=` is TRUE only of
equal values, which equi-joins rest on (`isTrue_eq`). The parser brings both
sides of a decimal comparison to their common scale (`UnFn.dkind`).

`SUM` (`sumOf`) gives a decimal of scale `s` when all its values are
decimals of scale `s`, and otherwise the integer sum of the integers and the
decimals' unscaled values, a mix of decimals with other values or with
other scales included. This case is unreachable for a plan the kind checker accepts; it binds no engine, and no contract theorem is stated for unchecked plans.
The checker is D28's (`Rel.kinds_sound`). The mixed value is a don't-care,
chosen to keep `SUM` independent of the order of its values (`sumOf_perm`)
and of how a partition splits them (`sum_partials`) without a side condition.
A NULL for a mix would break the second: a part that mixes kinds gives NULL,
the combining `SUM` skips NULL parts, and the parts left would add up to a
number where the whole gives NULL.

The abstract domain records the kind of a column's numbers (`AVal.nk`, with
`none` as top). A value of kind `k` is in an abstract value only if its `nk`
is `none` or `some k`, and the join of two different kinds is `none`. Static
kinds from the kind checker may refine `nk` on checked plans later.

Why: the kinds were in the parser and the kind checker (#924) only; with them
in the values, a well-kinded plan's values have their kinds by evaluation, and
the float facts state their premises about doubles. Those were the trusted
axioms `floatSum_mem`, `floatAvg_mem`, `floatSum_sign`, `floatSum_twoPhase`
and `floatAvg_twoPhase`; D25 retired them for theorems about the correctly
rounded sum (`floatSumCR_mem`, `floatAvgCR_mem`, `floatSumCR_sign`,
`twoPhaseSum_near`, `twoPhaseAvg_near`).

### D30. Statistical aggregates are correctly rounded exact moments

Decided 2026-11-07 (#918).

In the reference, `VAR_SAMP`, `VAR_POP`, `STDDEV_SAMP`, `STDDEV_POP`,
`COVAR_SAMP`, `COVAR_POP` and `CORR` of doubles are rounded once from the
exact moments of the values: the count `n`, and `Σx`, `Σx²` and `Σxy` as
exact dyadic rationals, since every finite double is a multiple of
2⁻¹⁰⁷⁴ (`FloatMoments.lean`). The co-moments `S = Σx² − (Σx)²/n` and
`C = Σxy − Σx·Σy/n` are exact. The variance is `S/d` rounded to the nearest
double, ties to even, with `d = n − 1` for a sample and `n` for the
population; the covariance is `C/d` rounded once. `STDDEV` and `CORR` are
rounded by comparing squares against the midpoint, with no square root
computed: `√(S/d)` and `|C|/√(Sxx·Syy)` against each candidate's midpoint
`m` by `m² · d < S` and `m² · Sxx · Syy < C²`, with `C`'s sign
(`sqrtMag`). Each is one value, a function of the multiset of values
(`varOf_perm`, `covOf_perm`, `corrOf_perm`), whatever the engine's
algorithm.

NULL as before D30: no values, a sample of one, and for `CORR` fewer than two
pairs or a side whose values are all equal, which is `Sxx = 0` or `Syy = 0`
(`stat_degenerate` `NULL`; `corrOf` gave NULL there before D30 too). NaN and
infinities as `varOf` had them: a NaN among the values gives NaN, and an
infinity gives NaN in `Rel.eval` and raises in a plan the checker accepts,
since its deviation `∞ − ∞` would create a NaN (#257). A finite result past
the largest double raises (#575).

Engines keep their own algorithms: Welford's update with Chan's merge in
DuckDB, Spark and grouped Polars, a blockwise two-pass in ungrouped Polars.
Each is within the plan's bound of the reference's value: the algorithm's
distance from the exact moments (`StatProps`, proved for Welford and Chan as
`StdModel.core_var_chan`, `core_cov_chan`, `core_corr_chan` in
`float-bounds/`), plus half an ulp of the reference's rounding. Their
`stat_algo` rows are `approxWithin "plan"`, as `sum_order`'s are, and
`StatAlgo` keeps `StatProps` as what `GENERIC` and `WELFORD_CHAN` allow. The
writers clamp an engine's variance and deviation at `0` and its correlation
to `[-1, 1]`, NaN kept (`Dialect.clamp_stat`, Polars likewise): the exact
value lies in the interval, so clamping never moves the engine's value
further from it (`Stat.clamp_near`), and `var ≥ 0` and `|corr| ≤ 1`
hold of every engine's result. The bounds differ in kind: `VAR_*` and
`STDDEV_*` are relative to the spread, the deviation's half the variance's;
`CORR`'s is absolute, about `c · n · u`; `COVAR`'s is absolute, scaled by
`√(Sxx · Syy)`, or relative only under a sign-definite precondition.
`Report.epsilon` reports `VAR_*`, `STDDEV_*` and `COVAR_*` columns
(`Epsilon.statEps`). `CORR` has no data-free bound (decided 2026-11-08,
#918): its distance to the reference is bounded only under a lower bound on
both sides' variances (`core_corr_chan`'s `L`), stated by the user and
checked by the run as a precondition, never inferred. Without one, a `CORR`
postcondition beyond `[-1, 1]` and the clamp is tested only, and the report
names that precondition as the way to a bound (`Epsilon.corrWhy`). The
contract language has no preconditions on aggregates yet, so the stated
bound waits for them. Snowflake keeps
refusing these aggregates (Snowflake behaviour recorded privately).

Consequences:

- `stat_algo` is no longer a choice of the reference; it stays a choice of
  the engines, and the reference's row is `EXACT`.
- The statistical aggregates are order-free (`AggFn.orderFree`), so
  `Measure.closedB`, `Rel.closedB` and `Rel.detPlan` hold of plans with them,
  and `contract_sound_all` and `contract_sound_allowed_closed` cover them.
  `QUANTILE_CONT` stays the only open measure.
- `varOf_props`, `covOf_props` and `corrOf_props` are retired, and
  `Rel.eval_allowed` rests on Lean's standard axioms alone.
- A postcondition at a rounding boundary can move by an ulp, which
  `sv.approx` absorbs.

Why: before D30 the reference stated generic properties for these
aggregates and let engine profiles refine them, so a plan reading one left
the engine a choice of value. `Rel.FloatOpenSafe`, `contract_sound_allowed`'s
side condition, failed for any such plan: `SELECT VAR_POP(x)` allowed many
values while an order fixed one. Exact moments give one value with no
algorithm imposed on engines, as D25 did for sums, retire three axioms, and
are the state an exact incremental `VAR` needs (#918 Part B). The cost:
engines go from refining exactly to within a plan's bound.

### D31. Double arithmetic is exact, rounded once

Decided 2026-11-07 (#929).

The reference defines +, −, × and ÷ of doubles as the exact result rounded
once to binary64, to nearest, ties to even, with IEEE 754's rules for
infinities, NaN and the sign of zero: an exact zero from non-zero operands
is +0, products and quotients take the XOR of the signs, a non-zero result
that rounds to zero keeps its sign. The sign of a NaN an operation produces
is open; an engine fact may pin it per platform. `pow`, the libm functions
and casts to double are separate decisions. On an IEEE engine no finite
value changes; the eight float axioms become theorems. Each engine carries
one fact per platform, binary64 with round to nearest even, no contraction,
no flush to zero, checked by a differential probe; an engine without it gets
a shim or a refusal.

The reference observes these results through its own zero and NaN rules
(ONE_ZERO, #89; `on_division_by_zero`); a profile with IEEE `zero_sign` sees
the signed result. (Corrected 2026-11-09: see below.)

In the model (`core/Sverify/Core/FloatArith.lean`): every finite double is an
integer multiple of 2⁻¹⁰⁷⁴, so the exact sum, difference and product are
integers in that unit, the product in 2⁻²¹⁴⁸, and the quotient a fraction of
two. `ofExactDiv` rounds each, as it rounds D25's sums, to the nearest
multiple of `ulp = 2^max(e−52, −1074)` with ties by that multiple's parity,
and to `±∞` at `|q| ≥ 2¹⁰²⁴ · (1 − 2⁻⁵⁴)`. `addI`, `subI`, `mulI` and `divI` are
IEEE 754's operations on every code, `-0.0` and the negative NaN included.
The reference's `fadd`, `fsub`, `fmul` and `fdiv` are these operations on the
raw values, and on finite operands they are the rounded exact result up to the
sign of a zero (`fadd_fin` …, stated on `canon` of the result).

Consequences:

- `FloatCode.add_scaled`, `sub_scaled`, `mul_scaled`, `div_scaled`,
  `div_scaled_err`, `add_nonneg`, `mul_nonneg` and `div_nonneg` are theorems
  (#582's axioms). `FloatCode.exp_fin` (libm's `exp`) stays an axiom.
- `Expr.eval`'s `+ − × ÷`, the double sums and ratios of `Aggregate`,
  `Window`, `Profile`, `DuckDBSQL`, `AllowedP` and `AllowedNear`, and the
  interpolation of `QUANTILE_CONT`'s value use them; `contAllowed`'s interval
  stays, so the quantile's formula stays open. `pow` and `log` keep native
  doubles (`lift₂`).
- `FloatArithCheck.lean` checks the operations against native doubles bit
  for bit, signed zeros included, on edge values, ties and pseudo-random
  operands at every exponent; and the reference's against `lift₂`, which they
  replace.
- The checker computes with integers where it called the FPU, and no
  `@[implemented_by]` hides the IEEE assumption in its runtime.

Why: native `Float` is opaque to the kernel, so no rounding bound on `x + y`
or `x · y` was provable, and the checker trusted eight axioms for them. The
exact definitions make `Rel.eval` on doubles unfold in proofs, which the
tolerance fold of #929 needs for its arithmetic rows (`c · x`, `x ± y`,
`x · y`, `x / y`). The trust moves to each engine's fact.

**Correction, 2026-11-09** (approved by the maintainer, via the theory advisor):
"The reference is IEEE on the full float code set, signed zeros and signed
NaNs included; `canon` applies only at identity boundaries; the reference
raises or leaves the result open where engines disagree."

- Values stay raw. A read gives the stored double, and every scalar function
  of doubles, arithmetic, negation, `%`, rounding and the libm functions,
  runs on the raw value and gives IEEE's result, `-0.0` included:
  `0.0 * -1.0` is `-0.0`, `-(0.0)` is `-0.0`, `sqrt(-0.0)` is `-0.0`,
  `-4.0 % 2.0` is `-0.0`, `atan2(-0.0, -1.0)` is `-π`. There is no `canon`
  after a scalar operation. A NaN an operation produces is the NaN code (its
  sign stays open, as above).
- Under `zero_sign` = `ONE_ZERO` and `nan_kind` = `ONE_NAN`, `canon` applies
  at the identity boundaries: `=` and `<` (lists and structs element by
  element), and the keys of `DISTINCT`, `GROUP BY`, joins and window
  partitions. `-0.0 = 0.0` and `-NaN = NaN` are true. A profile with IEEE
  zeros applies it nowhere.
- Where the engines agree on `-0.0`, the reference gives their value:
  `CAST(-0.0 AS BIGINT)` and `CAST(-0.0 AS DECIMAL)` are `0`, `sqrt(-0.0)` is
  `-0.0`, `-0.0` is finite. Domains read one zero: `ln(-0.0)` raises as
  `ln(0.0)` does, `atan2(-0.0, 0.0)` as `atan2(0.0, 0.0)`. Where they
  disagree, the reference raises: `x / -0.0` and `x % -0.0` raise as
  `x / 0.0` does (DuckDB gives `-∞`, Spark under ANSI raises).
- In the model: `FloatCode.ofFloat` and `toFloat` keep `-0.0` (`ofParts`),
  `fmod` gives a zero the dividend's sign, casts and `FMath.inDomain` read
  `canon c`, `fneg` is `negI`. The contract analysis bounds a double by its
  canonical code (`NumKind.norm`); a function's soundness holds up to `canon`
  (`Value.CanonEq`), and the functions of native doubles, whose abstractions
  bound nothing, by their shape alone (`Value.ShapeEq`, `mapAbs_top_sound`).
- `ORDER BY` is an identity boundary too: it sorts by a total preorder on
  canonical values, and rows tied on it may come in any order (`Allowed`).
- Where a class has several members, a `DISTINCT` row, a `GROUP BY` key and
  a `MIN` or `MAX` may be any member of the class present in the input, or
  the class's canonical value (`IsReps`, `AggFn.Picks`). Spark and DuckDB
  emit the canonical value, so a group of `-0.0`s comes out as `+0.0`;
  Polars emits a present member. `Rel.eval` keeps one admitted value, the
  raw-least member. Where the keys and arguments hold no doubles, each class
  has one member and the output is unique (`aggAllowed_eq`, `Rel.detPlan`'s
  `noDoubles` guards). A whole condition can tell the members apart
  (`atan2`), so a `DISTINCT` keeps the facts with one value on a class: the
  comparisons of numbers, and conditions `Expr.canonSafe` admits
  (`Fact.classSafe`).
- Incremental maintenance keeps its state per class and emits the class's
  canonical key: the maintained output of `GROUP BY` and `DISTINCT` is one
  the reference allows (`LinearAgg.aggregate_maintained`,
  `distinct_maintained`, `ExtremeAgg.extreme_maintained`).

Why: the reference must compute what the engines compute on a stored or
computed `-0.0`. Canonicalising reads or results instead is unsound: `atan2`
tells the zeros apart, and a `-0.0` made mid-plan (`0.0 * -1.0`) escapes a
canonicalising read. The engines normalise exactly at the identity
boundaries (Spark's `NormalizeFloatingNumbers`, DuckDB's hashing, Polars's
grouping; their facts).

Note (2026-11-09, theory advisor): a zero in an option's scope is either zero
(`Value.hasZero` reads `FloatCode.isZeroCode`), so `zero_sign`'s scope holds
a `-0.0` argument or result too, and `fp.elem` takes `zero_sign` for `atan2`
(Spark's reads `-0.0` as `0.0`). No reference value or allowed set changes.

### D32. Calendar functions work on the reference's timestamps, 0001 to 9999

Decided 2026-11-08 (signed off by the maintainer, reviewed by the theory
advisor).

The reference's timestamps are those of its dates (#251): 0001-01-01
00:00:00 to 9999-12-31 23:59:59.999999, `Time.tsMin` to `Time.tsMax` in
microseconds since 1970. Every calendar function is defined on all of them,
with the proleptic Gregorian calendar of `core/Sverify/Core/Time.lean`.
`date_part`, `strftime`, `time_of_day`, adding months to a timestamp,
truncation to a week, month, quarter or year, truncation of a date, and
`date_bin` raise (`Issue.overflow`) where the operand or the result leaves
the range. They no longer depend on DataFusion's ±2⁶³ nanoseconds (1677 to
2262) or on chrono's ±262,142 years. 0001-01-01 is a Monday, so no
truncation of a timestamp in range leaves it. A `date_bin` origin outside
the range is refused when the plan is checked, never at run time.

A DATE or TIMESTAMP value of the reference lies in 0001–9999 by its type. A
source value outside it fails the read, named; a computed date outside it
raises (#251). Calendar functions are total on the reference's values
(`Value.InCalendar`, `UnFn.datePart_issue_of_inCalendar`): a column read
needs no guard and no inferred precondition, and only a computed argument
can leave the range. The read checks each DATE and TIMESTAMP column once,
from the Parquet files' min/max statistics where they cover it (Delta and
Iceberg write them), else with one range predicate over the read, and fails
with "<column> holds dates outside 0001–9999 (<count>, e.g. <value>); the
reference's calendar covers 0001–9999. Filter them, or read the column as
text." (`sverify.engine.Connection.put`).

Outside the range the engines disagree: DuckDB and Polars give
`date_part('year')` 0 and 10000, but `strftime` of year 10000 is
`+10000-01-01` on Polars and Spark, and the reference has no year 0. So the
reference raises there, as it does for date arithmetic (#251), and picks no
value.

Each 1.0 engine reaches the reference natively inside the range and with
one guard outside it:

| engine | inside 0001 to 9999 | outside | type the writer pins |
|---|---|---|---|
| DuckDB | native ([duckdb-calendar-range](../engines/duckdb/facts/duckdb-calendar-range.json)) | computes; the SQL guards | `TIMESTAMP` (µs) |
| Polars | native ([polars-calendar-range](../engines/polars/facts/polars-calendar-range.json)) | computes; the translation guards | `Datetime("us")`; `"ns"` covers only 1677 to 2262 |
| Spark | native ([spark-calendar-range](../engines/spark/facts/spark-calendar-range.json)) | computes; the SQL guards | `TIMESTAMP_NTZ`, session time zone UTC |
| Snowflake | reachable by a shim, probe pending: parts in year 1 are right and sverify truncates weeks itself (private facts); month, quarter and year truncation at the ends is not recorded | computes (years 0 to 302024); the SQL guards | `TIMESTAMP_NTZ` |
| DataFusion | refused: it truncates and bins in nanoseconds ([DF-17](../upstream/bugs/DF-17.json)) | — | — |

The facts record the probe points: 0001-01-01, the leap days 0004-02-29,
1600-02-29 and 2000-02-29, 1900-02-28 and 1900-03-01, both sides of the
Gregorian switch (1582-10-04 and 1582-10-15) and 9999-12-31, each at
23:59:59.999999. `Time.lean`'s `#guard`s and `test_time.py::test_d32_probe_points`
check the same points.

In the model: `Time.tsMin` and `Time.tsMax` replace `nsMin`, `nsMax`,
`nsDayMin`, `nsDayMax`, `partMin`, `partMax`, `chronoDayMin` and
`chronoDayMax`. `Time.datePart` is `NULL` outside the range, where
`UnFn.issue` now raises (`datePart`, `dayPart`); `UnFn.mayIssue` reports it
unless the operand's bounds are inside the range. A column's type gives
those bounds (`ContractCheck.typeEnv`: a DATE in `dayMin` … `dayMax`, a
TIMESTAMP in `tsMin` … `tsMax`), so a column read discharges it. `UnFn.mayIssue_sound` covers
the new rows with the existing `rangeIssue_sound`. `Infer.atIssue` infers the
range as a precondition.

Consequences:

- A `date_part` raises only on a computed argument: on the catalogue's 136
  queries the checker reports one such `date_part` issue, and TPC-H Q09's
  `EXTRACT(YEAR FROM o_orderdate)` stays proved. The SQL writers still emit
  the guard on every `date_part` (35 on the catalogue's DuckDB SQL, 480
  guards in all, from 445) until the checker's discharged issues reach the
  Polars writer (#1174) and DuckDB's (#1169), which drop those on column
  reads.
- Truncation and parts of timestamps from 1677 back to 0001 and from 2262 to
  9999 run on every 1.0 engine, where they raised before.
- `strftime`'s `%Y` is always four digits.

Why: the old ranges were DataFusion's, and DataFusion is a tier-3 engine
(2026-11-08). The SQL standard's timestamps are the reference's dates', which
every 1.0 engine represents.

### D34. An option differs from the reference only on its scope

Decided 2026-11-08, by the maintainer after the theory review.

Each option differs from the reference only on its scope, a predicate on the
call's arguments and reference result stated beside the option. Engine rows
are statements about the scope; agreement outside it is the function's base
row. A plan depends on an option only where a call may be in its scope.

In the model, `optionScope` (`core/Sverify/Core/Scopes.lean`) states each
option's scope, one row per option of the catalogue in its order, and
`Rel.AllowedP` reads it: a call (`CallExtra`) or an aggregate (`AggExtra`)
takes another value than the reference's only where its table allows one of
its group's options a behaviour the reference does not and the call is in
that option's scope. A scope may be wider than where the behaviours differ,
never narrower; one not pinned down yet is every call.

| Option | Scope |
|---|---|
| `overflow` | the exact result is outside the type's range (an integer `SUM` outside 64 bits) |
| `on_division_by_zero` | the divisor is zero |
| `division_type` | the operands have opposite signs and the remainder is not zero |
| `min_mod_neg_one` | `MIN % -1` |
| `nan_creation` | the arguments are not NaN and the IEEE result is: `∞ − ∞`, `0 · ∞`, `∞ / ∞`, `0 / 0`, `fmod(±∞, y)`, `fmod(x, 0)`, a `SUM` of `+∞` and `−∞` |
| `float_overflow` | the arguments are finite and the correctly rounded result is infinite |
| `zero_sign` | an argument or the reference result is a zero (underflow, `x − x`, a sum rounding to zero) |
| `round_zero_sign` | the reference result is a zero (`round(-0.4)`, `ceil(-0.4)`) |
| `pow_one_inf` | `power` of `±1` to `±∞`, or of `1` to NaN |
| `nan_equality`, `nan_order` | an argument is NaN, or holds one |
| `nan_kind` | an argument or the reference result is NaN |
| `on_domain_error`, `on_log_zero`, `substring_range`, `cast_failure`, `date_range` | the reference reports the issue at the call (a domain error, a failed cast, a date out of range) |
| `negative_start` | a negative start |
| `null_handling` | an argument is NULL |
| `empty_group_aggregates` | an aggregate of no values |
| `avg_int_result` | an `AVG` with an integer result (`AggFn.iavg`); a `SUM` never meets it |
| the others (`rounding`, `sum_order`, `stat_algo`, `tie_*`, `shift_range`, …) | every call |

`sum_order`'s true scope is a sum that is not exact; it is every call until
the analyses can tell. An engine's own order of additions, overflow to `±∞`
on the way included, is `sum_order`'s (`FloatSums`), so `agg.fsum`'s
`nan_creation` and `float_overflow` are about the correctly rounded sum.

Consequences:

- `Rel.AllowedP` only narrows. `Rel.allowedP_reference`, `Rel.AllowedP_mono`
  and `Rel.AllowedP_transfer` keep their statements.
- The engines' functions show each of their deviations in an option's scope
  (`Profile.duckdb_withinOk`, `Polars.written_within`). DuckDB's
  `fmod(x, 0)` is NaN under `nan_creation`, since its table gives `fp.mod`
  no other `on_division_by_zero`; Polars's NaN for `power` is a domain
  error's (`on_domain_error`), since `power` has no `nan_creation`.
- A call reads only its group's options that apply to it (`optionApplies`,
  `optionApplies_of_scope`), so a `SUM` does not read `avg_int_result`
  (`ctorReads`, `Rel.reads`, `Rel.AllowedP_transfer`).
- A plan's option dependency report keeps an option only where a call may be
  in its scope, from the arguments' abstract values (`Expr.eval_dead`,
  `Rel.AllowedP_transfer_live`, a follow-up), and reports the function's
  base row's evidence where every option is dead.

### D35. Engine summation orders are bounded sets

Decided 2026-11-08 (#929): approved by the theory advisor, to whom the
maintainer delegated the sign-off.

`SumOrder b vs c`, the doubles a double `SUM` gives under a `sum_order`
behaviour, bounds every behaviour but `EXACT`. On `n ≤ 2³²` finite doubles
whose `2 · Σ(|xᵢ| + 2⁻¹⁰²²)` stays below the largest double, the sum is finite
and within `(γₙ + u) · Σ(|xᵢ| + 2⁻¹⁰²²)` of the exact sum, `u = 2⁻⁵³`,
`γₙ = nu / (1 − nu)` (`SumBound`). Stated in units of `2⁻¹⁰⁷⁴` and multiplied
out, it is an exact inequality on integers, so it needs no rounding of its
own.

- `ANY` and `PAIRWISE` keep their trees (`FloatSums`) and `SEQUENTIAL` its
  permuted sequential sum, each with the bound.
- `COMPENSATED` (Kahan's sum, Polars) and `SCALED_CONSTANT` (a constant run's
  `fl(k · x)`, DuckDB) were any double. They are now the bound alone: no
  theorem of the core reads their shape (`TreeSum.const` is float-bounds').
- `AvgOrder` follows: a sum within the bound, divided by the count.
- `EXACT`, the reference's order (D25), is unchanged.
- Window sums take their frame's `SumOrder` (`WinFn.AllowedP`): `TREE` and
  `RECOMPUTE` sum each frame's own values. `RUNNING_ADD` is a running state
  over the partition's prefix that never removes a row (duckdb-window-sum-order,
  spark-window-agg), so its value at a row is a sum of exactly the rows
  before it, the frame of the growing windows it runs: the prefix bound is
  the frame's, by those facts. A sliding sum (`SLIDING`) stays any value.

What stays trusted: the engines' algorithms meet the bound. `StdModel`'s
theorems in `float-bounds` justify it on the engines' facts
(`StdModel.Summed.near`, `epsilon_sum_cr`, `Rnd.kahan_near`), as the
`sum_order` rows' evidence. #1196, the bridge from float-bounds to the core,
retires it.

Why: `Rel.AllowedP` is the set the soundness theorems quantify over. A
behaviour that allows any double made every contract on a double `SUM`
unprovable at the plan level on DuckDB and Polars, although both algorithms
are bounded. `SumOrder.bound` reads the bound as a range the abstract domain
computes (finite, in `[sumLo, sumHi]`), which cuts `nan_creation`,
`float_overflow` and the NaN cases of a comparison downstream (D34), and the
margin check's theorem over its plan reads the same set.

### D36. Doubles have one zero and one NaN

Decided on [#89](https://github.com/AlexanderNenninger/substrait-lean/issues/89), merged 2026-10-31, and on #209.

The reference profile reads doubles with one zero and one NaN:
`zero_sign` `ONE_ZERO`, `nan_kind` `ONE_NAN`, `nan_equality` `NAN_IS_NAN`
and `nan_order` `GREATEST`, above `+∞`. `-0.0` is `0.0` everywhere, so
`1.0 / -0.0 = inf` where the plan asks for IEEE division, and `GROUP BY`,
`DISTINCT`, joins, partitions and sorts see one zero and one NaN. The core
keeps both zeros and the signed NaNs ([The value domain](core-semantics.md#the-value-domain));
the reference applies `FloatFormat.canon` to every input and output, as the
writers do (`Dialect.canon`). Substrait's YAMLs leave the grouping and
order of `-0.0` unspecified and compare NaN by IEEE's rules, so this is an
override ([Overrides](reference-semantics.md#overrides)).

Why: SQL users expect `-0.0 >= 0` and a NaN equal to itself, and DuckDB,
Polars and Spark compare NaN so (`nan_equality` `NAN_IS_NAN` in their
tables); IEEE's NaN, unequal to itself,
would split `GROUP BY` and `DISTINCT` and drop rows from joins.

### D37. No operation creates a NaN

Decided on #185 ("no newly created NaNs") and [#257](https://github.com/AlexanderNenninger/substrait-lean/issues/257), closed
2026-11-02.

No operation creates a NaN. An operation on non-NaN inputs whose IEEE
result is NaN is an issue (`Issue.domain`, `nan_creation = ERROR`), which
`verify` rules out or checks on the data; on the rows a precondition
excludes, `Rel.eval` keeps IEEE's value (NaN), as it keeps ±∞ under #575.
Under a verification profile that sets `nan_creation = NAN`, no issue fires
and the value is NaN. A plan that asks for IEEE division by zero (D39) makes
`0 / 0` such a NaN creation too: it raises under the reference, and only a
profile with `nan_creation = NAN` (DuckDB's) gives the NaN.

Why: with no NaN in the inputs (`~_.v.isnan()` in `requires`), there is
none in the outputs. Engines give NaN, NULL or an error there, and a plan
proved to never raise reaches none of them, so no engine needs a shim
([D21](#d21-tighten-the-reference-where-it-stays-practical)).

### D38. No operation on finite doubles overflows to infinity

Decided on [#575](https://github.com/AlexanderNenninger/substrait-lean/issues/575), closed 2026-11-04.

A `±∞` from the data passes through. An operation on finite doubles whose
IEEE result is `±∞` raises: `+`, `-`, `*`, `/` and `power` that overflow
(`1e308 * 10`, `power(10, 400)`, `power(0, -1)`), `exp` past `709.78`, and a
`SUM`, `AVG`, variance, covariance or correlation of finite values that
overflows (`Issue.infinite` in `Safety.lean`). `verify` rules the error out
by an inferred precondition: proved from the bounds where they do it,
otherwise listed in `Report.assumed` and checked on the data. `Rel.eval`
keeps the IEEE value on the rows the precondition excludes, so the lift of
DuckDB's SQL with `semantics="duckdb"` states DuckDB's result exactly.

Why: with no NaN and no `±∞` in the inputs, there is none in the outputs,
and every floating result has a usable bound. Substrait's YAMLs leave the
overflow unspecified ([ST-9](../upstream/bugs/ST-9.json)), and the
precondition rarely bites real queries (D21).


### D39. Division by zero has an IEEE value

Decided 2026-11-09 (theory advisor), within D31's correction.

`on_division_by_zero` gains the value `IEEE`. With it, `x / y` is IEEE 754's
quotient on the raw codes (`BinFn.fdivIeee`): by `0.0` or `-0.0` it is `±∞`
with the sign of the dividend XOR the sign of the divisor. It reads the
divisor's raw sign as a scalar operation does (D31), with no comparison of
`y` with zero. `0 / 0` and `±∞ / ±∞` create a NaN, so they raise under D37
(`nanCase`); only a profile with `nan_creation = NAN` gives the NaN, as
DuckDB's run profile does. An overflow of finite operands to `±∞` raises as
D38 says; a quotient by zero is the option's value, not an overflow
(`BinFn.infIssue`). The reference keeps `ERROR` and D37 unchanged: a portable plan raises at
any zero divisor and creates no NaN. DuckDB's IEEE operations are this
division, so the lift of DuckDB's `/` with `semantics="duckdb"` writes the
option, with `0 / 0` and `±∞ / ±∞` as NaN, as DuckDB gives them
(`DuckDBSQL.fdiv_of_canon_zero`). A Substrait plan spells it as
`divide` with the option, which the parser reads as `fdivIeee`.

Why: DuckDB gives `1.0 / -0.0 = -∞` (duckdb-float-signs). With one zero at
comparisons (D31), no expression of comparisons can tell the divisor's sign,
so the reference could not state DuckDB's division, and the lift had to
refuse `/` and everything built on it (`round(x, d)`). A dedicated operation
exposes `FloatCode.fdiv`, which is IEEE on every code already, and no other
expression gains access to the sign of a zero.

### D40. `power(±1, ±∞)` is C's `pow`

Decided 2026-11-09 (theory advisor).

`pow_one_inf` is IEEE 754's choice between `pow` and `powr` at their one
disagreement on numbers: `power(±1, ±∞)` and `power(1, NaN)`. `pow` (C's,
`ONE`) gives `1`; `powr` (`NAN`) gives NaN, as Java's `StrictMath.pow` does.
The reference is `ONE`: it computes `power` with C's `pow` on the raw doubles
(`FloatCode.lift₂ Float.pow`), as DuckDB and Polars do
([duckdb-pow-one-inf](../engines/duckdb/facts/duckdb-pow-one-inf.json),
[polars-pow-one-inf](../engines/polars/facts/polars-pow-one-inf.json)). Spark's profile
is `NAN` ([spark-math-domain](../engines/spark/facts/spark-math-domain.json)); its writer
refuses double `power`, so no portable plan meets it there. The scope is
`powOneInf` (`core/Sverify/Core/Issue.lean`). No reference value changes.

Why: an option states both engines' values, where a raise would take `1` from
the plans that DuckDB and Polars compute alike.

Also decided: `float_to_int`'s scope reaches `floor`, `ceil` and one-argument
`round` (`fp.floor`, `fp.round`), where an engine returns a `BIGINT` (Spark: NaN
is `0`; `±∞` and values past 64 bits overflow,
[spark-floor-ceil-bigint](../engines/spark/facts/spark-floor-ceil-bigint.json)). The
reference stays a double, and the `BIGINT` is the writer's cast.
