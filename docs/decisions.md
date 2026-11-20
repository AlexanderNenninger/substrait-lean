# Decisions

The decision log of sverify's semantics, for contributors: each choice the
reference, the core and the profiles make, with when and why it was made.
[core-semantics.md](core-semantics.md) is the design they apply to, and
[reference-semantics.md](reference-semantics.md) states the resulting
behaviour for users, without the history.

A decision that a later one corrects or replaces, in whole or in part, carries
a dated `Amended`, `Correction` or `Superseded` line under its heading, with
a link to the later decision, and its text above that line is the history. The
text of the later decision is the live rule, and each rule is stated there once.

Every decision after D49 ends its section with a line, `Recomputes sinks: yes`
or `Recomputes sinks: no`. A decision that changes a value of the reference or
narrows what it allows says yes, and its D-number goes into
`MEANING_CHANGES` (`python/src/sverify/incremental.py`), which the plan digest
a sink records hashes in: the sink is then recomputed once. A decision that
only opens a choice says no, since the stored rows stay among the allowed
results. `tests/test_plan_digest.py` checks the lines against the record.


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

Amended 2026-11-18 by [D48](#d48-a-result-is-determined-up-to-the-classes-its-observation-reads):
"determined" is up to row order and the member of each class of doubles, and
an observation that reads the members asks for the exact level.

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
rows the engine's model computes for the translated plan, under the engine's side condition (`Engine.NoRaiseSide` for DuckDB, `Engine.GuardFreeSide` for Polars and Spark, none for the reference).
The engine's actual output rests on `Engine.Runs` and the transfer check
(`Engine.contract_sound_runs`). Which options it fails on, engine by engine,
is [the realizability table](realizability.md) ([#900](https://github.com/AlexanderNenninger/substrait-lean/issues/900)).

### D14. Engine versions

An engine profile is tied to the engine's versions: it records the version,
or range, its facts were probed at. A run on another version warns, and a
run on another major version is refused until the probes are re-run. A new
version that changes a fact gets a new fact with `supersedes` (the `engine-fact`
skill) and a new row in the profile. Facts hold for the version they
were probed at, and the profile is only as good as its facts.

Amended 2026-11-20 by [D70](#d70-engine-versions-probed-in-range-out-of-range):
the range is the minor releases that hold a probed version, an unprobed version
inside it warns, and one outside it is refused.

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
translated plan, under the engine's side condition (`Engine.NoRaiseSide` for DuckDB, `Engine.GuardFreeSide` for Polars and Spark, none for the reference), through each engine's `Engine.Sound`. That the engine's actual
result is one its table allows stays trusted, as `Engine.Runs`, resting on the
tested rows `Engine.Refines` lists ([What is trusted](proofs.md#what-is-trusted)).

Amended (2026-11-17): that the translated plan does not raise is DuckDB's side
condition (`Engine.NoRaiseSide`), since DuckDB's model is its profile's
functions where they do not raise (`okImpl`). `Engine.Sound` and
`Engine.contract_sound` no longer take it: Polars and Spark hold under
`Engine.GuardFreeSide` and the reference under no condition
([#1484](https://github.com/AlexanderNenninger/substrait-lean/issues/1484),
finding 13). A run that raises returns no result, and `Engine.Runs` speaks of
a result, so the guarantee to a user is the same.

### D17. Changing the reference

While sverify is on 0.x, the reference changes where the design needs it. A
change to the reference ships in a minor version bump, with a
`changelog.d/` fragment that says what changed. Bumping the minor version
costs little, and the fragment tells users which proofs may change.

Amended 2026-11-18 (approved by the maintainer): from 1.0 a change to the
reference is one of two kinds. An opening only makes more plans proved or
run: a raise becomes a value, an allowed set grows, a refusal is accepted.
It ships in a minor version. A changed value, a new raise or a narrower
allowed set ships in a major version. Each has a `changelog.d/` fragment that
names the decision.

Why: a plan proved under one minor version stays proved, with the same
values, under the next.

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

Amended by [D50](#d50-the-frontends-lift-and-and-or-so-a-guard-protects-the-next-operand):
the core stays eager, and the frontends lift an `AND` or `OR` over a raising
operand so a guard protects it.

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
evaluates it on rows the analysis covers. A join whose other side is empty
has no pairs, while DuckDB still evaluates the pushed filter on the side's
rows. `Rel.HasIssueAll` models that case too (#1484 R3): each subexpression a
condition always evaluates may run on the rows of the join inputs it reads,
the other inputs' columns NULL (`Rel.ViewAllowed`), and
`Rel.mayIssues_sound_all` proves that `Rel.mayIssues` reports it.

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

Note (2026-11-19, theory advisor): D19 states the reference's raise set. An
engine may evaluate a conjunct on fewer pairs: a pair that another conjunct
makes not TRUE is in no allowed result (`isTrue_and3`), so by D16 the engine
may return there. Polars's hash-join keys do, and DuckDB's joins do. No
reference value, allowed set or raise set changes.


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
  `q_det`. `q_det` also chooses the level of determinism: one that reads the
  members of a class asks for the exact level
  ([D48](#d48-a-result-is-determined-up-to-the-classes-its-observation-reads)).

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

Note 2026-11-18: [D47](#d47-raise-value-or-open-where-engines-differ) states
when the reference raises. The `power(-∞, y)` example is a domain raise under
its rule 2: a negative base with a non-integer exponent is outside the real
power function's domain, whatever the base's size.

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

Amended 2026-11-18 (theory advisor): a condition is inferred when it is a
condition on single rows of an input that the report prints as a `requires`
line: a non-zero divisor, a bound on an integer operand, an argument in a
function's domain. It is assumed when no single input row decides it: a `SUM`
fits 64 bits (it depends on the group's size), and an operation on doubles
stays finite (stating it on the inputs needs a bound on every double column).
Assumed conditions keep their checks on the data (`Report.assumed`,
`Issue.assumed`). An unmet inferred precondition gives the verdict
`unproved`, and a plan whose only open conditions are assumed gives
`proved_with_checks`.

<a id="d24-tie-order-belongs-to-the-deterministic-profile"></a>

### D24. Tie order is open, and determinism is proved

The reference leaves `tie_order` and `tie_pick` open. Rows that tie in an
`ORDER BY` or in a window's order come in any order, a `FETCH` takes the
first rows of any order the plan allows, and `FIRST`, `LAST`,
`ARG_MIN`/`ARG_MAX`, `STRING_AGG`, `collect` and `MODE` take the rows that
tie in their own order in any order. `Rel.OrderAllowed`
(`core/Sverify/Core/OrderAllowed.lean`) holds the results of every such order, and a
contract holds on all of them: `contract_sound_all` for postconditions,
`Rel.keys_sound_all` for keys. An engine's own pick is one of these orders,
so it runs natively.

`Rel.eval` computes one allowed order: a stable sort (`List.mergeSort`) and
rows in list order (`Rel.eval_orderAllowed`). Determinism is a property the
checker proves of a plan, not a profile: a plan is determined when every
result the reference allows is `Rel.eval`'s up to row order (`Rel.detPlan`). A
consumer that needs a rerun to give the same rows asks for it, through
`run(reproducible=sv.equivalent())` or a sink's `reproducible=`
([D10](#d10-determinism), [D20](#d20-two-observations-per-output)). Engines
read tables in an order of their own, so no shim reproduces list order on
them, and a plan whose order is total, by a tie-break key or a uniqueness
precondition, is the one that qualifies. A plan without one is refused for
that requirement, and the refusal names each place where ties stay open
(`str(report)`, with the keys that would close them in `Report.ties`).
Since [D48](#d48-a-result-is-determined-up-to-the-classes-its-observation-reads)
determinism has two levels: up to the member of each class of doubles
(`Rel.detClass`, `Report.deterministic`), and exact (`Rel.detPlan`).

An order-sensitive operator reads one sorted enumeration of its input, and
its meaning is the set over all of them (`Lin` and `Sem`,
`analysis/Sverify/Analysis/Seam.lean`, #928). Below an unordered operator, as with a
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

Amended 2026-11-18 (theory advisor): two refusals predate this decision and
go.

- Spark's writer refuses a `FETCH` and a window over ties unless the report
  is deterministic, because no Spark order "can stand for Lean's list order"
  (`engines/spark/src/sverify_spark/dialect.py`).
  Spark's own pick is one of the allowed orders, so the plan runs natively.
  Its rerun row for `tie_order` says what two runs agree on.
- The parser refuses `MODE` without an `ORDER BY`
  (`frontend/Sverify/Frontend/Parse.lean`). Without one every row
  ties, so any of the most frequent values is allowed (`tie_pick`), and the
  report names the place.

Each opens when its engine fact exists: Spark's tie behaviour for sorts,
`LIMIT` and windows, and each engine's `mode` returning one of the most
frequent values. Until then the refusal's message names the missing fact.

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
  plan with open measures goes through `contract_sound_allowed` and
  `Rel.FloatOpenSafe`. Amended 2026-11-19: no double `SUM` or `AVG` is an open
  measure after D25, so `Measure.openB` and the machinery for it are removed.
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
since its deviation `∞ − ∞` would create a NaN (#257; `nan_creation`'s scope
covers it, `AggFn.nanCase`). A finite result past
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

Note (2026-11-16, #1486; no new decision): `StatProps`, the model of
`GENERIC` and `WELFORD_CHAN`, asked for the reference's own value outside
`Stat.fits` (more than 2³² values, or one above 2³⁹⁸ in magnitude). For
finite values that is false: `var_pop([1e150, 3e150])` is
`1.0000000000000002e+300` exactly rounded and `9.999999999999999e+299` on
DuckDB 2.0.0 and on streaming Polars 2.1.0. The last branch of `varStat`,
`covStat` and `corrStat` now splits in three: a NaN or an infinity among the
values gives the reference's value (`nan_through`, the infinity raise and
`Stat.nanGuard_varStat` rely on it); finite values inside `Stat.fits` give
the properties; finite values outside it are open, any double. No verdict
changes: such a column has no plan bound (`doubleMag`, `statEps`) and the
route reports it unproved. The reference's value and its promises are
unchanged.

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
  a `MIN` or `MAX` in a group or a window frame may be any member of the
  class present in the input, or the class's canonical value (`IsReps`,
  `AggFn.Picks`, `WinFn.Allowed`; `QUANTILE_DISC` too since D45). Spark and DuckDB
  emit the canonical value, so a group of `-0.0`s comes out as `+0.0`;
  Polars emits a present member. `Rel.eval` keeps one admitted value, the
  raw-least member. Where the keys and arguments hold no doubles, each class
  has one member and the output is unique (`aggAllowed_eq`, `Rel.detPlan`'s
  `noDoubles` guards, which belong to the exact level since
  [D48](#d48-a-result-is-determined-up-to-the-classes-its-observation-reads)). A whole condition can tell the members apart
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

Note (2026-11-15): the writers still applied the earlier rule, canon on every read and scalar result, so the written plan gave `atan2((0.0 * -1.0) + 0.0, -1.0) = π` where the reference gives `-π` (#1461). The writers print raw values and canon a key only where an engine's fact says its boundary tells the zeros apart. No reference value or allowed set changes.

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
the range. They no longer depend on a ±2⁶³ nanosecond range (1677 to 2262)
or on chrono's ±262,142 years. 0001-01-01 is a Monday, so no
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

Why: the old ranges were DataFusion's, which sverify no longer supports
(2026-11-09). The SQL standard's timestamps are the reference's dates', which
every 1.0 engine represents.

### D33. Unused

The number is unused. For an hour on 2026-11-08 it named the decision that is
now D37 (commits `b7281220` and `b202090f`); D37 took its place, and D33 was
not reassigned so that the numbers cited in commits stay unambiguous.

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
| `nan_creation` | the arguments are not NaN and the IEEE result is: `∞ − ∞`, `0 · ∞`, `∞ / ∞`, `0 / 0`, `fmod(±∞, y)`, `fmod(x, 0)`, a `SUM` or `AVG` of `+∞` and `−∞`, a variance, standard deviation, covariance or correlation of an infinity, a `QUANTILE_CONT` between a `-∞` and a `+∞` neighbour (`AggFn.nanCase`) |
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
  `fl(k · x)`, DuckDB) were any double. They are now the bound alone and
  exactness on small integers: no theorem of the core reads their shape
  (`TreeSum.const` is float-bounds').
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

Amended 2026-11-19 (#1608 12b-1): in `SumOrder`, the behaviours with no
shape (`SCALED_CONSTANT`, `COMPENSATED`) are the bound and exactness on small
integers: where every double of `vs` is an integer and `Σ |vᵢ| ≤ 2⁵³`
(`SmallInts`), `canon c` is the exact sum's. `AvgOrder` inherits it through
its sum. The shaped behaviours prove it (`SumOrder.int_exact`), and a mean
of such values is the reference's (`AvgOrder.int_exact`), so a double `SUM`
or `AVG` of converted integers with `N · max M 1 ≤ 2⁵²` has no tolerance
(`Epsilon.intMeanExact`). `float-bounds` backs the conjunct as
`Summed.near` backs the bound: `StdModel.Summed.int_exact`, under the model
hypothesis `StdModel.ExactInts` (integers up to `2⁵³` round to
themselves). The reference's `EXACT`, `Rel.eval` and the reference's
`Rel.Allowed` do not change. Engine profiles narrow on such sums, on each
engine's evidence (`engines/*/tests/test_*int_sums.py` over
`python/tests/_int_sums.py`; Snowflake's recorded privately).

### D36. Doubles have one zero and one NaN

Decided on [#89](https://github.com/AlexanderNenninger/substrait-lean/issues/89), merged 2026-10-31, and on #209.

The reference profile reads doubles with one zero and one NaN where rows are
compared for identity: `zero_sign` `ONE_ZERO`, `nan_kind` `ONE_NAN`,
`nan_equality` `NAN_IS_NAN` and `nan_order` `GREATEST`, above `+∞`. `-0.0 = 0.0`
in a comparison, and `GROUP BY`, `DISTINCT`, joins, partitions and sorts see
one zero and one NaN. Values stay raw elsewhere: a read gives the stored
double and a scalar operation gives IEEE's result. D31's correction has the
full rule: domains and casts read one zero, so `ln(-0.0)` raises and
`CAST(-0.0 AS BIGINT)` is `0`, and a `DISTINCT` row, a `GROUP BY` key, `MIN`
and `MAX` may be any member of the class or the canonical value. Where the
plan asks for IEEE division (`on_division_by_zero: IEEE`, D39), `1.0 / -0.0`
is `-∞`; the reference's own `/` raises at a zero divisor of either sign (D31's
correction; D39: "The reference keeps `ERROR`"). The core keeps both zeros and
the signed NaNs ([The value domain](core-semantics.md#the-value-domain)); the
reference applies `FloatFormat.canon` at the identity boundaries only.
Substrait's YAMLs leave the grouping and
order of `-0.0` unspecified and compare NaN by IEEE's rules, so this is an
override ([Overrides](reference-semantics.md#overrides)).

Why: SQL users expect `-0.0 >= 0` and a NaN equal to itself, and DuckDB,
Polars and Spark compare NaN so (`nan_equality` `NAN_IS_NAN` in their
tables); IEEE's NaN, unequal to itself,
would split `GROUP BY` and `DISTINCT` and drop rows from joins.

**Correction, 2026-11-15** ([#1446](https://github.com/AlexanderNenninger/substrait-lean/issues/1446)),
by the theory advisor, applying D31's correction:
as first written, this decision had the reference apply `canon` "to every
input and output" and give `1.0 / -0.0 = inf`. D31's correction of
2026-11-09 replaced that rule: `canon` applies only at the identity
boundaries, values stay raw, and the code follows it (`Expr.lean`'s
`fdivIeee` is `FloatCode.fdiv`). The text above is D31's rule; the decision
keeps its number.

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

Note (2026-11-19, theory advisor, ruling 163): `pow_one_inf` is `power`'s alone, so
`power` of doubles is the group `fp.pow` and `atan2` the group `fp.atan2`, where both were
in `fp.elem`; the unary functions stay there, without `pow_one_inf`. Routes class by
(group, option), so every unary function had inherited Spark's refusal of an option it
never reads. No reference value or allowed set changes.

Also decided: `float_to_int`'s scope reaches `floor`, `ceil` and one-argument
`round` (`fp.floor`, `fp.round`), where an engine returns a `BIGINT` (Spark: NaN
is `0`; `±∞` and values past 64 bits overflow,
[spark-floor-ceil-bigint](../engines/spark/facts/spark-floor-ceil-bigint.json)). The
reference stays a double, and the `BIGINT` is the writer's cast.

### D41. `modulus` of doubles accepts `division_type: FLOOR`

Decided 2026-11-15 (theory advisor).

`TRUNCATE` stays the default: `sverify_fmod`, C's `fmod`, exact. A plan that
states `division_type: FLOOR` on `modulus` of doubles means the expression
`a - b * floor(a / b)` in the reference's own double operations
(`Expr.floorFmodOf`, `engines/polars/Sverify/Polars/Profile.lean`), each
operation rounded and raising where it raises. It is not the correctly
rounded floored remainder: `1e20 % 3.0` is `0.0`. `Rel.eval` and `Rel.Allowed`
do not change.

Why: Polars's `%` of doubles computes this expression
([polars-double-modulus](../engines/polars/facts/polars-double-modulus.json)),
over its own `/` whichever kernel that takes
([polars-scalar-divisor](../engines/polars/facts/polars-scalar-divisor.json)).
No engine computes a correctly rounded floored remainder of doubles natively.
The template uses the reference's own operations, so every engine computes it,
and no plan the reference accepted before changes meaning.

### D42. The reference's value of the options no earlier decision states

Signed 2026-11-15 by the theory advisor ([#1446](https://github.com/AlexanderNenninger/substrait-lean/issues/1446)).
It states what `Profile.reference.table`
(`core/Sverify/Core/Options.lean`) does and changes no behaviour.

An option enters the core with the reference's value for it recorded as a
decision. These options had none: some were named nowhere in this record,
others only in D34's scope table, which gives their scope and no value, or in
a decision that names the option without its value. The reference's value of
each is:

| Option | The reference's value | Decided by |
|---|---|---|
| `division_type` | `TRUNCATE`: the remainder takes the dividend's sign; `FLOOR` is taken for integer `//` and `%` (`int.div`, `int.mod`) and for `%` of doubles (`fp.mod`, D41) where the plan asks; double division has no `FLOOR` | `Int.tmod`, `FloatCode.fmod`; D41 for doubles |
| `min_mod_neg_one` | `ZERO`: `MIN % -1` fits and is `0`; DuckDB's raise is its own (duckdb-R15-int-modulus) | D2 admits DuckDB's raise as an engine's extra raise; the value is this decision |
| `overflow` | `ERROR` at the declared width; `SILENT` or `SATURATE` on `int.arith` (`+`, `-`, `×`, negation) where the plan asks; refused on decimals | #202, #241 |
| `shift_range` | `DROP_BITS`; DuckDB's raise at `<<` is its own | D3 names the option; D2 admits DuckDB's raise |
| `decimal_rescale` | `TIE_AWAY_FROM_ZERO` when a result scale is smaller than the exact one | this decision |
| `round_zero_sign` | `ANY`: either zero, observed up to `canon`; `eval` gives `+0.0` | D34 (scope); the ruling of 2026-11-09 in duckdb-R15-round |
| `negative_start` | `LEFT_OF_BEGINNING` where the plan asks (`Text.substr`), `WRAP_FROM_END` otherwise (`Text.substrWrap`); `ERROR` is not modelled | #209 |
| `char_set` | `UTF8`; `ASCII_ONLY` is refused | this decision |
| `float_to_int` | `TRUNCATE` | D40 gives only its scope; the value is this decision |
| `cast_failure` | `THROW_EXCEPTION`, also for an unspecified `failureBehavior`; `RETURN_NULL` where the plan asks | this decision |
| `rounding` | `TIE_AWAY_FROM_ZERO` at `fp.round`, beside `TIE_TO_EVEN` elsewhere (native doubles) | #335; D5 for `TIE_TO_EVEN`; [D55](#d55-a-sql-cast-of-a-double-to-an-integer-rounds-half-to-even-as-a-composition) for `TIE_TO_EVEN` at `fp.round` |
| `quantile_interp` | `BETWEEN` | D13 names the option without a value; the value is this decision |
| `on_domain_error` | `ERROR`: outside its domain an elementary function raises | D37 |
| `on_log_zero` | `ERROR`: a logarithm of zero raises | D37 |
| `window_sum_algo` | `RECOMPUTE`: the frame's sum is computed anew | D25's note of #1032; D35 |
| `case_sensitivity` | `CASE_SENSITIVE`: string matching is case-sensitive; the other values are refused | this decision |
| `null_handling` | `ACCEPT_NULLS` (`concat` with a `NULL` is `NULL`); `IGNORE_NULLS` is refused | this decision |
| `date_range` | `ERROR`: date arithmetic past 0001-01-01 … 9999-12-31 raises | D32 |
| `time_interval_months` | refused: `TIME ± INTERVAL` with months has no value | this decision |
| `list_null_order` | `NULL` in `<` of lists; `GREATEST` in `ORDER BY`, `MIN` and `MAX` (`agg.order`) | #207 |
| `avg_int_result` | `DECLARED_TYPE`: the plan's output type, `fp64` or `i64` truncated | this decision |
| `clustered` | `ADJACENT`: equal keys are adjacent, the groups in any order | the `CLUSTERED` direction of Substrait's `relations/basics.md` |
| `ntile_spread` | `STANDARD`: the SQL standard's spread of the remainder | this decision |
| `distribution` | `SAMPLE` unless the plan asks for `POPULATION` | #54 |
| `empty_group_aggregates` | `NULL`: a `SUM` of no values or of `NULL`s only (the YAML's `sum`; `sum0` is `0`) | this decision |
| `null_join_keys` | `NO_MATCH`: a `NULL` key matches nothing, SQL's `=` | this decision |
| `string_positions` | `ONE_BASED_CHARS`: characters from 1, the YAML's | this decision |
| `substring_range` | `ERROR`: an offset outside `[-2³², 2³²)` or a length of `2³²` or more raises | #336 (`core/Sverify/Core/Text.lean`) |

Why: the rule is that the reference changes only through a recorded decision
and an option enters the core with its value recorded. The rows whose "Decided by" is this decision were never ruled on in this record; they record the values as of 2026-11-15, and a later decision changes one as D17 describes. A test (`tests/test_decisions_name_options.py`)
keeps every option of the core named in this file.

### D43. Text the engines map differently is an issue, `nonAscii`

Amended 2026-11-18 by [D51](#d51-case-mapping-has-the-value-the-engines-agree-on):
`UPPER` and `LOWER` leave this decision for `case_mapping`. The rest stands.

`UPPER`, `LOWER`, `ILIKE`, `reverse`, `ascii`, `levenshtein` and a regular
expression with a class (`\d`, `\w`, `\s`, `\b`) give Rust's values on ASCII
text, and the engines give their own elsewhere: DuckDB maps `ß` to `ẞ` where
Rust gives `SS`, and Rust's `\s` includes the vertical tab where RE2's does
not. The reference raises where the engines can differ, as
`Issue.nonAscii` (`core/Sverify/Core/Issue.lean`), under the option
`non_ascii_text` (`ERROR`, `COMPUTE`; the reference's value is `ERROR`).
`COMPUTE` says an engine gives a value where the reference raises. The
option names no table, so an engine profile states its own mapping.

The condition is `Text.isAscii`, and for a class regular expression
`Text.classesDiffer`: ASCII without the vertical tab (`Text.isPlain`). The
analysis carries it as two flags of `AVal` (`ascii`, `plain`), set by a column
declared ASCII in the checker's request (`"text"`, trusted as the schema's
nullability is) and by a literal's text, and `UnFn.mayIssue` and
`BinFn.mayIssue` report `nonAscii` unless every text operand has them. For
each reported issue the checker infers the base-table text columns that must
be ASCII (`Infer.asciiNeeds`), and Python renders the precondition and checks
it on the data (`Report.check_inputs`). The writers' guard raises on the same
predicate, so the run-time behaviour does not change and the report now lists
what the written SQL raises on (S9, #1484).

Why: the guard was the one writer check that no issue stated, so a plan with
`UPPER` over an unconstrained column reported nothing and the run raised on
the first accented name. `assumed` was rejected as the mechanism: an
assumption the model does not state leaves the invariant with an exception.
Plans with these functions on text not known to be ASCII move from proved to
an inferred precondition under every `semantics`; a per-engine value, and the
guard narrowing to the characters that differ, are later and rest on facts.

The option sits on the group `str.ascii` (`reverse`, `ascii`, `levenshtein`,
`ilike` and the regular expressions; D51 moved `upper` and `lower` to
`case_mapping` on `str.case`), because a profile transfer reads options by
group: it gives a call every option of its group, so an option sits on the
groups whose functions can report its issue, and `str.plain` (`length`,
`repeat`, trims) and `str.opaque` (`md5`, `sha256`) carry none. A `#guard` in
`Scopes.lean` ties a function's group to its issue. The transfer is static:
under `semantics="substrait"`, where `non_ascii_text` allows `COMPUTE`, those
seven functions are unproved on the option whether or not the column is
declared ASCII, as `substring_range` is on `str.sub`; a transfer that skips a
raise option whose issue the analysis rules out is a follow-up.

### D51. Case mapping has the value the engines agree on

Approved 2026-11-18 by the maintainer. It replaces D43's raise for `UPPER` and
`LOWER`; D43 landed first as written.

`UPPER` and `LOWER` map a character as DuckDB, Polars and Spark all map it, and
raise on a character they map differently or that one of them does not know
(D47, rule 4). The raise is the issue `Issue.caseDiffers`
(`core/Sverify/Core/Issue.lean`) under the option `case_mapping` (`ERROR`,
`COMPUTE`; the reference's value is `ERROR`, Substrait's `COMPUTE`).
The tables are generated from one fact per engine and version
(`python -m sverify_dev.case_mapping`: `core/Sverify/Core/CaseTable.lean` for
the reference, `python/src/sverify/_case_tables.py` for the writers' guards and
the inferred precondition) and are the intersection over the supported
versions. A mapping that changes a string's length is outside the table.

The alphabets are per function. `UPPER` raises on a string that holds one of
the 157 scalar values DuckDB, Polars and Spark map differently
(`characterization/case-differences.json`); `LOWER` on one of 56, or on every
`Σ` (U+03A3), 57 in all. Every other scalar has the one scalar the three give,
1,423 for `UPPER` and 1,431 for `LOWER`, and a scalar none maps stays as it is.
`LOWER` raises on every `Σ` until the facts on its context (the final sigma
reads each engine's Cased and Case_Ignorable sets on both sides) exist; the
exact set is a later narrowing. No set is coarser than a scalar list: the
facts cover every scalar, and a raise stays small and guardable (D47, rule 4).
ASCII text is in neither set, so a column declared ASCII proves as under D43.

The precondition names the agreed alphabet. Two declared column facts state
it, one per function (`upper_agreed` and `lower_agreed` in the checker's
request, `AVal.upperAgreed` and `AVal.lowerAgreed`): the column is in that
function's agreed alphabet, none of its scalars in the function's raise set.
The request holds a list of facts per column, under the key `text`
(`"ascii"` and `"plain"` are facts in it). ASCII gives both
(`Text.upperRaises_of_isAscii`, `Text.lowerRaises_of_isAscii`). Python renders
the inferred precondition as one native regular expression class per engine
and checks it on the data.

`ILIKE`, `reverse`, `ascii`, `levenshtein` and the regular expressions keep
D43. Regex classes follow by the same method under this number once their facts
exist. `ILIKE` stays under D43 until its fold facts exist, one per engine: if
every engine folds both operands with its own `lower`, it moves under `LOWER`'s
set, on the pattern as well.

Spark's writer calls `collate(upper(collate(x, 'UNICODE')), 'UTF8_BINARY')`:
the plain function follows the JVM's default locale (`tr`, `az` and `lt` map
`i` and `I` otherwise) and the collated form does not. Snowflake's writer
refuses `UPPER` and `LOWER` of anything but a literal until its facts, kept
privately, show the table. The ICU bundled with pyspark 4.0 and 4.1 lacks 28 scalars per
direction that 4.2 and later map; every one is in the raise sets, so the guard holds on all
of them (`spark-case-collated`).

Why: real text is rarely ASCII, so D43's precondition bites, against D21's own
condition. The engines agree on almost every letter.

Recomputes sinks: no

### D44. `replace` with an empty pattern is the string unchanged

Decided 2026-11-17 (the maintainer, on the theory advisor's recommendation,
#1508).

`replace(s, '', r)` is `s`: an empty pattern matches nowhere. It is `NULL`
where `s` or `r` is `NULL`, as for any pattern. `Text.replace` changes for
this case only; a non-empty pattern is Rust's `str::replace` as before.

Why: the reference's value is one every engine gives natively or by a cheap
shim. DuckDB returns the string unchanged
([duckdb-replace-empty-pattern](../engines/duckdb/facts/duckdb-replace-empty-pattern.json)),
and so does a constant fold on Polars, whose own `replace_all` inserts the
replacement at every character boundary
([polars-string-natives](../engines/polars/facts/polars-string-natives.json)).
Both frontends take only constant patterns, so the empty pattern is known when
the plan is written, and the writers fold it. The core gains no option, and the
raise set stays the small guardable one. The Substrait YAML leaves the case
unspecified ([ST-17](../upstream/bugs/ST-17.json)).

### D45. `QUANTILE_DISC` picks a member of a class, as `MIN` and `MAX` do

Approved 2026-11-17 by the user, on the theory advisor's proposal (the ruling
on [#1512](https://github.com/AlexanderNenninger/substrait-lean/issues/1512)'s zero sign).

`QUANTILE_DISC` selects one of its values by comparison, as `MIN` and `MAX`
do. Where the selected value is a double whose class has more than one member
(a zero, a NaN), the reference allows the value `AggFn.apply` selects, any
member of the group in that class, or the class's canonical value
(`AggFn.Picks`, `AggFn.classPick`). `AggFn.apply` keeps its pick. A value of
any other kind is alone in its class, so nothing else changes
(`AggFn.Picks.eq`).

Why: before this decision the reference fixed `QUANTILE_DISC`'s member of a
class to the raw-least (`sortVals` breaks ties by codes), and DuckDB returns
`-0.0` or `+0.0` by row order and thread count, outside `Allowed`. D31 already
opens the class for `MIN` and `MAX`; this extends its rule to the remaining
order statistic. It widens no verdict: a quantile is neither order-free nor
sorting, so `Rel.detPlan` already answers false for a plan with one, and the
contract analysis bounds a double by its canonical code.

Amended 2026-11-17 (the theory advisor's rulings on D45's windows, entries 28
and 34; the user's approval is pending on the pull request): windows join.
A window's `MIN`, `MAX` and `QUANTILE_DISC` over a frame allow what
`AggFn.Picks` allows over the frame's values, in the frame's order
(`WinFn.Allowed`); every other window function keeps its value, and a
windowed `QUANTILE_CONT` keeps its pin. `Rel.Allowed`'s and
`Rel.OrderAllowed`'s window cases admit any such result (`windowRowsA`), and
`WinFn.AllowedP` no longer pins a window's `MIN` and `MAX`. Why: D31's text
never named a group, and DuckDB's `duckdb-minmax-zero-sign` contradicts the
pin. Where the class-picking functions' arguments hold no doubles, a window
gives `windowRows` alone (`windowRowsA_eq`), and every admitted result is
`windowRows` up to each window value's class (`windowRowsA_canon`).
`Rel.detPlan`'s window case gains the aggregate case's guard
(`WinFn.pickFixed`), so a plan with a windowed `MIN`, `MAX` or
`QUANTILE_DISC` over an argument that may be a double is no longer
certified deterministic at the exact level; it keeps the certificate at the
class level
([D48](#d48-a-result-is-determined-up-to-the-classes-its-observation-reads)).

### D46. An integer column's values lie in its declared width

Decided 2026-11-17 (theory advisor).

A value of an `i8`, `i16`, `i32` or `i64` column of the reference lies in its
type's range, -2^(w-1) to 2^(w-1)-1, by its type, as a DATE lies in 0001-9999
(D32). A source value outside it fails the read, named. A computed value
outside it is an overflow, as before (the Widths row of
[the reference semantics](reference-semantics.md)). The checker takes the
range as known (`ContractCheck.typeEnv`): a column read needs no inferred
precondition to fit its own width, and only a computed value can leave it.

The run checks each narrow integer column once, before any engine reads it
(`Report.check_inputs`). A physical integer type contained in the declared
one passes by its type. A wider one gets one range check over the read and
fails with a `PreconditionError` that names the column, the declared type,
the count and one value. It runs on `Report.run`, `run_sharded`, and an
incremental view's first load and each batch; a transform called on bound
tables is verified on the schemas the engine reports for them, so it declares
no type the data could exceed, and a view planned again after a schema change
(`_replan`) likewise.

Why: the docs state the width of results and said nothing of a source value
outside the declared width. D32 settled the same gap for dates, and D46 has
its shape. It adds no option, no raise on a computed value and no engine
name. The range enters the checker only after the run establishes it on the
data, so the check on the run lands before the checker change.

### D47. Raise, value or open where engines differ

Decided 2026-11-18 (theory advisor).

Where the tier-1 engines differ on an input, the reference answers by the
first rule that applies.

1. The engines' values compare equal on every engine: the reference allows
   any of them (D31, D36, D45).
2. The input is a zero divisor, gives a result outside its type's range, or
   lies outside the function's real domain: the reference raises (D37, D38,
   D39). The precondition that excludes it is a standard one on the operands:
   non-zero, bounded, in the domain. A domain is the real function's, read
   with one zero, so `power(x, y)` with a negative `x` and a non-integer `y`
   raises for `x = -∞` as for a finite `x`, where IEEE 754 answers `+∞`.
3. The function has a defined value there: the difference is an option
   (D34), and the reference takes a value every tier-1 engine gives natively
   or by a cheap shim. Of several, it takes the one the most engines give
   natively, then Substrait's, then IEEE 754's or the SQL standard's. An
   engine that cannot reach the value has its writer refuse the function.
4. No value is reachable on every tier-1 engine: the reference raises, when
   a precondition on the inputs excludes the case and rarely bites real
   queries (D21), and the frontends refuse the function otherwise. Such a
   raise narrows as engine facts arrive.

Until a case has its decision, the frontends refuse it under the reference,
and `semantics="<engine>"` lifts that engine's value from a fact.

Read by this rule: `x / 0.0` and `x / -0.0` (rule 2, with D39's option),
`power(-∞, y)` (rule 2, D21's example), `power(±1, ±∞)` (rule 3, D40),
`replace` with an empty pattern (rule 3, D44), `float_to_int` (rule 3, D42),
`QUANTILE_DISC` of doubles (rule 1, D45), non-ASCII case mapping (rule 4,
D43).

Why: D21 raised where an engine differs and D40 took an option where two
engines agree, and no text said which applies when. The raise set stays
small and guardable, and a value two engines compute alike stays a value.

### D48. A result is determined up to the classes its observation reads

Approved 2026-11-18 by the maintainer, on the theory advisor's proposal
(review C2).

A plan's result is determined when every result the reference allows is the
same up to row order and up to the member of each equivalence class of
[D31](#d31-double-arithmetic-is-exact-rounded-once) (`-0.0` and `0.0`;
every NaN). A place that only picks a member of a class leaves the result
determined: a `GROUP BY` or `DISTINCT` key over doubles, `MIN`, `MAX`,
`QUANTILE_DISC`, and their windowed forms
([D45](#d45-quantile_disc-picks-a-member-of-a-class-as-min-and-max-do)).
`Report.deterministic` reports this level, and refreshes and idempotent sink
epochs require it by default ([D10](#d10-determinism)): the default
observation reads one zero and one NaN, so no rerun it compares can differ at
a pick.

An observation that reads the members (`floats` and `zeros` both exact,
`Observation.reads_members`) asks for the exact level. There each class pick
is an open place: the refusal names it and the two ways out, a class-blind
observation or a plan without the pick.

Both levels are proved. The exact level is `Rel.detPlan`
(`check_deterministic_sound`): every allowed result is `Rel.eval`'s up to row
order. The class level is `Rel.detClass` (`check_class_determined_sound`):
every allowed result is `Rel.eval`'s up to row order and `Row.canon`. A plan
where an expression reads a picked value and can tell the members apart
(`atan2`, a cast to a string) is not determined at the class level, and the
report names the expression.

Tie order, tie picks and an unordered `FETCH` are open at both levels
([D24](#d24-tie-order-is-open-and-determinism-is-proved) unchanged).

`floats="plan"` reads one zero and one NaN whether or not the plan has a
float bound (`Observation.equal`). The refinement order (`coarser_than`),
which D18's check and the engines' rerun rows use, still compares `zeros` as
a component of its own: under `floats="plan"` or a tolerance it asks for more
than `Observation.equal` can see, which is sound.

Amends: D10 (the default requirement is the class level); D20 (the
consumer's observation `q_det` chooses the level); D24 (determinism is a
proved property at two levels); D31's correction (the `noDoubles` guards
belong to the exact level); D45's last sentence (the certificate is kept at
the class level and dropped at the exact level).

Why: a refresh of `SELECT region, MAX(price) … GROUP BY region` over a double
`price` was refused, though no observation a refresh uses by default can
tell the results apart. The step from an observation to a level is
`observation.py`'s until the bridge to `Relation.Equiv` is proved
([trusted base](trusted-base.md)).

### D49. A value known from one engine is provisional

Decided 2026-11-18 (theory advisor).

A function whose reference value is stated from DuckDB's facts alone is
marked "DuckDB-defined" in [the reference semantics](reference-semantics.md).
It runs on DuckDB only: the other engines' writers refuse it and name
[#271](https://github.com/AlexanderNenninger/substrait-lean/issues/271).
When a second tier-1 engine's facts arrive, D47 decides the value under a
D-number, and the mark goes. The rows marked are `round(x, d)`, the casts from
a string, `date_diff`, `lpad` and `rpad`; the owner of the table marks every
other row whose only support is a DuckDB fact.

A release states the count of DuckDB-defined functions.

Why: the reference belongs to no engine, and these rows said "as DuckDB
computes it" with no decision and no second engine's facts. The mark states
what is known, and the rule for new functions (Lean and DuckDB first) keeps
producing such rows.

### D50. The frontends lift `AND` and `OR` so a guard protects the next operand

Decided 2026-11-18, approved by the user.

`WHERE qty <> 0 AND total / qty > 1` reads as a guard, and SQL users write
it so. The SQL and Ibis frontends lift `p AND q` so that a raising operation in
`q` runs only where `p` is not FALSE, and `OR` likewise where `p` is not TRUE.
The core stays eager (D19), and `semantics="duckdb"` keeps DuckDB's eager
reading, where DuckDB raises.

The lift is the call `sverify_and` (`sverify_or`) over the operands, which the
parser reads as nested `CASE` (`Expr.andLift`, `Frontend/Guard.lean`):
`T_k = CASE WHEN p_k IS NOT FALSE THEN T_{k+1} ELSE 0`, ending in
`CASE WHEN p_1 AND … AND p_n THEN 1 ELSE NULL`, and the conjunction is
`T_1 = 1`. Its size is linear in the operands, and each operand is written
three times: twice in `p IS NOT FALSE` (`p IS NULL OR p`) and once in the
closing conjunction; a plain operand a fourth time, outside the chain. A lift
inside an operand is written three times a level. Operands that cannot raise
(`Expr.plain`, a syntactic check with no use of the analysis) stay outside; an
`AND` of plain operands stays the eager `AND`, and its plan does not change.

Proved (`Frontend/Guard.lean`, with the `OR` duals): on every row where the
eager `AND` returns, the lift returns the same (`Expr.andLift_refines`); where
an operand is FALSE and the operands before it do not raise, the lift is FALSE
whatever follows (`Expr.andLift_false`); an error in a reached operand still
surfaces (`Expr.andLift_error`); and the lift is TRUE, FALSE or NULL, so it can
be an operand (`Expr.andLift_boolVal`). The `andG` lemmas are the chain's case
lemmas. A constant subexpression that raises is outside the guard (D21,
`Rel.constIssues`): `x <> 0 AND 1 // 0 = 1` raises for the whole plan under the
lift as under the eager reading. The analysis refines the `THEN` branch by its condition and reads
`p IS NULL OR p` as a fact on a column (`x <> c`, `0 <= c < x`).

An engine runs the lifted plan on a recorded fact that its `CASE` evaluates the
taken branch alone; an engine or a shape without such a fact refuses it. The facts:
`duckdb-exec-short-circuit` (DuckDB runs it), `spark-exec-evaluation-order`
(Spark runs it, also with a subexpression twice in a branch) and
`polars-exec-when-eager` (Polars runs it, collected with common-subexpression
elimination off, `polars-exec-cse-hoist`). Snowflake follows its private facts.
Polars's masking excludes a branch under `group_by().agg` and `over()`; an
aggregate's `FILTER` and a window's argument are tested in
`tests/test_and_or_engines.py`.

Interim limits, until step D50-d (a gate for 1.0):

- Only the top three levels of a nest of `AND` and `OR` are lifted
  (`LIFT_LEVELS`, `plan_json.py`; a connective's level is one more than the lifted
  ones enclosing it). Below that the connective is the eager `AND` or `OR`: a
  guard there does not protect the next operand, so the guarded operation is
  reported as an inferred precondition, as before D50. The cap exists because a
  lift nested in a lift multiplies the size: with a guarded leaf, depth 3 of
  alternating connectives measured 29 times the eager plan's characters, and
  depth 4 took 5,171 s in the checker. Since the lift has the eager value
  wherever the eager reading returns (`Expr.andLift_refines`), a plan proved
  under the cap stays proved when D50-d lifts the lower levels.
- The analysis proves zero and null guards (`x <> c`, `0 <= c < x`). A range
  guard before a cast (`x BETWEEN a AND b AND CAST(x AS BIGINT) > 1`) and a
  pattern guard before a string cast run correctly on the engines, but are
  reported as inferred preconditions; step D50-e (before 1.0) adds a
  refinement through `p IS NOT FALSE` for the range guard. A pattern guard stays
  unproved.

Why: the eager reading made the commonest guard in SQL unprovable, and the
engines that short-circuit give the value the user meant.

The lift is the chain `Expr.andLift`, in place of the `Expr.guardBy` shape first
approved (2026-11-18); the plain operands are found by `Expr.plain`.

Recomputes sinks: no. The reference's values do not change: a plan that raises on no row
computes what it did, and a lifted guard only removes a raise.

### D53. A timestamp with the time zone UTC is an instant

Decided 2026-11-19 (theory advisor).

A timestamp with the time zone UTC is an instant. `Kind.timeTz` holds
microseconds since 1970-01-01 00:00 UTC, the value the naive kind holds. The
reference computes with an instant wherever no zone is read: comparison with
another instant, `IS [NOT] DISTINCT FROM`, ordering, `MIN`, `MAX`, `COUNT`,
`DISTINCT`, grouping, join keys, window keys, and `CASE`, `COALESCE` and
`NULLIF` among instants. Everything that reads a calendar field of an instant
is refused (opened for the Ibis frontend at UTC by [D69](#d69-a-calendar-function-of-a-utc-instant-in-ibis-reads-its-utc-wall-clock)) and names [#1725](https://github.com/AlexanderNenninger/substrait-lean/issues/1725):
arithmetic with intervals, the difference of two instants, `date_trunc`,
`extract`, a cast to a date or a string. A comparison of an instant with a
naive timestamp is refused. Zones other than UTC are refused. The conversion is
a function of the core that returns its argument; nothing else in `Rel.eval` and
`Rel.Allowed` changes.

Read in two steps. Step 1 read an instant column, computed with it and wrote it
back as an instant (Arrow `timestamp[us, tz=UTC]`, Delta `timestamp`). Step 2
adds the conversion between an instant and a naive timestamp at UTC
(`UnFn.atUtc`: `x AT TIME ZONE 'UTC'` in SQL, the cast between `timestamp('UTC')`
and `timestamp` in Ibis) and instant literals: a literal is an instant when its
text or Python value carries an explicit offset, which is folded to UTC
microseconds; it is the conversion of a timestamp literal, so it has the kind of
every other instant expression. A literal without an offset reads the session
zone and is refused; so are DuckDB's `CAST(tstz AS TIMESTAMP)`, `tstz::DATE` and
`CAST(ts AS TIMESTAMPTZ)`, and a comparison, `IN`, `COALESCE`, `CASE` or set
operation that mixes an instant with a naive timestamp, which DuckDB brings to
the session's zone. The Ibis frontend refuses a mix too, and an explicit Ibis
cast between the two kinds is the conversion.

No option and no profile entry: the operations above read no zone, so the
engines agree on them under every session zone
([duckdb-time-zones](../engines/duckdb/facts/duckdb-time-zones.json),
[polars-datetime-zone](../engines/polars/facts/polars-datetime-zone.json),
[spark-time-zones](../engines/spark/facts/spark-time-zones.json)). DuckDB and
Polars have a map for the instant, and a fact for each spelling of the conversion
([duckdb-instant-conversion](../engines/duckdb/facts/duckdb-instant-conversion.json),
[polars-instant-conversion](../engines/polars/facts/polars-instant-conversion.json));
Spark and Snowflake refuse it and name the issue.

Recomputes sinks: no

Why: a Delta `timestamp` is an instant, and read as the naive kind it would
return `timestamp_ntz` columns and let calendar functions run unstated, which a
later kind would change. A refusal lifted later is a minor change, a corrected
rule a major one. D53 gives a meaning to plans that had none, so no stored node
changes its meaning.

### D54. The lift refines the dialect

Decided 2026-11-19 (theory advisor, ruling 105; #1484).

Under `semantics="reference"`, a SQL text in dialect X lifts to a plan with
this property: wherever the reference gives a value, X running the same text
natively gives that value, up to the classes D47 leaves open and the float
bands of D52 and D53. Where the reference raises, X may give a value, NaN or
an infinity, and the inferred preconditions name those inputs. A construct that
cannot meet this is refused by the lift, with a hint that names spellings
that do. A construct whose two readings differ only on a named degenerate input
class may be a listed exception, shown in the report.

The text of a SQL query reads as DuckDB's under both semantics (`/`, `//`, NULL
order, `replace`); the semantics is what the functions do. The two profiles
differ in five fields. In two the reference raises where DuckDB gives NaN or
`-inf` (`domain_error`, `log_zero`): a raise is visible and the inferred
preconditions guard it. In three the reference gives another value:

| `Profile` field | reference | DuckDB | where | the lift |
|---|---|---|---|---|
| `float_to_int` | truncates | rounds, ties to even | `CAST(double AS integer)` | refuses, with a hint |
| `decimal_to_int` | truncates | rounds, ties away from zero | `CAST(decimal AS integer)` | refuses, with a hint |
| `corr_degenerate` | NULL | NaN | `corr` of one pair or a constant side | lists it |

R9 stays the reference's rule: the model's cast of a double or decimal truncates,
and the Ibis frontend's cast means that. DuckDB SQL's `CAST` is DuckDB's cast,
which rounds, so the SQL lift refuses it under the reference until #322 gives
the model a rounding cast (the user's choice on #1484, 2026-11-19). The hint
for a double names the spellings with one meaning under both semantics,
`CAST(round(x) AS BIGINT)`, `floor` and `ceil` (`round(x, 2)` is not one: it
leaves a fraction); the hint for a decimal points at #322 and names none. `corr` stays a listed exception: the
readings differ only on one pair or a constant side (ST-3), and refusing it
would refuse every `corr`. `Report.dialect_differences` shows it with the
construct, where it is, both readings, an example and the spellings.

L is a rule for frontends. It changes nothing in `Rel.eval`, `Rel.Allowed` or
`Profile.reference`, and the verdict gains no value: the list says what the
proof covers, and proved stays proved. A SQL query with `semantics="duckdb"`
and an Ibis transformation list nothing. `semantics="reference"` stays the
default for raw SQL ("verify two paths" and "portable everywhere" keep it).

Recomputes sinks: no

Why: a proof is about the plan the lift writes. A user reads it as a statement
about the SQL they wrote, so where the plan's value differs from the text's
the report says so. A refusal lifted later is a minor change, a changed value a
major one (D17), so the casts are refused before a release and `corr` is listed.

### D56. Decimal `+` and `-` check each operand at the result's scale

Decided 2026-11-19 (theory advisor, ruling 131; the user, #1484: "If DDB can't
run the behavior, we should disallow it").

Decimal `+` and `-` across scales bring each operand to the result type
`DECIMAL(p, s)` before they add. An operand whose rescaled value has more than
`p` digits raises an overflow, also where the exact result would fit. Only an
operand with `pᵢ + (s − sᵢ) > 38` can raise so, and the check is written for
those operands only: `Parse.decimalCall` wraps them in `UnFn.decimal 38 s`, the
checked rescale that `CASE`, `COALESCE` and `GREATEST` use. DuckDB casts both
operands to the result type (fact `duckdb-decimal-addsub-operand-cast`). The
raise is an overflow that a declared range guards: the inferred precondition is
`|a| < 10^(38 − s)`. Substrait leaves the operand's rescale open ([ST-18](../upstream/bugs/ST-18.json)).

`×` has no such cast: its result scale is `s₁ + s₂`.

Recomputes sinks: no

Why: DuckDB raises on a cancelling sum such as `DECIMAL(38,0) + DECIMAL(38,10)`
at `10^28`, so a plan the reference accepted there would return a value that
DuckDB cannot run. A raise the preconditions name is visible; a value the
engine does not give is not.

### D58. A timestamp's delta counts the unit boundaries crossed

Decided 2026-11-19 (theory advisor, ruling 137).

`a.delta(b, unit)` is `idx(a) - idx(b)`, an `int64`, where `idx(t)` is the
floor of `t`'s microseconds divided by the unit's microseconds, for
`microsecond`, `millisecond`, `second`, `minute`, `hour` and `day`. The floor
puts a value before 1970 where `date_trunc` puts it. Two timestamps 1 µs apart
across a boundary differ by 1; two almost a unit apart inside one unit differ
by 0. NULL in gives NULL out, and nothing raises beyond the timestamps' own
range (D32).

DuckDB's `date_diff(part, start, end)` counts the same way with its arguments
the other way round. The Ibis frontend writes the delta from existing
functions: each side floored with `date_bin` from the epoch, the difference
divided by the unit's microseconds, so Lean's model has no new function.

`week`, `month`, `quarter`, `year` and `nanosecond` are refused until facts pin
each engine's boundary (month, quarter and year are the next step).

The delta of dates and times follows the same rule and is refused until built,
and a time-zone-aware timestamp's delta is refused.

Recomputes sinks: no

Why: DuckDB is the default oracle ([`duckdb-timestamp-date-diff`](../engines/duckdb/facts/duckdb-timestamp-date-diff.json))
and Ibis documents the delta as the number of unit boundaries crossed
([`TimestampValue.delta`](https://ibis-project.org/reference/expression-timestamps#ibis.expr.types.temporal.TimestampValue.delta)). The refused units are those where engines place the
boundary differently.

### D55. A SQL cast of a double to an integer rounds half to even, as a composition

Decided 2026-11-19 (theory advisor, ruling 106; [#322](https://github.com/AlexanderNenninger/substrait-lean/issues/322)).
It replaces the dated amendment to D42's `rounding` row of 2026-11-18.

- `fp.round` accepts `rounding: TIE_TO_EVEN` at zero digits: IEEE 754's
  roundToIntegralTiesToEven on the magnitude (`onMag evenMag evenMag`,
  `core/Sverify/Core/Rounding.lean`). The default stays `TIE_AWAY_FROM_ZERO`, so no plan
  accepted before changes its result.
- The zero sign follows `round_zero_sign`. `-0.0` and `0.0` are one class, and the cast
  reads one zero (D31).
- NaN and `±∞` pass through the `round` and raise at the cast.
- `float_to_int` remains an engine's native-cast option that no evaluator reads. The lift
  reads the dialect's value to choose the composition.
- A SQL cast of a double to `BIGINT` means `ftoi (froundEven x)`, in Substrait
  `cast(round(x, rounding: TIE_TO_EVEN))`, and of a decimal the rescale to scale 0 then
  the cast, under D54. The reference's own `cast` and Ibis are unchanged (R9, truncation).
- The value comes from IEEE 754 and Substrait's own option name, from no engine's facts,
  so D49's mark does not apply.

Implemented by [#1959](https://github.com/AlexanderNenninger/substrait-lean/pull/1959).

Recomputes sinks: no

Why: a cast that means DuckDB's value is a round followed by a cast, and stating it as a
composition adds one option value and no new cast.

### D59. String to timestamp is strict and raises on a mismatch

Decided 2026-11-19 (theory advisor, ruling 137).

- The format is a literal. A column-valued format is refused.
- Directives: `%Y` (4 digits), `%m %d %H %M %S` (2 digits each), `%f` (6 digits), `%j`
  (3 digits), `%%`. Fixed width, ASCII digits, no sign, no padding variants.
- Literal text matches exactly. No whitespace is skipped, at the ends or inside. The
  whole string is consumed.
- A date is required, as `%Y %m %d` or as `%Y %j`. Time parts are optional and default
  to 0. No directive occurs twice; `%j` with `%m` or `%d` is refused.
- Any other directive, and any time-zone directive, is refused at verify time.
- Values: year 0001 to 9999, proleptic Gregorian validity (Feb 30 fails), hour 0 to 23,
  minute and second 0 to 59 (no second 60), `%j` 001 to 366 and valid for the year.
- A string outside this language raises a domain error, the same class as a failed
  string cast: one listed raise, guardable with a regular-expression match first. NULL
  in, NULL out.

A lowering runs the native parser alone only where facts show the engine accepts
exactly this language for the format. Otherwise the writer guards with a native
regular-expression match of the reference's language before the parse, and turns an
engine's NULL into the raise. The reference's raise set grows by this one entry. The
refusals (other directives, non-literal formats) are lifted later without a new
decision when facts allow.

Recomputes sinks: no

Why: the engines' parsers differ on width, whitespace and trailing text, and a strict
language with one guardable raise is a value every engine reaches natively or behind a
cheap native guard.

### D62. `%` of decimals is the truncated remainder at the common scale

Decided 2026-11-20 (theory advisor, ruling 181; [#1941](https://github.com/AlexanderNenninger/substrait-lean/issues/1941)).

`a % b` on decimals is the truncated remainder of the two values at scale
`max(s₁, s₂)`: it takes the dividend's sign, its type is
`DECIMAL(min(p₁ − s₁, p₂ − s₂) + max(s₁, s₂), max(s₁, s₂))`, a NULL operand gives
NULL, and a zero divisor raises (`Issue.divByZero`, as integer `%`). The core computes
on the unscaled integers at one common scale, as for `+`, `-` and `*`; the function has
a group of its own, `dec.mod`. An operand upscaled past 38 digits follows D56's check
where every tier-1 engine's fact shows D56's behaviour, and is refused otherwise.

Implemented by [#1951](https://github.com/AlexanderNenninger/substrait-lean/pull/1951).

Recomputes sinks: no

Why: it lifts a recorded refusal (`dec.div`, until #27) for `modulus`, with the type
rule of Substrait's YAML, whose borrow branch never applies here.

### D67. Opaque columns: a kind with no operations

Decided 2026-11-20 (theory advisor, ruling 187; [#1958](https://github.com/AlexanderNenninger/substrait-lean/issues/1958), [#1918](https://github.com/AlexanderNenninger/substrait-lean/issues/1918)).

A column of a type the frontend does not model is an opaque column: a kind,
`Kind.opaque`, and no new value. What the model holds for it is an injective image of
the engine's value. The kind checker refuses every use but carrying it: an opaque
argument to any function, measure or window function, a branch of `if_then` or
`coalesce`, a cast either way, a sort, grouping, partition or order key, and DISTINCT
and the set operations that compare rows. `IS NULL` and `IS NOT NULL` are admitted. A
column whose type contains an unmodelled type is opaque as a whole. There is no
literal and no cast. Each lowering writes a plain column reference, and the report gives
the column's declared type and nullability and nothing else. `Rel.eval` and
`Rel.Allowed` do not change.

Implemented by [#1977](https://github.com/AlexanderNenninger/substrait-lean/pull/1977).

Recomputes sinks: no

Why: a well-kinded plan reads nothing from an opaque column, so no result depends on
which image, and equality of two outputs in the model is equality of the engines'
values. The law is that a plan commutes with every injective renaming of that sort. It
lifts a refusal: sverify carries such a column and states nothing about its content.

### D69. A calendar function of a UTC instant in Ibis reads its UTC wall clock

Decided 2026-11-20 (theory advisor, ruling 193; [#1725](https://github.com/AlexanderNenninger/substrait-lean/issues/1725)).
It opens what D53 left as a later decision.

A function of a `timestamp('UTC')` expression whose Ibis result type is not an
instant (a date, a time of day, an integer part, a string of the supported
`strftime` directives, or the naive timestamp of `truncate` and `bucket`) means
that function of the instant's UTC wall clock: `f (atUtc false x)`. The Ibis
producer writes the conversion into the plan; the parser keeps refusing a
calendar function of an instant, so a plan states its zone or is refused. The
core, the options and the profiles are unchanged. Arithmetic with intervals, the
difference of two instants, a cast to a string, zones other than UTC and the SQL
spellings that follow DuckDB's session zone stay refused (D53, D54). Facts:
[duckdb-instant-conversion](../engines/duckdb/facts/duckdb-instant-conversion.json),
[polars-instant-conversion](../engines/polars/facts/polars-instant-conversion.json),
[duckdb-time-zones](../engines/duckdb/facts/duckdb-time-zones.json). Spark and
Snowflake refuse the conversion and name the issue.

Recomputes sinks: no. A refusal is lifted; no accepted plan changes its meaning.

Why: in Ibis the zone is in the column's type, so the plan can state it; in DuckDB SQL
it is in the session, which sverify never reads. With the conversion in the plan,
`t.ts.truncate('D')` is the same plan as `t.ts.cast('timestamp').truncate('D')`: one
meaning, proved once.

### D70. Engine versions: probed, in range, out of range

Decided 2026-11-20 (theory advisor, ruling 198 and its addendum, on [#2045](https://github.com/AlexanderNenninger/substrait-lean/issues/2045);
ruling 200 states the third paragraph's first sentence). Amends D14.

An engine profile states the versions its facts were probed at and one range around
them: the minor releases that hold a probed version, from the lowest probed patch up.
A profile whose engine has no such releases states its own range. The engine
package's dependency bound is that range.

A run that claims a guarantee on a probed version claims it in full. On an unprobed
version inside the range it warns, and the route records the version: the proof
stands, and the engine step assumes that this version computes what the probed one
does. Outside the range the run is refused until the probes are re-run.
`unverified=True` runs it anyway and claims nothing.

No guarantee of a verified run rests on an engine raising. An input the proof excludes
is excluded by a proved precondition or by a check whose verdict is a value the engine
returns. A version that raises on fewer inputs changes no verified run, and one that
raises on more stops a run with the engine's error.

At 1.0 a profile holds no row indexed by version. When a probed version changes a
value that a lowering, a shim or a check reads, the lowering is rewritten to read the
engine only where the versions in range agree, where one native expression does it.
Otherwise the profile moves to the new version and the range's floor moves with it. A
change on the error side supersedes its fact and keeps both versions.

The guard and the bounds are tracked in [#2052](https://github.com/AlexanderNenninger/substrait-lean/issues/2052).

Recomputes sinks: no

Why: D14 refused only another major, and a patch release changed a native value
(`list_contains([], NULL)` at DuckDB 2.0.1). An unprobed patch warns and an unprobed
minor is refused. No guarantee rests on an engine raising, so a version that raises on
fewer inputs changes no verified run.
