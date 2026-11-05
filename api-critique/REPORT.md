# sverify's public API, as a newcomer meets it

An outside view of sverify 0.5.0 (main at b87a8963, a day before the release),
from a data scientist and a data engineer who know Ibis, SQL, dbt and Polars,
and nothing of Lean or Substrait. I worked only from the README, `docs/`, the
notebooks, docstrings and `help()`, and from what `sverify` exports.

The eight tasks are scripts in [`tasks/`](tasks/), and [`LOG.md`](LOG.md) has
the raw notes in the order they happened, with every message quoted in full.

| Task | Script | Attempts | Outcome |
|---|---|---|---|
| Double-charge rule (self-join) | `t1_double_charge.py` | 4 | proved and refreshed on both engines |
| Sessionization (LAG, running sum) | `t2_sessionize.py` | 4 | proved as a transform; `session_no >= 1` not provable |
| Delta rollup with a refresh | `t3_delta_rollup.py` | 1 | worked first time |
| dbt-style SQL model | `t4_sql_model.py`, `t4b_…` | 4 | blocked by one `RANK()`; a key lost through a join |
| Contracts on doubles, tolerances | `t5_float_contracts.py` | 4 | worked once I left the report and read the guide |
| Refusals, inferred preconditions | `t6_refusals.py`, `t6b_…` | 5 | worked; messages long and partly wrong |
| DuckDB and Polars | `t7_engines.py`, `t7b_…` | 3 | ran; `//` means two things |
| `to_substrait()` | `t8_substrait.py` | 2 | worked for integers; a filter on a double is refused |

On timing: I am an agent, and my wall clock (about 20 minutes from install to
the last task, reading included) says little about a person's. The better
measures of cost are the attempts column and the moments in the log where a
message or a doc sent me the wrong way or nowhere. A person would spend most
of their first hour on the findings in section 1.

Each finding has a cost (high: blocks or misleads in the first hour; medium:
costs minutes and trust; low: polish), a proposal, and whether the proposal
breaks the API.

## 1. Error and report messages

The messages decide the first hour more than anything else. Some are
excellent (1.9). Many speak in the checker's terms, repeat themselves, or give
advice that cannot be followed.

### 1.1 Reports show expressions the user never wrote (high)

`(price - cost) * 100 // price` with no `requires` (task 6) produced ten
`may fail: overflow` entries, eight of them about the reference's rewrite of
the division:

```
may fail: overflow: ((((price - cost) * 100) + 1) // price) - 1
  hint: no single bound rules it out; for example, state `(_.price >= -4 * 10**16)`, `(_.price < 4 * 10**16)`, ...
may fail: overflow: (((price - cost) * 100) - 1) // price
  hint: ...
```

Elsewhere the report names columns by position or internal function:

- `may fail: overflow: ($1 - $3)` (task 2, `ts - lag(ts)`)
- `assumes: $2 may overflow to ±inf on finite inputs` (task 4, `sum(amount)`)
- `cast out of range: TO_DECIMAL_2(amount)`, `DECIMAL_10_2(TO_DECIMAL_2(amount))` (task 4)
- `inferred from \`ts + 300000000\`` for `ts + ibis.interval(minutes=5)` (task 1)
- `((_.dup_ts - _.first_ts) <= <scalar[interval('s')]>)` (task 1)

Proposal: map every issue back to the user's expression before printing. One
issue per user expression and kind ("`(price - cost) * 100 // price` may
overflow"), with the internal sub-expressions folded into it. Print intervals
as the user wrote them (`interval(minutes=5)`), and where no label exists,
print the output column name (`sum(amount)`, `revenue`) and never `$n`. Not
breaking.

### 1.2 Advice that cannot be followed (high)

Hints that are wrong cost more than no hint: the user follows them, fails, and
stops trusting the rest.

| Message (verbatim) | Why it fails | Better |
|---|---|---|
| `unique(dup_txn) … add sv.unique('dup_txn') on the input it comes from to requires` (task 1) | the input has no `dup_txn`; it's `txn_id` renamed, and a self-join can repeat it | "`dup_txn` comes from `payments.txn_id` through a join that can match a row more than once, so no key on `payments` makes it unique" |
| `unique(customer_id) … add sv.unique('customer_id') on the input it comes from` (task 4b) | already declared on both inputs | "the key `customer_id` of `customers` is lost through the join on `c.customer_id = p.customer_id`" (and see 2.3) |
| `sd_t … declare it NOT NULL in the schema (\`!int64\`) or add \`_.sd_t.notnull()\` to \`requires\`` (task 5) | `sd_t` is an output double, NULL for one-row groups (the counterexample shows it) | "`sd_t` is NULL for a group of one row (counterexample below); allow it, `(_.sd_t >= 0) \| _.sd_t.isnull()`, or filter `n >= 2`" |
| `hint: \`ts + 300000000\` is inside an AND or OR … e.g. \`ibis.cases((_.x != 0, 10 // _.x)) > 1\`` (tasks 1 and 6) | fires on a join condition and on `price - cost`, which the user didn't put in any `&`; the example is a division | fire only when the user's own `&`/`\|` holds both the guard and the guarded operation, and quote both |
| `overflow: ($1 - $3)`, `hint: no bound on an input column rules it out: it reads the value of a window function` (task 2) | bounding `ts` removed the issue | "bound `ts` in `requires` of `clicks` (both operands come from it)" |
| `note: … Declare \`unique(...)\` on the partition (or grouping) and order columns of the input` (task 4) | the window's input is a CTE; and with the tie broken by the key it still fails (2.2) | name the window and the columns it orders by, and say when no input key can reach them |
| `on_inferred='warn' or 'silent' assumes it` at the end of a refusal (task 6) | applies to one of eleven reasons; the overflows still fail with `warn` | say it only on the "needs:" line it applies to |

Proposal: every hint carries code the user can paste, and a test that pastes
it and checks the issue goes away (the suggestions already work this way:
"Sverify proves each suggestion before showing it"). A hint that can't be
proved that way is dropped. Not breaking.

### 1.3 The exception repeats the report, on one long line (medium)

`VerificationError`'s first line joins every reason with commas (about 1,600
characters in task 6), and the report under it repeats each one. The
`AND`/`OR` hint appears once per sub-expression. A notebook cell shows a wall.

Proposal: the first line is a count and a pointer:

```
VerificationError: 2 of 3 postconditions not proved, 1 precondition needed (e.report has the details)
  needs: (_.price != 0) on items, for `((price - cost) * 100) // price`
  not proved: (_.revenue >= 0): may be NULL (counterexample: price = NULL)
  may fail: `(price - cost) * 100 // price` may overflow: bound price and cost in requires
```

One line per finding, hints deduplicated, the full report in `e.report`. Not
breaking (message text only).

### 1.4 A report doesn't say whether it proved (medium)

`print(report)` (task 2) starts with `requires …` and never states the verdict.
In task 5 every `ensures` line said `proved`, yet `report.proved` was `False`,
and nothing printed said why: the tolerance `abs=1e-9` was below the plan's
bound of 2e-7, which the report doesn't show.

Proposal: a first line, `proved` or `NOT proved: <the reasons, counted>`, and
an `observes:` line that shows the plan's float bound beside the tolerance
(`floats within abs=1e-9, below the plan's bound 2.0e-7`). Not breaking.

### 1.5 Route lines speak Lean and private modules (medium)

Every refresh prints one of:

```
route on duckdb: reference: verified under the reference; the translation to duckdb is proved once: the DuckDB lowering (Lowering.lower_correct) and its writer [exact, tested]
route on polars: reference: verified under the reference; the translation to polars is sverify.polars_engine's shims to the reference, tested against Rel.eval [shim, tested]
```

"proved once" then `tested`; a Lean theorem name; a private module; and for a
mean, `[observed equivalent(rows='sequence', floats=within(abs=1.998402245904532e-07)), tested]`
with sixteen digits and `rows='sequence'` for a plan with no `ORDER BY`.

Proposal: `route on polars: shim (integer division rewritten to truncate); evidence tested`,
and `observed: doubles within 2.0e-7`. Keep the long form in `Route.reason`.
Not breaking.

### 1.6 Names in two spellings (low)

`FIRST, LAST, STRING_AGG, MODE, ARG_MIN or ARG_MAX` and in the next line
`first(), last(), group_concat(), mode(), argmin() or argmax()`;
`datetime.datetime(9999, 1, 1, 0, 0)` in `requires` after the hint said
`datetime(9999, 1, 1)`. Pick the user's language (SQL names for SQL, Ibis
names for Ibis) and Python's short reprs. Not breaking.

### 1.7 "Lean" as the subject (low)

"Lean only knows it is undetermined", "Lean worked out that…". A newcomer
reads Lean as a third party. Proposal: "Sverify" or "the checker" in messages
and docs. Not breaking.

### 1.8 Raw exceptions from inside `verify` (medium)

- `sv.approx(_.lo <= _.mean_t)` raises `TypeError: approx relaxes comparisons
  of a column with a number … it cannot relax LessEqual` from deep in
  `contracts.py`, at `verify` time (task 5). Proposal: check in `sv.approx(...)`
  itself and say "column against column; `sv.approx` takes a column against a
  number". Not breaking.
- A condition that Ibis can't type (`_.a - _.b <= ibis.interval(minutes=5)`)
  surfaces as an `IbisTypeError` traceback through six sverify frames (task 1).
  Proposal: wrap with the condition's text: "ensures condition 3 doesn't type
  check: …". Not breaking.
- A stale checker gives `ValueError: substrait-check --contract failed:
  error: divide: option division_type = [FLOOR] is not supported (the model
  does [TRUNCATE])` (log, "Checker binary"). `CheckerVersionError` exists and
  didn't fire. Proposal: compare the checker's hash with the one sverify
  expects and raise `CheckerVersionError("the checker is older than this
  sverify: rebuild it with `lake build substrait-check` or unset
  SVERIFY_CHECK")`. Not breaking.

### 1.9 What works well

Keep these as the model for the rest:

- `RouteError: refused on duckdb: agg.fsum's sum_order: mean_t is within
  abs=1.9984e-07 of the reference, and the postcondition asks within(rel=1e-09):
  state sv.equivalent(floats=sv.within(abs=2e-07)) or looser in ensures, or
  sv.equivalent(floats="plan") for the plan's own bound`: the number, the fix,
  the alternative.
- `healthy needs (_.margin_pct >= 0) (it may be FALSE on some rows) on 'm';
  margins only guarantees (_.revenue >= 0)`.
- `refused on duckdb: not verified: … (see report.unproved);
  run(..., unverified=True) runs it anyway`.
- `it divides by the constant 0, so every row it reaches raises: change the divisor`.
- Counterexamples: `readings(sensor, temp_c) = [('', 0.0)] gives … sd_t = None`.

## 2. Awkward: semantics a user trips over

### 2.1 One tie-sensitive window makes every postcondition undetermined (high)

A dbt mart with `rank() OVER (ORDER BY revenue DESC)` (task 4): every
`ensures` came back `NOT proved: Lean only knows it is undetermined: rows may
tie…`, including `revenue >= 0` and `n_orders >= 1`, which don't read the rank
and which "known about the output" lists as proved facts. Ranking columns are
common in marts; this blocks the whole contract.

Two parts:

- Undeterminedness should reach only the columns that read the window (and
  keys and row counts only where the window feeds a filter or join).
- `RANK()` and `DENSE_RANK()` give tied rows the same value, so their result
  doesn't depend on the order among ties. Only `ROW_NUMBER`, `LAG`, `LEAD`,
  `FIRST_VALUE` and the like do.

Proposal: scope `undetermined` per output column, and mark `RANK`,
`DENSE_RANK`, `PERCENT_RANK`, `CUME_DIST` and aggregate windows over `RANGE`
frames as tie-free. Not breaking (more plans prove).

### 2.2 Breaking the tie with a key isn't seen through a join (medium)

`ORDER BY revenue DESC, customer_id` after a `GROUP BY customer_id` and a join
on a unique `customer_id` still gave "undetermined" (task 4). Proposal: carry
keys through to the window's input (2.3 is part of this). Not breaking.

### 2.3 A key is lost when the join's other column is projected (medium)

`SELECT p.customer_id …` keeps `unique(customer_id)`; `SELECT c.customer_id …
JOIN … ON c.customer_id = p.customer_id` loses it (task 4b), and the message
asks for a key already declared. In dbt models the dimension's column is the
usual choice. Proposal: treat columns equated by an inner join's condition as
one for keys. Not breaking.

### 2.4 `//` means two things, and `%` a third (high)

On `x = -7` (task 7b):

| Input | `x // 2` | `x % 2` | `q*2 + r == x` |
|---|---|---|---|
| Ibis, `semantics="reference"` or `"duckdb"` | -4 (floor) | -1 (truncated) | no |
| SQL `sv.sql`/`sv.verify`, reference | -3 (truncated) | -1 | yes |
| Ibis, `semantics="polars"` | -4 | 1 | yes |

Ibis's `//` is `FloorDivide`, so sverify is faithful to Ibis, but a user
splitting milliseconds into seconds and a remainder gets an identity that
fails for negatives, and examples.md (example 4) says "Polars's integer
division floors, and the reference's truncates", which reads as "Ibis `//`
truncates". Proposal: a short section in the guide, "Integer division in Ibis
and SQL", with this table; and a report note when one plan uses Ibis `//` and
`%` on the same operands. Not breaking.

### 2.5 Every Arrow column is nullable (medium)

pyarrow tables, and so `StaticSource` and `con.put`, make every column
nullable. `sv.unique("txn_id")` doesn't imply NOT NULL, so `first_txn: any
integer or NULL` and `ensures _.first_txn.notnull()` fails until each key
column gets `_.x.notnull()` in `requires` (task 1). dbt users write
`unique` and `not_null` as two tests and will understand, but nothing in the
first examples says so. Proposal: the report says "`first_txn` may be NULL
because `payments.txn_id` is nullable in its schema: add `_.txn_id.notnull()`
to requires". Optionally `sv.key("txn_id")` for `unique` plus `notnull`.
Not breaking (`sv.key` is new).

### 2.6 Tolerances: stating nothing is looser than stating "exact" (high)

From task 5:

- No observation in `ensures`: runs on both engines, accepting doubles within
  the plan's proved bound (2e-7 here). `report.observation` prints
  `equivalent()`, which reads as exact.
- `sv.equivalent(floats=sv.within(abs=1e-9))`, meant as "be strict": the plan
  runs nowhere, DuckDB included.
- `sv.equivalent(floats="plan")` is the same as stating nothing, and appears
  only inside one `RouteError`; no doc mentions it.
- A tolerance below the bound is caught at `verify` for `abs=` (`proved=False`
  with no reason printed) and at `run` for `rel=` and `ulps=` (`proved=True`,
  then `RouteError`).
- A route class prints `rows='sequence'` for a plan with no `ORDER BY`, while
  the observation's default is `rows='multiset'`; `Observation`'s repr has
  `elements='sequence'` beside it.

Proposal: one model. The default observation is `floats="plan"` and
`report.observation` prints it so (`equivalent(floats=plan, ≤ 2.0e-7)`).
`floats="exact"` means bit-exact and says at verify time which engines can
give it. Every tolerance kind is checked against the bound at verify, with
the reason in the report (1.4). Document `floats="plan"` in example 5.
Breaking only in what `report.observation` prints.

### 2.7 `on_unproved="warn"` needs a second opt-in (medium)

A transform with `on_unproved="warn"` builds with a plain `UserWarning` whose
text is the whole report, and then `refresh()` refuses with `RouteError: …
run(..., unverified=True) runs it anyway` (task 6b). The user called
`refresh`, not `run`. Proposal: "warn" means the node runs unverified, with
`UnverifiedRunWarning` at each refresh; the message names the method called
(`refresh(unverified=True)`). Breaking in behaviour, for the better: today
"warn" is an error one step later.

### 2.8 A `RouteError` for a proof failure (low)

Running an unproved report raises `RouteError`, though no route failed.
Proposal: raise `VerificationError` (or a subclass `UnverifiedRunError` of
both) so `except VerificationError` catches every "not proved". Breaking for
code that catches `RouteError` there, unless it subclasses both.

### 2.9 Inferred `SUM` assumptions aren't errors, inferred bounds are (low)

0.5 makes inferred preconditions errors by default (`on_inferred="error"`), but
`assumes: SUM of amount_cents fits 64 bits in every group (inferred; checked
on the data while the job runs…)` passes silently (task 3), and so does
`temp_c may overflow to ±inf` (task 5, which names `temp_c` where the sum
overflows). Proposal: either fold these into `on_inferred` or name them
differently ("checked at run time" rather than "inferred"), and name the sum.
Not breaking if renamed; breaking if folded in.

## 3. Awkward: names and vocabulary

### 3.1 Route, class, profile, semantics, observation (high for reading the output)

A newcomer meets five words for "what the result means where":

| Word | Where | What it is | Does it land? |
|---|---|---|---|
| semantics | `semantics="duckdb"` | which engine's behaviour the proof assumes | yes, after example 7 |
| profile | `Profile.duckdb` in route lines | the same thing, by its Lean name | no: a second name for semantics |
| route | `route="auto"`, `native`/`reference`/`transfer`/`recheck` | how the proof reaches an engine | partly: `reference` is also a semantics |
| class | `exact`/`observed`/`shim`/`refused`, `Route.cls` | what you can rely on | yes, the most useful of the five; `None` seen in task 7 |
| observation | `sv.equivalent(...)`, `report.observation` | what counts as the same result | no: "observation" reads as "a data point" |

Proposals:

- Print "semantics" everywhere, never "profile": `verified under semantics="duckdb"`.
  Keep `Profile` for the Lean and characterization docs. Not breaking.
- Rename the route `reference` to `translated` (the translation carries the
  reference's choices). Breaking for `route="reference"`; keep it as an alias
  for one release.
- Lead with the class, not the route kind, in every printed line and in
  `Route.__str__`: `polars: shim, proved`. Not breaking.
- Call the concept "equivalence" in docs and attributes:
  `report.equivalence` beside `report.observation` (deprecated later). The
  function is already `sv.equivalent`. Breaking only after the deprecation.
- `Route.cls` is never `None`: the `LAG` over a key in task 7 should say
  `exact`. Bug fix, not breaking.

### 3.2 `engine=` means two things (medium)

`transform(engine=)` is where checks on data run; `refresh(engine=)` and
`run(con, engine)` are where the plan runs. Proposal: rename the transform's
to `check_engine=` (keep `engine=` deprecated for a release). Breaking after
deprecation.

### 3.3 Pairs of names for one idea (low)

| Here | There | Proposal |
|---|---|---|
| `transform(check_requires=)` | `Report.run(check_inputs=)` | `check_requires=` on both |
| `Report.run(deterministic=)` | `engines.to_sql(tie_free=)` | `deterministic=` on both |
| `Report.run(engine=None)`: the connection's | `Node.refresh(engine="duckdb")` | both default to the connection's or DuckDB, the same way |
| `sv.verify(transform, …)` | takes an expression or SQL | rename the parameter `query` (positional-only, so not breaking) |
| `Report.needs_text()`, `needs_lines()` (methods) | `needed`, `unproved`, `stated` (attributes) | properties throughout |
| `DeltaSource.contract()` (method) | `Contract` docstring: "`DeltaSource.contract` … read it back" | a property, or fix the docstring |

Breaking for the renamed keyword arguments; offer the old ones with a
`DeprecationWarning` for a release.

### 3.4 Refresh reports are named after the sink (low)

The rollup's report is headed `daily:` (the sink's directory) and the stored
contract's `view` is `'daily'`, where the transform is `daily_revenue` (task 3).
Proposal: `daily_revenue → daily:`. Not breaking.

### 3.5 "Δ" in summaries (low)

`payments@v0→v1, Δ trusted (change feed)` for a `StaticSource.apply` (task 1).
Proposal: `changes from payments v0→v1 (applied in memory)`. Not breaking.

## 4. Missing

What I reached for and didn't find:

| What | Why | Proposal | Breaking |
|---|---|---|---|
| `sverify.__version__` | first thing in a bug report | add it | no |
| Conditions back from a refusal | `e.report.needed` is `{'items': ['(_.price != 0)']}`, strings that need `eval` | `report.needed_conditions` as Ibis deferreds or SQL strings, by the language of the transform, ready for `requires=` | no |
| `Node.to_substrait()` and on the decorated transform | pipelines hold nodes; only `Report` exports | delegate to the node's report | no |
| "Where can this run?" in one call | I looped engines and caught three exception types | `report.routes_for(("duckdb", "polars"))` returning each engine's class or refusal, without running | no |
| Rows behind a `PreconditionError` | the exception has no attributes; a job can't quarantine and go on | `e.source`, `e.condition`, `e.rows` (a small Arrow table), and `refresh(on_violation="quarantine", quarantine=DeltaSink(...))` later | no |
| Proved NOT NULL in the sink | the guide says "proved guarantees become NOT NULL columns"; `not_null=[]` and nullable Delta columns though the report proved `n_orders ≥ 1` | write every column the report knows non-NULL as NOT NULL, or say in the guide that only stated `ensures` reach the table | no |
| A short way to state a key | `sv.unique("id")` plus `_.id.notnull()` for every Arrow key | `sv.key("id")` | no |
| Window sums' facts | `session_no` (a running sum of 0/1 over a frame holding the current row) is `≥ 0 or NULL`, and nothing says the checker doesn't track more | a report note: "window SUMs are tracked as ≥ 0 or NULL" | no |
| `isin` as a range | `new_session.isin([0, 1])` not proved while the report knows it is in [0, 1] (task 2) | read `isin` of integers as their range | no |
| A float filter that exports | `t.filter(t.w > 1.0)` is refused by `to_substrait()` (ST-4) | a shim for ordering comparisons of doubles (`is_nan(x) OR …`), as for equality | no |

## 5. Obsolete or redundant after 0.5

### 5.1 Five knobs for "not proved"

`on_unproved=`, `on_inferred=`, `infer=`, `strict=` and `unverified=`. `infer=False`,
`infer=False, on_inferred="silent"` and `strict=True` gave the same error in
task 6.

Proposal:

- Remove `strict=` (deprecated since before 0.5: "Deprecated alias of `infer`,
  with the opposite polarity"). Breaking; it already warns.
- Fold `infer=False` into `on_inferred="off"`: one parameter for inferred
  preconditions with four values, `"error"` (default), `"warn"`, `"silent"`,
  `"off"`. Breaking; keep `infer=` deprecated for a release.
- Keep `on_unproved=` for postconditions and `unverified=` on `run`/`refresh`,
  and make `on_unproved="warn"` imply `unverified=True` for that node's
  refreshes (2.7).

### 5.2 Other leftovers

- `sv.references(*legacy)`: the positional form is deprecated; remove it.
  Breaking; it warns today.
- `sverify.testing.Connection.datafusion`: deprecated; remove it. Breaking.
- `sv.equivalent(floats="plan")` and an absent observation are the same (2.6);
  document one and make the other its spelling.
- `node.plan` (a Substrait JSON string with sverify's private extension URNs)
  beside `report.to_substrait()` (portable). Rename `node.plan` to
  `node.internal_plan`, or document that it is not portable and point at
  `to_substrait()`. Breaking if renamed.
- `to_sql(json.loads(big.plan), SNOWFLAKE)`: `plan` is a string the user must
  parse to hand back to sverify. Accept the string. Not breaking.

### 5.3 The top-level namespace

`dir(sverify)` lists 31 names, 14 of them submodules (`sv.sverify`,
`sv.engine`, `sv.incremental`, `sv.plan_json`, `sv.observation`, …), against
18 in `__all__`. Tab completion shows all 31. `Report` has 46 public
attributes and is exported with its ~25-field constructor.

Proposal: import submodules under private names in `__init__`, so `dir(sv)`
matches `__all__`. Drop `Report` from `__all__` (users get it from
`verify`); keep it importable for type hints. Not breaking for documented use.

### 5.4 Exceptions in four places

`RouteError` is in `sverify.routes` and `sverify.errors` (examples.md imports
the first); `Unsupported` is `sverify.plan_json.Unsupported` (from `verify`
on unsupported SQL) and `sverify.engines.Unsupported` (from `run`), neither in
`sverify.errors`; `approx` raises `TypeError`; a stale checker `ValueError`.

Proposal: every exception sverify raises on purpose lives in
`sverify.errors` and subclasses one `SverifyError`; `Unsupported` becomes one
class there. Docs import from `sverify.errors` only. Not breaking if the old
names stay as aliases.

## 6. Docs: gaps and wrong statements

| Where | Statement | Problem | Fix |
|---|---|---|---|
| README, "Eight [examples]" | | examples.md has ten | "Ten" |
| README, pytest section | `assert_engines_agree(node, data)  # DuckDB, Polars and DataFusion agree` | DataFusion is paused (tier table) and not installed by default | "every installed engine" |
| guide, Delta Lake | "The proved guarantees become NOT NULL columns and CHECK constraints" | only stated `ensures` do; proved non-NULL columns stay nullable (task 3) | fix the code or the sentence (section 4) |
| guide, Contracts | "the report suggests [`sv.approx`] when an exact claim misses only by rounding" | `mean_t >= -90` with a bounded input got no suggestion (task 5) | fix the suggestion, or say it needs `sv.max_rows` first |
| examples.md 4 | "Polars's integer division floors, and the reference's truncates" | Ibis `//` floors under the reference (2.4) | say which operator; add the table |
| examples.md 6, 7, 9 | `from sverify.routes import RouteError` | every other error comes from `sverify.errors`, which has it | import from `sverify.errors` |
| `Contract` docstring | "`DeltaSource.contract` … read it back" | it's a method | `contract()` |
| nowhere | `sv.equivalent(floats="plan")` | only in a `RouteError` | document in example 5 |
| nowhere | `report.run` refuses an unproved report | example 2 shows only proved runs | one line in example 2 |
| README tier table | Polars is Tier 2 | `MIN` and `MAX` of doubles are refused on Polars ("see #271"), which a data scientist meets in their first `aggregate` | a line under the table: what Polars refuses today, linked to `_support.py`'s list or a docs table |
| README install | "elsewhere pip builds from the sdist, which needs elan" | `pip install .` from a checkout starts a full `lake build` of every generated module (load 25 on a 10-core laptop in a minute) | say so, with `SVERIFY_PREBUILT_CHECK` for contributors |
| guide, Using sverify | "`report.run(con)` … checks the report's preconditions" | fine; but `check_inputs=False` vs the transform's `check_requires=False` (3.3) | one name |

## 7. The five changes that would most improve the first hour

1. Reports and errors in the user's terms: no `$n`, no internal rewrites, one
   line per user expression, a verdict on the first line, the exception's text
   a short summary with `e.report` for the rest (1.1, 1.3, 1.4, 1.5).
2. No wrong advice: every hint carries code that sverify has checked makes
   the issue go away, or no hint (1.2). This is the trust repair.
3. Scope tie-sensitivity to the columns that read the window, and treat
   `RANK`/`DENSE_RANK` as tie-free (2.1), so a dbt mart with a rank column can
   have a contract.
4. One float model: the plan's bound is the default and the report prints
   it; every tolerance is checked at verify; `floats="plan"` documented (2.6).
5. Fewer knobs for "not proved": remove `strict=`, fold `infer=` into
   `on_inferred=`, and make `on_unproved="warn"` mean the node runs (5.1, 2.7).

The Delta and refresh path (task 3) already gives a newcomer the experience
the rest should: it worked first time, and every line of its report meant
something.
