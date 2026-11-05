# Session log

The raw notes behind REPORT.md, in the order they happened, on 2026-11-05,
between 08:40 and 09:00. The attempts count is the better measure of cost.

## Setup

- `pip install -e python[polars,delta,iceberg]` from main at b87a8963 (0.5.0
  is not on PyPI yet; the release PR #680 is open). A plain (non-editable)
  install from the checkout starts a full `lake build` of every generated
  module: load went to 25 on the laptop within a minute. The README says
  pip builds from the sdist with elan only "elsewhere", so a user installing
  from a git checkout gets no warning that this takes minutes and many GB.
- `sverify.__version__` does not exist. `importlib.metadata.version("sverify")`
  works.
- `dir(sv)` lists 31 names, 14 of them submodules (`sv.sverify`, `sv.engine`,
  `sv.incremental`, `sv.observation`, `sv.plan_json`, …). `sv.__all__` has 18.
  Tab completion shows both.

## Reading

- README says "Eight examples"; examples.md says "Ten short examples".
- The examples import `RouteError` from `sverify.routes`; every other error
  comes from `sverify.errors` (which also has `RouteError`).
- Routes (`native`, `reference`, `transfer`, `recheck`) and classes (`exact`,
  `observed`, `shim`, `refused`) are two vocabularies printed side by side:
  `reference: verified under the reference; … [shim, proved]`. The route
  called `reference` and the semantics called `reference` are different
  things with one name.
- `@sv.transform` has `infer=`, `on_inferred=`, `strict=`, `check_requires=`,
  `engine=`, `on_unproved=`, `semantics=`. `strict` is in no doc I read.
- `sv.verify` takes SQL with `tables=`, Ibis without; `semantics` defaults to
  `None` there and to `"reference"` on `transform`.
- `to_sql(json.loads(big.plan), SNOWFLAKE)`: `Node.plan` is a JSON string that
  the user must parse to hand back to sverify.
- README's pytest section says `assert_engines_agree` checks "DuckDB, Polars
  and DataFusion", while the tier table says DataFusion work is paused.

## Task 1: double charges (4 attempts)

1. Self-join with `ensures=[first_txn < dup_txn, unique("dup_txn")]`. Refused,
   correctly for the first claim (my mistake). Messages:
   - `inferred from \`ts + 300000000\``: I wrote `ibis.interval(minutes=5)`.
     The interval shows as raw microseconds.
   - The AND/OR hint fires on a join condition and suggests
     `ibis.cases((_.x != 0, 10 // _.x)) > 1`, a division example, for a
     timestamp addition. Noise.
   - `unique(dup_txn) … add sv.unique('dup_txn') on the input it comes from
     to requires`: the input has no column `dup_txn` (it is `txn_id`
     renamed), and a self-join cannot keep it unique anyway. Wrong advice.
   - The exception text is one 600-character line that lists every reason,
     then the report repeats each one.
2. Every pyarrow column is nullable, so `first_txn: any integer or NULL` even
   with `sv.unique("txn_id")`. A dbt user expects `unique` and `not_null` as
   separate tests, but nothing tells them NOT NULL must be stated for every
   key column of an Arrow table.
3. `_.dup_ts - _.first_ts <= ibis.interval(minutes=5)` raised a raw
   `IbisTypeError` traceback from deep in `contracts.py` (Ibis's own typing:
   seconds vs minutes). Not sverify's fault, but no wrapping that names the
   condition.
4. Proved. The report prints `((_.dup_ts - _.first_ts) <= <scalar[interval('s')]>)`
   and `datetime.datetime(9999, 1, 1, 0, 0)` where the suggestion said
   `datetime(9999, 1, 1)`.
5. The refresh report: `route on duckdb: reference: verified under the
   reference; the translation to duckdb is proved once: the DuckDB lowering
   (Lowering.lower_correct) and its writer [exact, tested]`. "proved once" and
   then `tested`; Lean theorem names in a user-facing line. On Polars:
   `sverify.polars_engine's shims to the reference, tested against Rel.eval
   [exact, tested]`: a private module name, and "shims" with class `exact`
   while examples.md shows `[shim, proved]` for Polars.
6. `Δ trusted (change feed)` for a `StaticSource.apply`. "Δ" is jargon.

## Task 2: sessionization (4 attempts)

1. LAG plus a running `SUM` per user. `sv.verify` returns a report whose
   `print` never says "not proved" at the top; I had to print `r.proved`.
2. `may fail: overflow: ($1 - $3)`: column positions, not names (`ts - lag(ts)`).
   Its hint, "no bound on an input column rules it out: it reads the value of
   a window function", is wrong: bounding `ts` to 1900–2200 removed the issue.
3. `known about the output: new_session: an integer in [0, 1]`, yet
   `_.new_session.isin([0, 1])` is "NOT proved: it may be FALSE". Restated as
   `>= 0` and `<= 1`, both proved.
4. `session_no >= 1` (a running sum over a frame holding the current row, whose
   first row is 1) is unprovable, with no counterexample and no hint. Fine as a
   limitation; the report could say that window sums are tracked as
   "≥ 0 or NULL" only.
5. `Report.needs_text` is a method, `needs_lines` too, beside `needed`,
   `stated`, `unproved`, `unchecked`, `errors`, `warnings`: I printed a bound
   method by mistake. Seven overlapping views of "what's wrong".
6. `r.run(con)` on the unproved report: `RouteError: refused on duckdb: not
   verified: ensures (_.session_no >= 1) is not proved … (see report.unproved);
   run(..., unverified=True) runs it anyway`. Actionable. But it is a
   `RouteError`, though nothing about a route failed: it is a verification
   failure.
7. The transform version proved `unique(user_id, session_no)`. Refresh on
   Polars printed `[shim, tested]` this time (task 1 printed `[exact, tested]`
   for Polars); the class depends on the plan, which nothing explains.
8. `node.status`: `recomputed (not incrementally maintainable (left join,
   fetch or window); no touched groups: the aggregate's input has no delta
   rules (not incrementally maintainable (left join, fetch or window)))`. The
   same parenthesis twice, nested, and it doesn't say which of the three it
   met (a window).

## Task 3: Delta rollup with a refresh (first try)

1. Worked first time: Delta source with CDF, `group_by.aggregate`,
   `DeltaSink`, refresh after an append and a delete, a bad batch refused.
   This is the strongest part of the API.
2. `assumes: SUM of amount_cents fits 64 bits in every group (inferred;
   checked on the data while the job runs, which raises if it does not)`.
   0.5 makes inferred preconditions errors by default (`on_inferred="error"`),
   but this inferred assumption passes silently. Two policies for one idea.
3. The hint proposes `sv.max_rows(922_337_203_685)`: correct, but a user
   wants "add `sv.max_rows(n)` for any n up to 9.2e11".
4. The refresh report is headed `daily:` (the sink's directory name), not
   `daily_revenue` (the transform). The contract's `view` is `'daily'` too.
5. The sink's Delta schema has every column `nullable=True`, and
   `DeltaSource(...).contract` says `not_null=[]`, though the report knows
   `region: a string` and `n_orders: an integer ≥ 1` (never NULL). The guide
   says "The proved guarantees become NOT NULL columns and CHECK
   constraints". Only stated `ensures` reach the table; facts the checker
   found don't.
6. `DeltaSource.contract` is a method; `Contract`'s docstring writes it as an
   attribute (`DeltaSource.contract … read it back`). I printed a bound
   method again.
7. `refused batch: 1 inserted row(s) of orders violate (_.amount_cents >= 0)`.
   Clear, but it shows neither the row nor the source version, and doesn't say
   that nothing was written and the next refresh retries.

## Task 4: a dbt-style SQL model (4 attempts)

1. A CTE, a `GROUP BY`, a join and `rank OVER (ORDER BY revenue DESC)`,
   with the dbt tests as the contract. Every postcondition came back
   `NOT proved: Lean only knows it is undetermined: rows may tie in the ORDER
   BY of a window …`, including `revenue >= 0` and `n_orders >= 1`, which
   don't read the rank, while "known about the output" lists
   `revenue: a double ≥ 0.0` and `n_orders: an integer ≥ 1`. One window
   column makes the whole contract unprovable.
2. `RANK` gives tied rows the same rank, so its result does not depend on
   the order of ties. Treating it like `ROW_NUMBER` is too strict.
3. Breaking the tie with the key (`ORDER BY revenue DESC, customer_id`) still
   gave "undetermined": the checker doesn't see that `customer_id` is unique
   after the aggregate and the join. The note's advice, "Declare `unique(...)`
   on the partition (or grouping) and order columns of the input", can't be
   followed: the window's input is a CTE, not an input table.
4. Without the rank: `unique(customer_id)` "NOT proved: the preconditions do
   not make it a key: add sv.unique('customer_id') on the input it comes from
   to requires". I had declared exactly that on both inputs. The gap (task
   4b): `SELECT c.customer_id … JOIN customers c ON c.customer_id =
   p.customer_id` loses the key; `SELECT p.customer_id` keeps it. The two
   columns are equal on every output row.
5. `assumes: $2 may overflow to ±inf on finite inputs`: column positions
   again (`sum(amount)` once the rank is gone, so the label exists).
6. The note lists functions twice in two spellings: `FIRST, LAST,
   STRING_AGG, MODE, ARG_MIN or ARG_MAX` and `first, last,
   group_concat, mode, argmin or argmax`.
7. "Lean only knows …", "Lean worked out …": a user who doesn't know Lean
   reads this as a third party. "Sverify" or "the checker" says the same.
8. Unsupported SQL: `Unsupported: QUALIFY is not supported yet`,
   `aggregate ANY_VALUE is not supported yet`. Clear. The exception class is
   `sverify.plan_json.Unsupported` (a `ValueError`), not in `sverify.errors`,
   and a second `Unsupported` exists in `sverify.engines`.
9. `amount::DECIMAL(10,2)`: `may fail: cast out of range: TO_DECIMAL_2(amount)`
   and `overflow: DECIMAL_10_2(TO_DECIMAL_2(amount))`: internal function
   names, and "the inference does not cover this kind of cast": no way out
   offered (a bound on `amount` would do).
10. `amount / 0`: "it divides by the constant 0, so every row it reaches
    raises: change the divisor". Good.

## Task 5: contracts on doubles, with tolerances (4 attempts)

1. Per-sensor mean, std, min, max with `temp_c` in [-90, 60]. `mean_t >= -90`
   and `lo <= mean_t <= hi` are "NOT proved: it may be FALSE", with no hint.
   examples.md and the guide say the report suggests `sv.approx` and a row cap
   when a claim misses by rounding; here it suggested nothing, and
   "known about the output" says `mean_t: any double`. The fix (add
   `sv.max_rows`, wrap in `sv.approx`) came from the guide, not the report.
2. `sd_t >= 0`: "it may be NULL on some rows, where sd_t is NULL: declare it
   NOT NULL in the schema (`!int64`) or add `_.sd_t.notnull` to
   `requires`". `sd_t` is an output column, a double, and NULL for a group of
   one row (the counterexample shows exactly that, which is great). The
   advice can't be followed; "allow NULL: `(_.sd_t >= 0) | _.sd_t.isnull`"
   would be the fix.
3. `sv.approx(_.lo <= _.mean_t)` raised a bare `TypeError` traceback from
   inside `sv.verify`: "approx relaxes comparisons of a column with a number,
   combined with AND and OR; it cannot relax LessEqual". Fine text, wrong
   time: `sv.approx(...)` could check its argument when called, and say
   "column against column".
4. `assumes: temp_c may overflow to ±inf on finite inputs`: `temp_c` is in
   [-90, 60]; the sum may overflow. Names the wrong thing.
5. Attempt 2: every `ensures` line says `proved`, yet `rep2.proved` is False.
   Nothing in the printed report says why. (The tolerance `abs=1e-9` is below
   the plan's bound, 2e-7, which the report doesn't print.)
6. `ensures (_.sd_t >= 0) | _.sd_t.isnull: proved; depends on floats, which
   the observation ignores`. I can't tell whether that is a warning.
7. (Stale checker only: `rep2.epsilon` said `'proved': {'abs': False}`. With
   the current checker it says `True`; not a finding.)
8. `within(rel=1e-9)` and `within(ulps=4)`: `proved=True` at verify, then
   `RouteError: refused on duckdb` at run. `within(abs=1e-9)` was
   `proved=False` at verify. Too tight a tolerance is caught at two
   different times depending on its kind.
9. The `RouteError` is the best message I met: it names the plan's bound,
   the fix (`sv.within(abs=2e-07)` or looser) and the facts. It offers
   `sv.equivalent(floats="plan")`, which no doc I read mentions.
10. A tight tolerance refuses the run on DuckDB, the default engine. A user
    who adds `sv.equivalent(floats=sv.within(abs=1e-9))` to be strict gets a
    plan that runs nowhere; with no observation at all, it runs everywhere
    within 2e-7. Stating nothing is looser than stating `exact`.
11. `ensures=[]`: `report.observation` prints `equivalent` (exact), but both
    routes print `[observed equivalent(rows='sequence',
    floats=within(abs=1.998402245904532e-07)), tested]`. Three spellings of
    the default (`[]`, `floats="plan"`, `floats=within(abs=2e-7)`), and the
    route says `rows='sequence'` for a plan with no ORDER BY while the
    observation's default is `rows='multiset'`. `Observation`'s repr shows
    `elements='sequence'` beside `rows='multiset'`.
12. `Unsupported: min of doubles is not yet supported on Polars; DuckDB runs
    it (see #271)`. `MIN` of a double column refused on a Tier 2 engine is a
    surprise in the first hour, and the README tier table doesn't hint at it.
    It's raised as `Unsupported`, not `RouteError`.

## Task 6: refusals and inferred preconditions (5 attempts)

1. One line of user code, `(price - cost) * 100 // price`, with no
   `requires`, gave a `VerificationError` whose first line is ~1,600
   characters, and a report with 10 `may fail: overflow` entries, eight of
   them about expressions I never wrote:
   `((((price - cost) * 100) + 1) // price) - 1`,
   `(((price - cost) * 100) - 1) // price`, … These are the reference's
   rewrite of the division, leaking into the report. Each has its own hint,
   with bounds that differ (`2**62`, `4 * 10**16`).
2. The AND/OR hint fires twice, for `price - cost` and `(price - cost) * 100`,
   which aren't inside any `&` or `|` I wrote.
3. The hints propose negative lower bounds (`_.price >= -4 * 10**16`) for a
   price; the natural fix, `_.price > 0` with an upper bound, is not what the
   message suggests.
4. `e.report.needed` gave `{'items': ['(_.price != 0)']}`: strings, not
   conditions I can paste back into `requires` without `eval`. Only the
   division's precondition is "needed"; the overflow bounds are hints, in
   another field. `report.suggestions` was `{}`.
5. `on_inferred="warn"` didn't help: the overflows aren't "inferred
   preconditions" (no single bound), so they still fail. The message ends
   with `on_inferred='warn' or 'silent' assumes it`, which reads as though
   it would make the error go away.
6. `infer=False`, `infer=False, on_inferred="silent"` and `strict=True` all
   gave the same error. `strict` warns `DeprecationWarning: transform(strict=True)
   is deprecated; write infer=False`. Three parameters for whether and how
   preconditions are inferred.
7. With bounds declared: proved. A bad row: `PreconditionError: 1 inserted
   row(s) of items violate (_.price > 0)`. The exception carries no
   attributes (`rows`, `condition`, `source`), so a job can't quarantine the
   rows and go on, the way dbt's `store_failures` or a dead-letter table
   would.
8. Composition: `healthy needs (_.margin_pct >= 0) (it may be FALSE on some
   rows) on 'm'; margins only guarantees (_.revenue >= 0)`. Clear and
   actionable.

## Checker binary

The prebuilt `substrait-check` I first linked was built at 22:17 the day
before, before this morning's Lean merges, so `semantics="polars"` failed with
`ValueError: substrait-check --contract failed: error: divide: option
division_type = [FLOOR] is not supported (the model does [TRUNCATE])`. I
switched to a checker built at b87a8963 (the commit under test) and reran
every task. Only two outputs changed: `report.epsilon` now says
`'proved': {'abs': True}`, and the RouteError lost a "(tested)". The log
above reflects the current checker except where noted.

A user hits the same thing with `SVERIFY_CHECK` pointing at an old build, or
an editable install after `git pull` without `lake build`: a `ValueError`
with checker internals. sverify knows its checker's hash
(`substrait-check.hash` sits next to the binary); a mismatch could say
"the checker is older than this sverify; rebuild with `lake build
substrait-check`". `CheckerVersionError` exists in `sverify.errors` but
didn't fire.

## Task 7: DuckDB and Polars (3 attempts)

1. Six small jobs, each `sv.verify` then `run` on both engines: all ran.
   Classes: `exact` on DuckDB, `shim` on Polars for integer division and
   strings, `observed` for a mean on both, and `None` for a `LAG` over a
   unique key on both. `Route.cls` is None, which is none of the four
   documented classes.
2. `Route` has 17 public fields (`bound_proved`, `cls`, `fallbacks`,
   `rerun_evidence`, `suggested`, …). For "can I run this on Polars, and what
   do I give up?" I want two: the class and one sentence.
3. Ibis `x // 2` on `x = -7` gives `-4` under the reference (floor, Ibis's
   `FloorDivide`), SQL `x // 2` gives `-3` (truncation, DuckDB's `//`), and
   `x % 2` gives `-1` in both. So with Ibis, `q * 2 + r == x` fails for
   negative `x` under the reference and DuckDB semantics, and holds only
   under `semantics="polars"`. examples.md (example 4) says "Polars's integer
   division floors, and the reference's truncates", which a user reads as
   "Ibis `//` truncates". The same operator means two things in sverify's
   two input languages, and the docs mention neither.
4. `semantics="polars"` then `run(con, "duckdb")`: `refused on duckdb:
   integer // and % with division_type FLOOR (Polars's, semantics='polars')
   run on polars only; duckdb truncates: verify with semantics='reference' to
   run on duckdb`. Clear, though DuckDB's own `//` from Ibis floors (point 3).
5. No one-call "where can this run?" matrix: I looped over engines and
   caught exceptions. `report.routes` is filled only for engines already run.

## Task 8: `to_substrait()` (2 attempts)

1. `report.to_substrait` gives 79 KB of protobuf JSON for a one-column
   projection, and `sv.from_substrait` proves it again. Works.
2. `Node` and the decorated transform have no `to_substrait`; only a
   `Report` does (`transform.last_report.to_substrait` works). A pipeline
   user holds nodes.
3. `node.plan` is also a Substrait JSON string, with sverify's private
   extension URNs (`extension:io.sverify:black_box`). Two Substrait outputs,
   one portable and one not, and nothing on `node.plan` says which.
4. `t.filter(t.w > 1.0)` can't be exported by default: `refused for
   Substrait: cmp's nan_equality: Substrait allows NAN_IS_NOT_NAN where the
   proof uses NAN_IS_NAN (ST-4, upstream/bugs/ST-4.json); no shim writes it
   for this plan: export with shims='annotate' …; cmp's nan_order: …; cmp's
   zero_sign: … state zeros in sv.equivalent(...)`. Three reasons, a path
   into a repository the user doesn't have, and `nan_equality` for a plan
   with only `>`. A filter on a double column is common; the default
   `shims="apply"` refusing it is a surprise. The last fix doesn't say which
   value (`zeros="canon"`).
5. `upper`: `upper maps non-ASCII text by a rule Substrait leaves open
   (ST-10, …)`, refused in every mode, with nothing to do about it.
6. A mean with `sv.equivalent(floats=sv.within(abs=1e-6))` exports with
   `class=exact`, while `run` calls the same plan `observed`.
7. `sverify.engines.run_substrait_json` runs on DataFusion only (needs the
   `datafusion` extra); the name doesn't say so.

## Task 6b: `on_unproved="warn"`

`on_unproved="warn"` builds the node with a plain `UserWarning` (the whole
report as its text), and then `refresh` refuses: `RouteError: refused on
duckdb: big: not verified: … run(..., unverified=True) runs it anyway`. I
called `refresh`, not `run`; `refresh(unverified=True)` works. So "warn"
needs a second opt-in at every refresh, and the message names the wrong
method.

## Obsolete and overlapping parameters

From the public docstrings and signatures:

- `transform(strict=)`: "Deprecated alias of `infer`, with the opposite
  polarity". Still in the signature.
- `sv.references(*legacy)`: deprecated positional form.
- `sverify.testing.Connection.datafusion`: deprecated.
- `transform(check_requires=)` and `Report.run(check_inputs=)`: one idea,
  two names.
- `Report.run(deterministic=)` and `engines.to_sql(tie_free=)`: one idea,
  two names (the guide says `tie_free=True` is "justified by a report's
  `deterministic`").
- `transform(engine=)` is where checks on data run; `refresh(engine=)` and
  `run(con, engine)` are where the plan runs. One word, two meanings.
- `sv.verify(transform, …)`: the first parameter is named `transform` and
  takes an Ibis expression or SQL.
- `Report.run(engine=None)` defaults to the connection's engine;
  `Node.refresh(engine="duckdb")` to DuckDB.
- `on_unproved=`, `on_inferred=`, `infer=`, `strict=`, `unverified=`: five
  knobs for "what happens when something isn't proved".
- `sv.__all__` exports `Report`, a dataclass with ~25 constructor fields.

## Second pass, on main at 7af9267d

Rebuilt the checker for main after #681 and installed sverify editable from
it, with `testing`.

### RANK, rechecked

`t4_sql_model.py` with the `rank()` column: `n_orders >= 1`, `revenue >= 0`
and `revenue_rank >= 1` now prove (#681). `unique(customer_id)` still fails,
the join-key gap (#694).

### Task 9: pytest (2 attempts)

1. `assert_contract`, `assert_engines_agree` and the `sv_engine`/`sv_source`
   fixtures work as the README shows. The failure messages are the best in
   sverify: `big_orders on duckdb does not give the expected rows: missing (1
   expected row(s) not produced): {'id': 1, 'doubled': 61} unexpected …`, and
   `the test data does not meet what big_orders requires: 1 row(s) of orders
   violate (_.amount >= 0): {'id': 1, 'customer': 'ada', 'amount': -5}`, with
   the rows. A refresh's `PreconditionError` (task 3) shows no rows.
2. `cases(node)` yields `{"orders": pyarrow.Table}`, while `assert_contract(data=)`
   takes `{"orders": [tuple, ...]}`. My property test indexed rows and failed
   with `'>=' not supported between instances of 'pyarrow.lib.Int64Scalar' and
   'int'`. One shape for test data in both places, or `data=` accepting
   tables, would avoid it.
3. `assert_contract(big_orders(ibis_table))`: `TypeError: expected a
   sverify.Node (a source piped into a transform), got Table`. A transform
   works on Ibis tables, so a contract test on one is the natural first step.

### Task 10: a custom source into Iceberg (3 attempts)

1. `pip install 'sverify[iceberg]'` gives no catalog to try it with:
   `SqlCatalog` needs `sqlalchemy` (`pyiceberg[sql-sqlite]`). Notebook 2's
   header has it; the README's extras list doesn't say so.
2. `from_query(fetch, cursor_on="ts", name="events")` into an `IcebergSink`,
   then an append, a restart (`resumed from analytics.per_user@v2`): all
   worked first time.
3. A late event (older than the cursor): `refresh()` says `events@v2
   unchanged, already committed` and drops it, as the docstring warns.
   `refresh(audit=True)` raises `AuditError: events@v2 differs from the table
   read again in full: its batches missed rows; nothing was applied`. The
   error names neither the rows nor a fix. The usual fix, re-reading a window
   behind the cursor and deduplicating by key, has no parameter:
   `from_query(..., lookback=timedelta(minutes=15), key="event_id")` would
   pair with `sv.arrives_within`.
4. The sink's table property `sverify.contract` holds the contract as JSON,
   with `"not_null": []` again (task 3, #691).
5. `AuditError` is raised from `sverify.incremental` (also in `sverify.errors`).

### Task 11: SQL for the warehouse (3 attempts)

1. `to_sql(json.loads(node.plan), SNOWFLAKE)` works, for DuckDB, Snowflake
   and Spark. The SQL is three nested subqueries with positional aliases
   (`s3."g0"`, `"m0"`, `"c1"`) and an overflow guard on every `SUM`
   (`CAST('sverify: integer overflow: ' || … AS NUMBER(38,0))` on
   Snowflake). It runs, but no one would paste it into a dbt model or review
   it in a PR.
2. There is no `report.to_sql(dialect)` beside `report.to_substrait()`.
3. `node.table` before a refresh: `RuntimeError: per_customer has no state
   yet: call refresh() first`. After it, `node.table` is the stored state,
   so `sv.verify(node.table…, requires={"orders": …})` fails with `unknown
   table 'orders'; the inputs are: per_customer`, and the node's proved
   contract doesn't come along (#692 has "facts as chainable conditions").
4. A top-1 by `total` on Snowflake: `Snowflake tables have no row order, so
   FETCH and windows over a named table cannot follow the Lean model's list
   order (windows run with tie_free=True)`. It mentions windows for a
   `LIMIT`, and Lean; and doesn't say the fix: break the tie with a key
   (`order_by([_.total.desc(), _.customer])`), which makes
   `report.deterministic` True, then pass `tie_free=True`.
