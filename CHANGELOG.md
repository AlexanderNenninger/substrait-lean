# Changelog

## 0.7.1 (2026-11-07)

Two soundness fixes on 0.7.0. Every plan 0.7.0 ran still runs.

### Fixes

- A stated tolerance (`sv.equivalent(floats=sv.within(...))`) on a double
  column whose bound the checker can't give, such as a `SUM` of doubles
  without a row cap or a value computed from one, passed as met by every
  engine, and the plan reported proved. It is now refused there with the
  reason (`… has no bound on its distance to the reference …`), and a run on
  such a column counts as tested ([#1029](https://github.com/AlexanderNenninger/substrait-lean/pull/1029)).
- A window `SUM`, `AVG`, `VARIANCE` or `STDDEV` of doubles was classed
  `exact`: the plan's bound left window functions out
  ([#1032](https://github.com/AlexanderNenninger/substrait-lean/issues/1032)).
  Such a plan still runs. `Report.epsilon` gives the column no bound
  (`"abs": null`, naming #1032), its route is observed on tested evidence,
  and a tolerance stated on the column is refused.

## 0.7.0 (2026-11-05)

0.6.0 was tagged but never published: two tests the release ran against the
installed wheel read repository files the wheel doesn't have, so nothing
reached PyPI. 0.7.0 is the first release of 0.6.0's changes (the 0.6.0
section below), of 0.5.0's, and of these. It is also the first release of
`sverify-dbt`, at the same version. A release's version-bump pull request now
runs the whole wheel test, so a failure like this shows before the tag.

### Breaking changes

Upgrading from 0.4.0, read the 0.6.0 and 0.5.0 sections' breaking changes
too. New in 0.7.0, in the entry "Breaking: sources, sinks and the top level of
1.x" below:

- `StaticSource(table, name=...)` and `sverify.testing.source(..., name=...)`
  need `name=`, and `version` is keyword-only.
- `SourceBatch.kind`, `SourceRefresh.mode` and `SinkWrite.mode` are
  snake_case (`"change_feed"`, `"snapshot_diff"`, `"row_level"`), with no
  deprecation period.
- Renamed keywords and methods on sources and sinks warn and name the new
  form.
- SQL from `node.to_sql(dialect)` and `report.to_sql(dialect)`; one way to
  run on Spark (`sverify.engines.run`); `con.create`, `con.rows`, `con.get`
  and `con.put` replace the table helpers; `substrait_json` lifts under the
  reference semantics by default.
- The `sverify` command's exit codes, flags (`check --fix/--diff/--full`,
  `--format`) and JSON (format 1 of `schemas/cli.schema.json`) change before
  1.x freezes them.

Names deprecated in 0.6.0 and 0.7.0 still work with a `DeprecationWarning`
that names the replacement; they go in 0.8, since 0.6.0 never reached PyPI.

### Coverage targets for 1.0

`docs/coverage-targets.md` lists the SQL and Ibis constructs sverify 1.0 covers, by area, with the ones skipped and the reason for each ([#743](https://github.com/AlexanderNenninger/substrait-lean/issues/743)). `python -m sverify_dev.coverage --targets` prints the share covered, 27 of 60 on 2026-11-05.

### A template repository for pipelines on GitHub

- `templates/pipelines/` holds the contents of a template repository for
  data engineering on your phone
  ([#771](https://github.com/AlexanderNenninger/substrait-lean/issues/771)):
  workflows that prove each pull request's pipelines and comment the
  contract in plain words (`check`), run them on staging data with a
  preview catalog (`preview`), refresh `main`'s on a schedule in a
  `production` environment (`refresh`), publish a catalog to GitHub Pages
  with DuckDB-WASM (`pages`) and open an issue when a refresh fails
  (`alerts`). Tables go to a `data` branch by default, or to your bucket
  through OIDC for enterprise. A worked pipeline keeps Eurostat's
  `nama_10_gdp` up to date, and `CLAUDE.md` with sverify's skills teaches
  Claude Code the loop. CI runs the template's steps on a recorded Eurostat
  response against every change to sverify.

### ODCS contracts

`sverify.odcs` writes a node's contract as an Open Data Contract Standard
document (ODCS v3.2.0) and reads ODCS contracts as conditions
([#791](https://github.com/AlexanderNenninger/substrait-lean/issues/791)).
The export maps NOT NULL columns to `required`, keys to `primaryKey` and
`unique`, value sets, ranges and row caps to quality rules, and the
docstring to descriptions; each rule carries a `sverify` custom property
saying whether it is proved, checked on the data or declared. `odcs.read`
gives the conditions for `requires` or `ensures` and lists, with a warning,
every rule it cannot read. `sverify contract export <file>:<node> --format
odcs` writes it from the command line. YAML needs the new extra
`sverify[odcs]`.

### Breaking: sources, sinks and the top level of 1.x

From the API review before 1.0 (`api-review/PROPOSAL.md`, items 11 and 12).
Each old form below still works in this release with a `DeprecationWarning`
that names the new one, except the snake_case values.

Sources and sinks (E2–E5):

- `contract(version=None)` reads the recorded contract on every source and
  sink: `DeltaSource`, `IcebergSource` (where `version` is a snapshot's
  sequence number, read from the metadata log), `DeltaSink`, `IcebergSink`
  and a `Sink` of your own. `Sink.committed()` is deprecated; a custom sink
  overrides `contract()`, and one that still overrides `committed()` works
  with a warning.
- `DeltaSource.contract(version)` reads the contract recorded up to
  `version`. Before, it returned the latest one, because delta-rs's history
  of a table loaded at an older version lists the latest commits
  ([DL-2](upstream/bugs/DL-2.json)).
- `DeltaSink.maintain(vacuum_retention=)` and
  `IcebergSink.maintain(snapshot_retention=, min_snapshots=)` take the
  constructors' names; `vacuum=` and `expire=` are deprecated. Every
  retention takes a `timedelta` or an ISO 8601 duration such as `"P7D"`.
- `StaticSource(table, name=..., version=...)` and
  `sverify.testing.source(rows, schema, name=...)` need `name=`, and
  `version` is keyword-only: two sources named `"table"` in one pipeline
  would collide.
- `SourceBatch.kind`, `SourceRefresh.mode` and `SinkWrite.mode` are
  snake_case: `"change_feed"`, `"snapshot_diff"`, `"row_level"`. Code that
  matches `"change feed"`, `"snapshot diff"` or `"row-level"` changes; the
  printed reports read as before.

The top level (A1–A4, A6):

- `Changes` is `sverify.io.Changes`, beside `StaticSource`, and
  `sv.from_substrait(data)` is `sv.Report.from_substrait(data)`, beside
  `Report.from_json`.

  ```python
  from sverify.io import Changes  # was: sv.Changes

  orders.apply(Changes(inserts=[(3, "cy", 50)]))
  report = sv.Report.from_substrait(exported)  # was: sv.from_substrait
  ```
- `sv.rows_per("customer", "day", at_most=3)` takes its columns as `unique`
  and `key` do; `rows_per(["customer", "day"], 3)` is deprecated.
- `sv.arrives_within("ts", "PT15M")` takes the lateness as a `timedelta` or
  an ISO 8601 duration; `days=`, `hours=`, `minutes=` and `seconds=` are
  deprecated.
- `sv.approx(cond, rel=, abs=, ulps=)` takes the tolerances of `sv.within`;
  the comparison moves by the largest of them, and by `rel=1e-6` when none
  is given.
- `sv.sql(query, name="orders")` names the chained table, the word every
  source uses; `as_=` is deprecated. `semantics` is typed as `Semantics`.
- A transform's report is `transform.report`, as a node's is
  `node.report`; `last_report` is deprecated, and `last_preconditions`
  (the refresh report says how each precondition was established).

### Repeated terms written once

A term a written plan computes in several places, `CASE` branches among
them, is now computed once as a column when the plan evaluates it on every
row anyway (#821, `Expr.repeated` in `SubstraitLean/Bind.lean`). Ibis's
`find` with a start drops from 66 kB of Snowflake SQL to 3 kB, and
`day_of_week.full_name()` from 11 kB to 2 kB on DuckDB and Spark.

### Smaller written SQL

Sverify binds the arguments that its guards would copy to columns before it
writes a plan (`SubstraitLean/Bind.lean`, #821): a nested date or double
operation, or an aggregate's argument, is computed once in a projection
below and read by name. The `month end` query of #821 drops from 51 kB of
Spark SQL to 7 kB, and the catalogue's largest Snowflake statement from
547 kB to 16 kB. `Rel.evalI_bindArgs` and `Rel.raises_bindArgs` prove
that the plan computes the same rows and raises the same errors on every
engine.

### Breaking: SQL from a node or a report, one way to run on Spark, `Connection` methods (api-review F1 to F4)

From the API review before 1.0
([#795](https://github.com/AlexanderNenninger/substrait-lean/pull/795),
`api-review/PROPOSAL.md` F1 to F4). The deprecated names still work in
0.7 with a `DeprecationWarning` that names the replacement, and go in 0.8.

- `node.to_sql(dialect)` and `report.to_sql(dialect)` write the plan a proof
  checked as DuckDB, Snowflake or Spark SQL (`"duckdb"`, `"snowflake"`,
  `"spark"`, or a `Dialect`), with its run-time checks. They refuse a plan
  that is not proved (`UnverifiedRunError`), as `refresh` and `run` do, and a
  report's `deterministic` lets windows run without a row-order tiebreak.
  Before, the way to SQL was `to_sql(json.loads(node.internal_plan), dialect)`.
- `con.create(name, schema, rows)` and `con.rows(name)` replace
  `sverify.engines.create_table(con, name, schema, rows)` and
  `table_rows(con, name)`, which warn.
- `Connection.arrow` and `Connection.ibis` are deprecated: `con.get(name)`,
  `con.rows(name)` and `con.put(name, table)` read and write the tables, and
  `con.table(name).get_backend()` is the Ibis backend, for SQL of your own.
- `sverify.engines.run(con, plan, "spark")`, or a Spark session as the
  engine, is the one way to run a plan on Spark; `run_spark(plan, tables)`
  warns. A window without a row order runs on Spark when the contract
  states its order key (`sv.unique(...)`), through `node.to_sql("spark")`
  or `report.to_sql("spark")`; `run` takes no tie flag.
- `sverify.engines.substrait_json(con, sql)` now lifts the SQL under the
  reference semantics, as `sv.verify` and `sv.sql` do. Pass
  `semantics="duckdb"` for what DuckDB computes, the old default.
- The API reference documents `Dialect` by its fields (`name`, `guards`,
  `finite`, `decimals`). Its SQL-writing methods, subclasses of it, and the
  plan layer (`to_sql`, `substrait_json`, `written_plan`,
  `run_substrait_json`, `delta_plans`) are outside the 1.x promise
  ([docs/stability.md](docs/stability.md)).

Migration:

```python
# before
from sverify.engines import SNOWFLAKE, create_table, run_spark, table_rows, to_sql
create_table(con, "orders", schema, rows)
table_rows(con, "orders")
to_sql(json.loads(node.internal_plan), SNOWFLAKE)
run_spark(plan, {"orders": orders_table})
con.ibis.raw_sql("SELECT 1")

# after
con.create("orders", schema, rows)
con.rows("orders")
node.to_sql("snowflake")
run(con, plan, "spark")  # con holds the orders table
con.table("orders").get_backend().raw_sql("SELECT 1")
```

### `round(x, d)` follows DuckDB 2.0 where the result overflows

`round(x, d)` with a negative `d` gives `x` itself where the rounded value
would overflow, as DuckDB 2.0 does (`round(1.5e308, -308)` is `1.5e308`),
where the model gave 0, DuckDB 1.4's answer. The Polars and SQL writers
follow, and the engine fact `duckdb-round-digits-2` supersedes
`duckdb-R15-round-digits`, whose probes missed the case.

### Faster rows in and out of a connection

`con.create`, `con.rows` and the row lists a refresh reads build and read
Arrow tables column by column, without a dictionary per row: 100,000 rows of
four columns go into a table in 22 ms (88 ms before) and out in 71 ms (92 ms
before), with a quarter and three fifths of the Python memory.

### Breaking: the `sverify` command before 1.0 (API review I1–I5)

The command 0.6.0 shipped (#744) changes its exit codes, flags and JSON
before 1.x freezes them
([#797](https://github.com/AlexanderNenninger/substrait-lean/pull/797)):

- Exit codes: 0 proved (a refresh committed every row), 1 not proved,
  2 usage error (argparse's too), 3 unsupported or refused, 4 time or
  memory budget exceeded, 5 a refresh quarantined rows or held a node,
  6 error. In 0.6.0, 2 was refused, 3 budget, 4 error. `sverify --help`
  lists them.
- `sverify suggest <file> [--apply]` is `sverify check <file> --diff` (show)
  and `--fix` (write, then check again).
- `sverify explain <file>:<node>` is `sverify check <file>:<node> --full`;
  `explain` takes codes only.
- Codes are snake case (`may_be_false`), as the report writes them, each with
  a level; `explain` still reads kebab case.
- `--format text|json|github|sarif|junit` (`--output-format`; `--json` is
  `--format json`). `github` writes workflow commands that annotate a pull
  request's lines, `sarif` a SARIF 2.1.0 log for code scanning, `junit` a
  test report
  ([#793](https://github.com/AlexanderNenninger/substrait-lean/issues/793)).
- The JSON is format 1 of `schemas/cli.schema.json`: each node's `name`,
  `nodes`, `status`, `summary` (its third key is `not_proved`), `links` and
  `report`, the node's `Report.to_json()`. The 0.6.0 keys `verdict`,
  `problems`, `needs` and `facts` come from the embedded report.
- `sverify contract export` (#791) follows the same exit codes.
- `import sverify` loads its names on first use: `sverify --help`,
  `--version` and `explain` take 0.1 s, down from 1.3 s.

### The checker's slow cases

- The checker's abstract evaluation no longer evaluates a projection's or an
  aggregate's input once per expression, which grew exponentially with the
  plan's depth: TPC-DS q36 took 56 s per proof and takes 0.8 s, and the
  catalogue's 55 contracts 110 s and 5 s
  ([#825](https://github.com/AlexanderNenninger/substrait-lean/issues/825)).
  A decimal cast's bounds, each table's description and a plan with
  `VALUES` cost less too.

### A faster check: a proof cache, and no search where only ties are open

- Sverify keeps the checker's answers on disk, so the next `verify`,
  `check` or `refresh` of an unchanged transform does not prove it again.
  An entry is keyed by the plans, conditions and profile the checker reads,
  sverify's version and a hash of the checker binary; any change to them
  proves again. The cache is in `SVERIFY_CACHE_DIR` (default
  `~/.cache/sverify`), and `SVERIFY_CACHE=off` turns it off
  ([#825](https://github.com/AlexanderNenninger/substrait-lean/issues/825)).
- A postcondition that only the order of ties leaves open has the reason
  `"ties"` (`CheckedCondition.ties`), and the counterexample search skips
  it ([#691](https://github.com/AlexanderNenninger/substrait-lean/issues/691)).
- A checker request interrupted by the CLI's time budget or Ctrl-C ends
  the checker's process. Before, its answer stayed in the pipe and the next
  request read it as its own.
- The checker speaks protocol 2 (a `--rows` mode for the counterexample
  search): rebuild a checker you set with `SVERIFY_CHECK`.
- CI times every catalogue transform and the tour's notebooks, cold and
  warm, by stage, and fails past the budgets of
  [#745](https://github.com/AlexanderNenninger/substrait-lean/issues/745)
  (`python -m sverify_dev.bench`).

## 0.6.0 (2026-11-05, tagged, not published)

0.5.0 was tagged but never published: a Spark test ran out of memory in the
release's wheel tests, so nothing reached PyPI. 0.6.0 is the first release of
0.5.0's changes (the 0.5.0 section below) and of these. It is also the first
release of `sverify-dbt`, at the same version.

### Breaking changes

Upgrading from 0.4.0, read the 0.5.0 section's breaking changes too. New in
0.6.0, each with its own entry below:

- Fewer knobs for "not proved" and one name per concept (#690, #695):
  `on_inferred="off"` replaces `infer=False`; the route `"reference"` is
  `"translated"`; `@sv.transform(engine=)` is `check_engine=`;
  `Report.run(check_inputs=)` is `check_requires=`; `node.plan` is
  `node.internal_plan`. Renamed keywords warn and go in 0.7. Removed:
  `strict=`, the positional `sv.references`, `Connection.datafusion`.
- A run of an unproved plan raises `UnverifiedRunError`, a
  `VerificationError` and a `RouteError`.
- Every exception sverify raises derives from `sverify.errors.SverifyError`.

### Quarantine: bad rows set aside, the rest flows

A batch that breaks a precondition on a source no longer has to stop the
pipeline ([#184](https://github.com/AlexanderNenninger/substrait-lean/issues/184)).
`on_violation` on `sv.transform` or on a source chooses what a refresh does:

- `"quarantine"` sets the offending rows aside, with the reason, in a table
  next to the node's sink (`<sink>_quarantine`, or `.write(sink,
  quarantine=...)`), and the node runs on the others. A row breaks a row
  condition, or shares its key with another row: every row of a repeated
  key is set aside, so the rule needs no order and a recompute agrees with
  the batches. `Catalog.kept_sound` (`SubstraitLean/Quarantine.lean`)
  proves every precondition holds on the kept rows, so the node's proof
  holds. A delete or update upstream releases rows.
- `"hold"` commits nothing for the batch and holds the node at its
  versions until a later version meets the preconditions. Conditions on a
  table as a whole (`max_rows`, `arrives_within`) hold the node this way
  under quarantine too.
- `"error"` stays the default.

The refresh report says how many rows each refresh set aside, released and
saw deleted, with examples. `Refresh.outcome` (`"ok"`, `"quarantined"`,
`"held"`), `Refresh.alert()` (Markdown for whoever is on call) and
`Refresh.to_json()` (format 1, `sverify/schemas/refresh.schema.json`) are
new, and `Node.quarantined()` returns the rows set aside. `sverify refresh`
exits 5 when rows are quarantined or a node is held, with `status`
`"quarantined"` or `"held"` in its JSON. The quarantine
table's format is stable within 1.x (`sverify/schemas/quarantine.schema.json`,
[docs/stability.md](docs/stability.md)).

`SchemaError` now names the column, the change, the version and the
contract it breaks, with what to do: "`orders.id` became nullable at v12,
and the new rows have NULLs in it; `paid` requires _.id.notnull(). Fix the
upstream, or handle NULLs in `paid` (e.g. `.fill_null(0)`) and relax
`requires`."

### One vocabulary for `on_unproved`, `on_inferred` and `on_violation`

The three `on_*` parameters share their values (the API review's C1): `"error"`
raises, `"warn"` goes on with a warning, `"ignore"` goes on silently,
`"check"` checks on the data at run time, `"off"` infers nothing, and
`on_violation` adds `"quarantine"` and `"hold"`.

- `on_unproved="runtime"` is now `on_unproved="check"`, and
  `on_inferred="silent"` is `on_inferred="ignore"`. The old spellings still
  work for one release, with a `DeprecationWarning`; a report JSON written
  with `"silent"` reads as `"ignore"`.
- `transform(check_requires=False)` with an `on_violation` other than
  `"error"` raises `ValueError`: that setting acts on the checks it turns off.

### Breaking: fewer knobs for "not proved", one name per concept (#690, #695)

From the API critique (#686). Every renamed or removed keyword below still
works in 0.6 with a `DeprecationWarning` that names its replacement, and goes
in 0.7. The names deprecated before 0.5 are gone.

Not proved (#690):

- `on_inferred="off"` replaces `infer=False` on `sv.verify` and
  `@sv.transform`: nothing is inferred or assumed, so a `SUM` that may leave
  64 bits, or a double operation that may overflow to ±inf, is an error.
  `on_inferred` takes `"error"` (the default), `"warn"`, `"silent"` and
  `"off"`. `infer=` warns.
- `@sv.transform(on_unproved="warn")` now lets the node's refreshes run
  unverified, each with an `UnverifiedRunWarning`, where it used to need
  `refresh(unverified=True)` as well.
- A run or refresh of a plan that is not proved raises
  `sverify.errors.UnverifiedRunError`, a `VerificationError`, so
  `except VerificationError` catches every "not proved". It is also a
  `RouteError`, so `except RouteError` still catches it. A refresh's message
  names `refresh(unverified=True)`.
- An assumed `SUM` reads `fits 64 bits in every group (checked at run time:
  the job raises if it does not; on_inferred="off" makes it an error)`, and
  an assumed finite double operation `stays finite on finite inputs (checked
  at run time …)`. Neither says "inferred" any more.
- Removed: `@sv.transform(strict=...)` (deprecated since 0.4),
  `sv.references(col, table, other)` (write `to=`), and
  `sverify.testing.Connection.datafusion` (deprecated since 0.4).
- `node.plan` is `node.internal_plan`: sverify's own form of the plan, with
  its private extension URNs. `Report.to_substrait()` is the portable one.
  `node.plan` warns.

Names (#695):

- The route `"reference"` is `"translated"`: a plan verified under
  `semantics="reference"` runs through the translation to the engine.
  `route="reference"` warns and takes `"translated"`; `Route.kind` is
  `"translated"`.
- A route's line names the route only where it is not `translated`:
  `exact; transfer: verified under semantics="duckdb"; …`.
- Printed output says `semantics="duckdb"` where it said `Profile.duckdb`.
- `@sv.transform(engine=)` is `check_engine=`: where checks on data run.
  `refresh(engine=)` and `run(con, engine)` keep `engine` for where the plan
  runs.
- `Report.run(check_inputs=)` is `check_requires=`, as on `@sv.transform`.
- `sverify.engines.to_sql(tie_free=)` is `deterministic=`, as on
  `Report.run`; `run_spark` too. `to_sql` also takes the plan as a JSON
  string, so `to_sql(node.internal_plan, SNOWFLAKE)` needs no `json.loads`.
- `Node.refresh(engine=None)` and `Group.refresh` default to `None`, DuckDB,
  as `Report.run(engine=None)` defaults to its connection's engine.
- `sv.verify`'s first parameter is `query`, positional-only.
- `report.equivalence` is the equivalence the result is proved up to, by the
  name of `sv.equivalent`; `report.observation` stays.
- `report.needed_text` is a property; `Report.needs_text()` and
  `needs_lines()` warn.
- A refresh report of a stored node is headed by the transform and the sink,
  `daily_revenue → daily:`, where the names differ.
- `summary()` reads `changes from orders v1→v2 (change feed)` where it read
  `orders@v1→v2, Δ trusted (change feed)`.

### Public API additions

- `sverify.__version__` is the installed version, and `dir(sverify)` lists
  `__all__` and `__version__`; the submodules import as before.
- `node.to_substrait()` and `transform.to_substrait()` export the report of
  a node and of a transform's last call, as `report.to_substrait()` does;
  `node.report` is that report.
- `PreconditionError` carries the table (`.source`), the condition
  (`.condition`) and up to ten of the rows that break it as an Arrow table
  (`.rows`).
- `sv.key("id")` states a primary key: `sv.unique("id")` and
  `'"id" IS NOT NULL'`.
- `report.not_null` lists the output columns the checker shows are never NULL, and
  a stored node writes them as NOT NULL columns and records them in its
  contract, with those `ensures` states.
- `report.needed_conditions` gives `report.needs` as conditions ready for
  `requires=`: Ibis deferreds for an Ibis transform, SQL strings for a SQL
  one.
- Every exception sverify raises on purpose derives from
  `sverify.errors.SverifyError`, and keeps its built-in base; the classes
  stay importable where they are defined.
- `isin([0, 1])`, and SQL's `x IN (0, 1)`, of integers that fill a range is
  read as that range, so a column known to lie in it meets the condition.

([#691](https://github.com/AlexanderNenninger/substrait-lean/issues/691))

### The strings a column can hold

Sverify tracks the strings a column can be while they are few (up to 64):
a constant is its string, `s = 'k'` and `s IN ('a', 'b')` narrow a column,
`s <> 'k'` and `NOT IN` take strings out, and `CASE`, `COALESCE`, projections,
joins, grouping and `UNION ALL` carry the sets through. A filter
`status <> 'cancelled'` over a source whose `status` is one of four strings
proves `status IN ('placed', 'shipped', 'returned')`, which is dbt's
`accepted_values`, and a tag that is a constant in each branch of a
`UNION ALL` proves the tag's values. The report's facts name the strings:
"one of the strings 'q1', 'q2', 'q3', 'q4'"
([#708](https://github.com/AlexanderNenninger/substrait-lean/issues/708)).

A key of each branch of a `UNION ALL`, with a column the branches cannot share
a value in (a constant tag, a `GROUPING` level, ranges apart), is a key of the
union. `unique(region, quarter)` over an unpivot by `UNION ALL`, and the
group keys of a rollup written as a union, now prove
([#436](https://github.com/AlexanderNenninger/substrait-lean/issues/436)).

### sverify-dbt lives in this repository and is released with sverify

`sverify-dbt` ([`dbt/`](dbt/README.md)), which proves a DuckDB dbt
project's data tests and model contracts before the models run, is back in
this repository with its history. From this release on it is published to
PyPI with sverify, at the same version, pinning `sverify==<version>`. The
`dbt` CI job runs its tests, its check of the sample project
(`dbt/examples/shop`, 19 of 26 tests and constraints proved), and
`dbt build` without the proved tests
([#732](https://github.com/AlexanderNenninger/substrait-lean/issues/732),
[#177](https://github.com/AlexanderNenninger/substrait-lean/issues/177)).

### A map of the proofs

[`docs/proofs.md`](docs/proofs.md) names each Lean module's job and the
theorems each guarantee rests on (`contract_sound`, `Rel.keys_sound`, the
delta rules, the engine profiles' shims), with what they trust. Each
generated Lean module's header says how to regenerate it, and
`tests/test_proof_map.py` keeps the map in step with the modules (#733).

### Stable formats and a stability policy for 1.x

[docs/stability.md](docs/stability.md) states what 1.x keeps stable: the
formats a running pipeline reads, the contracts it proved, and the Python
API, which breaks in a minor release only loudly, with a test, a changelog
entry and a migration note
([#737](https://github.com/AlexanderNenninger/substrait-lean/issues/737)).

- The sink's contract record (`sverify.io.Contract`) has a `format`, 1, and
  a JSON schema, `sverify/schemas/sink-contract.schema.json`. A record
  without `format`, written before this release, reads as format 1; a
  record of a newer format is refused with an error that says to upgrade
  ([#734](https://github.com/AlexanderNenninger/substrait-lean/issues/734)).
- The Substrait contract metadata, `io.sverify.substrait.v1.Contract`,
  follows protobuf's rules for updating a message, and its manifest has a
  JSON schema, `sverify/schemas/substrait-manifest.schema.json`
  ([#735](https://github.com/AlexanderNenninger/substrait-lean/issues/735)).
- `python/tests/formats/` holds what each release wrote: Delta and Iceberg
  sinks from 0.4.0 on and Substrait exports.
  [`tests/test_formats.py`](python/tests/test_formats.py) reads them all, and
  a pipeline resumes from an old Delta sink.

### The report as JSON

`Report.to_json()` writes a report as a versioned JSON document for CI jobs
and tools, and `Report.from_json()` reads it back into a `Report` with the
same verdict
([#736](https://github.com/AlexanderNenninger/substrait-lean/issues/736)).
The document holds the verdict, each postcondition with its reason, message
and counterexample, the runtime issues and assumptions, what the proof needs
(`Report.needs`), the facts, the non-NULL columns and the routes. Its format
is 1, with a JSON schema, `sverify/schemas/report.schema.json`, and follows
the rules of [docs/stability.md](docs/stability.md): within 1.x it only gains
keys, and a reader refuses a newer format with an error that says to
upgrade. `python/tests/formats/` holds reports for
[`tests/test_formats.py`](python/tests/test_formats.py) to read back.

### The `sverify` command

- `sverify check <file>[:<node>]` proves every contracted transform and node
  a Python file applies, without running it, and prints the contract in
  plain words first: what the output guarantees, what each refresh checks
  on the data, and what is not proved, each problem with a code. A dbt
  project goes to `sverify-dbt check`
  ([#744](https://github.com/AlexanderNenninger/substrait-lean/issues/744)).
- `sverify suggest <file> [--apply]` writes the preconditions the proofs
  need (`Report.needs`) into the decorators' `requires=`, then checks the
  file again.
- `sverify refresh <file>:<node>` runs a node and reports what changed;
  `sverify explain <code>` explains a code, and `sverify explain
  <file>:<node>` prints a node's full report.
- Every command takes `--json` (a provisional format until #736) and exits
  0 proved, 1 not proved, 2 refused, 3 budget exceeded, 4 error.
- `--timeout` (default 30 s, `SVERIFY_TIMEOUT`, 0 turns it off) bounds
  proof, planning and checking, never a refresh moving data.
  `--memory-limit` (`SVERIFY_MEMORY_LIMIT`) sets DuckDB's `memory_limit`,
  with a spill directory (`SVERIFY_SPILL_DIRECTORY`); a breach stops before
  any sink commits.
- `sverify.cli.discover(path)` does what `check` does from Python.

### Spark's local session keeps its parser cache bounded

`sverify.engines`' local Spark session turns on Spark's management of the SQL
parser's ANTLR cache (`spark.sql.parser.manageParserCaches`, flushed at 10 % of
the driver heap). The deeply nested SQL that sverify writes for date arithmetic
grew that cache to most of the 1 GB default heap, and later queries failed with
`AGGREGATE_OUT_OF_MEMORY` (the 0.5.0 Wheels run). `SVERIFY_MEMORY_LIMIT`
(#783) now also sets the session's `spark.driver.memory`.

## 0.5.0 (2026-11-05, tagged, not published)

### Breaking changes

Upgrading from 0.4.0, check these first. Each has its own entry below.

- `Report.run`, `Node.refresh` and a group's `refresh` refuse a plan whose
  report is not proved (#655). Pass `unverified=True` to run it anyway. Runs
  choose their route by default (`route="auto"`); `route=None` is gone.
- A precondition that sverify infers is an error by default (#655): add it to
  `requires`, or pass `on_inferred="warn"` (0.4.0's behaviour, with a
  warning) or `on_inferred="silent"`.
- Route classes are renamed (#655): `refines` is `exact`, and
  `refines_up_to` and `approx` are `observed`. The other two classes are
  `shim` and `refused`.
- A sink's `reproducible` defaults to doubles within the plan's proved bound
  (`floats="plan"`) (#655). A sink whose consumers need the same bits on a
  rerun states `reproducible=sv.equivalent()`.
- `Report.run` checks preconditions and the absence of new `±∞` on the data
  before it runs (#604, #575). A batch that breaks them is refused with a
  `PreconditionError`. `check_inputs=False` skips the precondition check.
- `AND` and `OR` evaluate both operands (#604, D19), so an error in either
  operand counts. A constant subexpression that raises makes the whole plan
  raise (#609). Both change the reference.
- Polars always runs on its streaming engine. Polars's engine settings and
  environment variables no longer choose the engine.
- The SQL lift refuses rankings with an `ORDER BY` of their own (#625).
- The reference leaves the order of ties open (#679, D24). Proofs hold for
  every order. A deterministic run (`deterministic=True`, an incremental
  refresh, or a sink's `reproducible=`) refuses a plan whose ties stay open,
  and names each place (`Report.tie_places`).
- `verify` checks a stated float tolerance against the plan's bound on each
  engine (#689). A tolerance tighter than every engine meets leaves the plan
  unproved; before, it was refused only at run time.

### `sv.rows_per` bounds the rows per key, and row caps bound exact sums

`sv.rows_per(["customer"], at_most=n)` in `requires` states that at most `n`
rows of an input agree on the columns. It is checked on the data like
`unique`. Lean carries the bounds through filters, sorts, `DISTINCT`,
projections, unions and joins on a key, and an aggregate grouping by the
columns has groups of at most `n` rows. So an integer or decimal `SUM` of
values in `[-m, m]` per group is proved to fit when `n · m` does, without a
cap on the whole table
([#219](https://github.com/AlexanderNenninger/substrait-lean/issues/219)).
`Report.relations` lists the bounds on each relation's rows.

A row cap (`sv.max_rows`) now also bounds the value of an exact `SUM`, so
decimal arithmetic on a sum, such as TPC-H q11's `SUM(…) * 0.0001`, can be
proved to fit
([#470](https://github.com/AlexanderNenninger/substrait-lean/issues/470)).

### Sharded integer AVG

`--shard` and `sverify.engines.run_sharded` split an integer `AVG` (Substrait's
`avg` of `i64` with an `i64` result) across shards: each shard computes a `SUM`
and a `COUNT`, the combining plan adds them up and divides, truncating toward
zero. Lean proves it once for algebraic aggregates, a final expression over
distributive partials (`Rel.eval_algebraic` in `SubstraitLean/Partition.lean`),
when the plan's column types make the argument an integer. `AVG` with a double
result is still refused with `float_order="exact"` ([#245](https://github.com/AlexanderNenninger/substrait-lean/issues/245)).

### COUNT, SUM and DISTINCT are maintained from changes

A node that ends in an aggregate of `COUNT` and integer `SUM` per group, or
in `DISTINCT`, is now maintained from the changes to its input when the
input has delta rules. It keeps a count and a sum per group beside its rows
and adds each batch's change to them, so a refresh no longer reads the input
of the groups a batch touches, and `status()` reports the node as
maintained. Lean proves the result equal to a full recompute, groups that
appear and disappear included (`LinearAgg.aggregate_maintained` and
`LinearAgg.distinct_maintained`). An integer `SUM` that leaves 64 bits still
raises, as on a full recompute. This is the first stage of
[#248](https://github.com/AlexanderNenninger/substrait-lean/issues/248).

### MIN, MAX, exact AVG, semi and anti joins are maintained from changes

A node that ends in `MIN`, `MAX`, or a `DECIMAL` `SUM` or `AVG` per group is
now maintained from its input's changes, like `COUNT` and integer `SUM`. A
batch that only inserts into a group merges its values into the group's
state; the groups it deletes from are recomputed from the new input, and
only those. A node that ends in a semi or anti join on equal keys keeps a
count of matches per key, so a refresh never reads the right side and reads
the left side only for the keys that gain their first match or lose their
last. Lean proves each equal to a full recompute
(`ExtremeAgg.extreme_maintained`, `ExtremeAgg.map_maintained`,
`SemiDelta.semi_maintained`), and the new state survives a failed commit.
`mean()` of integers, a double, is still recomputed by touched groups. This
is the second stage of
[#248](https://github.com/AlexanderNenninger/substrait-lean/issues/248).

### Polars runs decimal plans

`engine="polars"` runs plans over `DECIMAL` columns, which it used to refuse
("unsupported column type"). Values keep the plan's `DECIMAL(p, s)`, and the
translation computes what Polars rounds differently: a product at the sum of
the scales, a smaller scale and an `AVG` half away from zero, an empty `SUM`
as NULL ([#27](https://github.com/AlexanderNenninger/substrait-lean/issues/27),
[engine-profiles.md](docs/engine-profiles.md#decimals-on-polars)). The 22
TPC-H queries, 8 TPC-DS queries and 10 finance queries of the catalogue now
run on Polars. A cast of a double to a decimal of more than 22 places is
refused there.

### `verify` reports a decimal `SUM` that may leave its precision

A `SUM` of decimals has a declared precision: ten more digits than its
argument, at most 38. DuckDB raises past it ("Overflow in SUM of DECIMAL"),
while `verify` let a contract over the sum be proved. It now reports the
overflow as it does an integer `SUM` that may leave 64 bits: with `infer`,
the sum is assumed to fit and checked on the data while the job runs
(`Report.assumed`), and row caps with a bound on the column prove it fits
([#316](https://github.com/AlexanderNenninger/substrait-lean/issues/316)).

### Black-box functions

DuckDB functions the checker treats as opaque now come from one table,
`core/Sverify/Core/BlackBox.lean` ([#325](https://github.com/AlexanderNenninger/substrait-lean/issues/325)).
Each row gives a function's types, how it treats NULL, whether it may raise,
and its laws, which the contract checker uses and Lean proves of the model.
The SQL lift reads them, the plan calls them under the URN
`extension:io.sverify:black_box`, and DuckDB runs its own function; other
engines refuse them (#271). The first two are `base64(encode(s))` (also
`to_base64`), never NULL for a string, and the aggregate `entropy(x)`, a
double at least 0, so `verify` proves `entropy(x) >= 0`. Adding a function is
adding a row ([reference semantics](docs/reference-semantics.md#black-boxes)).

### Statistical aggregates as black boxes

The SQL lift reads more of DuckDB's aggregates as black boxes
([#326](https://github.com/AlexanderNenninger/substrait-lean/issues/326)):
`product`, `kahan_sum` (also `fsum`, `sumkahan`), `favg`, `sem` and `mad`, not
NULL over values, `sem` and `mad` at least 0; and `kurtosis`, `kurtosis_pop`
and `skewness`, which DuckDB raises on for infinite or huge values, so
`verify` reports a domain error. Black-box aggregates may now raise. Integers
are converted to doubles, as DuckDB converts them. `bit_count` of a BIGINT is
exact, in [0, 64]. `histogram` (a MAP) and `weighted_avg` (two arguments) are
refused with a reason. The engine facts `duckdb-moments` and
`duckdb-statistical-aggregates` record what DuckDB 2.0.0 does.

### Vector and list functions

The SQL lift reads DuckDB's vector functions of lists of doubles as black
boxes ([#327](https://github.com/AlexanderNenninger/substrait-lean/issues/327)):
`list_cosine_similarity`, at least -1, so `verify` proves
`array_cosine_similarity(a, b) >= -1`; `list_cosine_distance` and
`list_distance`, at least 0; `list_inner_product`,
`list_negative_inner_product` and `array_cross_product`. Each may raise, on a
NULL element or lists of different lengths. The `array_*` names are read as
the functions of lists. `list_sum` of integers is exact, a BIGINT as `SUM`'s.
`list_extract`, `list_element` and `array_extract` are read as `l[i]`, and
`array_value(…)` as a list literal. The engine facts `duckdb-list-vectors` and
`duckdb-list-sum` record what DuckDB 2.0.0 does.

### More DuckDB scalars as black boxes

The SQL lift reads more of DuckDB's scalars
([#328](https://github.com/AlexanderNenninger/substrait-lean/issues/328)),
as rows of the black-box table: `printf` and `format` of a format and one
value, which may raise; `octet_length(encode(s))` and `strlen(s)`, the UTF-8
byte length, at least 0; `signbit` of a double; and `yearweek` of a date,
bounded by DuckDB's dates. Lean evaluates all but `printf` and `format`.
`weekday(d)` is now read as `dayofweek(d)`, exactly. `age` stays refused:
its INTERVAL is not in the model. The engine facts `duckdb-printf`,
`duckdb-signbit` and `duckdb-yearweek` record what DuckDB 2.0.0 does
([reference semantics](docs/reference-semantics.md#black-boxes)).

### A SUM of a double constant is a double SUM in the written SQL

The SQL writer read a double constant in an aggregate as an integer, as Lean's
`Expr.kind` does for a double's code, where Lean's parser goes by the plan's
literal. So `SUM('inf'::DOUBLE)` was written as an integer `SUM` and raised
"integer overflow in SUM: inf", where `Rel.eval` and DuckDB give `inf`. The
writer now reads the declared type as Lean does (`doubleJ`), for `SUM`, `AVG`
and the sides of `COVAR_*` and `CORR`
([#341](https://github.com/AlexanderNenninger/substrait-lean/issues/341)).

### Hash joins and hash aggregation in Lean's evaluator

`substrait-check` evaluates plans with inlined data through `Rel.evalFast`
(`SubstraitLean/EvalFast.lean`), which Lean proves equal to `Rel.eval`, rows and
order included (`Rel.evalFast_eq`). Equi-joins, semi-joins, `EXCEPT` and `INTERSECT` hash the right
side, and `DISTINCT`, `fn(DISTINCT …)` and `GROUP BY` use hash sets and maps,
where `Rel.eval` compares every pair of rows. The query of DuckDB's
`hash_join_dict_surviving_outer_build.test` (3,532 rows) evaluates in 0.41 s,
down from 9.2 s, and its larger variant in 0.33 s, down from 54 s.
`substrait-check --eval-spec` evaluates with `Rel.eval`, for tests
([#357](https://github.com/AlexanderNenninger/substrait-lean/issues/357)).

### Proved error bounds for sharded double `SUM` and `AVG`

`--shard` and `sverify.engines.run_sharded` with `float_order="any"` now split
`SUM` and `AVG` of doubles with a proved bound on how far each result is from
Lean's one-pass sum. Each shard also reports `SUM(|x|)`, `COUNT(x)` and
`MAX(|x|)` per split double, `--shard`'s output says which columns carry the
bound (`float_bounds`, `Split.float_bounds`), and `run_sharded(...,
tolerance=True)` returns a `Sharded` with τ per row and column.
`sverify.partition.apriori_tolerance` gives the bound before running, from a
row cap and a bound on the values. The bounds are proved in
`float-bounds/FloatBounds/Shard.lean` and linked to the split plan by
`floatSplit_sum` and `floatSplit_avg` in `SubstraitLean/Partition.lean`
([#428](https://github.com/AlexanderNenninger/substrait-lean/issues/428)).

### The SQL lift reads the variance family

`sv.sql` and SQL transformations now lift `STDDEV_SAMP`, `STDDEV_POP`,
`VAR_SAMP`, `VAR_POP`, the aliases `STDDEV` and `VARIANCE`, `COVAR_SAMP`,
`COVAR_POP` and `CORR`, of integers and doubles, to the Substrait functions the
Ibis producer writes. With `semantics="duckdb"`, `CORR` is DuckDB's: NaN for
one pair or a side whose values are all equal, where the reference's is NULL
(`duckdb-corr`). The SQL writer now runs a `FILTER` on `COVAR_*` and `CORR`. Sverify proves what it proves for Ibis's `std()`, so
`SELECT workflow, stddev_samp(duration_s) FROM jobs GROUP BY workflow` gives
"a double ≥ 0.0 or NULL", with `GROUP BY ROLLUP` too. Of a `DECIMAL` they are
refused for now
([#433](https://github.com/AlexanderNenninger/substrait-lean/issues/433)).

### `verify` proves that a `SUM` of a 0/1 flag fits 64 bits

Counting rows with `SUM(CASE WHEN … THEN 1 ELSE 0 END)` no longer gets a
"SUM overflow" warning. A group has fewer than 2⁶³ rows, as `COUNT(*)` is a
BIGINT in the reference and in every engine, so a `SUM` of values in
`[-1, 1]` fits 64 bits without a row cap. The size hypothesis of the
reference semantics now states that bound. Values in a wider range still
need `sv.max_rows(n)` to be proved
([#437](https://github.com/AlexanderNenninger/substrait-lean/issues/437)).

### Ibis conditions on SQL transformations

`sv.verify` on a SQL string took only SQL conditions and raised a
`TypeError` on an Ibis one. Its `ensures` and `requires` now take Ibis
conditions too: an Ibis postcondition reads the lifted query's output, and
an Ibis precondition its input table, so a query keeps its contract when it
moves between SQL and Ibis
([#438](https://github.com/AlexanderNenninger/substrait-lean/issues/438)).

### DeltaSink accepts its constraints as Delta stores them

Delta (delta-rs) reads a CHECK constraint back in its own form: `x BETWEEN 0 AND 10` as `x >= 0 AND x <= 10`, and `hi >= lo` as `lo <= hi`. `DeltaSink` now compares constraints after rewriting `BETWEEN` into its two comparisons and turning every comparison to face the same way, so a stored node with a proved `between` or a column-to-column comparison in its `ensures` refreshes again after its first write ([#439](https://github.com/AlexanderNenninger/substrait-lean/issues/439), [#487](https://github.com/AlexanderNenninger/substrait-lean/issues/487)).

### The options a plan meets, and whether its proof transfers

`substrait-check --dependencies <plan.json>` lists the options a plan meets,
with the reference's, DuckDB's and Polars's choice at each. It says, for each
pair of profiles, whether a proof under the first holds under the second, and
which shims each engine needs for the plan. Lean proves the check sound
(`Rel.transfer_of_transferB`,
[#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444)).

### Engine settings checked before a routed run (#444)

A profile's facts hold under the engine's default settings. Before
`Report.run(..., route=...)` or `refresh(route=...)` runs, sverify reads
the settings the plan will run under and compares them with those the
facts were probed under. A setting a choice depends on refuses the run
with the setting named (`sverify.errors.EngineSettingsError`): on DuckDB
`default_null_order`, `default_order`, `integer_division`,
`error_on_division_by_zero`, `ieee_floating_point_ops`,
`default_collation`, `scalar_subquery_error_on_multiple_rows`,
`enable_optimizer` and `disabled_optimizers`; on Polars an engine
affinity that forces another engine than streaming
(`pl.Config.set_engine_affinity("in-memory")`), since sverify runs
Polars's streaming engine (#605). DuckDB's
`preserve_insertion_order` warns (`EngineSettingsWarning`). `TimeZone` and
`Calendar` are not checked: the written SQL never reads them
(duckdb-time-zones). DuckDB's settings are read on the cursor sverify
runs plans on, so a `SET GLOBAL`, or a `SET` of a global-only setting, is
seen; a session's `SET` on another cursor is not.

### DuckDB and Polars as choice tables

`substrait-check --options` now prints DuckDB's (2.0.0) and Polars's (2.1.0)
choices and how each relates to the reference, option by option, for integer
and double arithmetic, `SUM`, `AVG` and sorts, from their facts in
`characterization/`
([#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444)).
A plan's integer `divide` may now state `division_type: TRUNCATE`, which is
what it computes.

### The float tolerance per engine

`--contract` now gives each double output column a bound per engine
(`"epsilon_by_engine"`). The bound carries the summation order's share and
each engine's own per-operation error through `+ − × /` from the ranges the
preconditions give: Polars's division by a literal is within 3u of IEEE's
quotient, and its `log10`, `log2` and `log(b)` within 2.1 ulp; DuckDB's
`log(b, x)` within 1.4 ulp; `+ − × /` and `sqrt` are correctly rounded on
both. Lean does not prove these bounds yet
([#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444)).

### Engine sums, transfers up to an order, and a LIMIT over ties

- DuckDB's and Polars's double `SUM` and `AVG` are within #85's bound of the
  reference's, not one of its orders: DuckDB merges partial sums in finishing
  order and adds a constant vector as one product; Polars's in-memory groups
  use Kahan's sum
  ([#633](https://github.com/AlexanderNenninger/substrait-lean/issues/633)).
- The transfer check between profiles (`--transfer`, a route's transfer)
  accepts a behaviour below the one the proof used, such as a sequential sum
  where the proof allowed any order.
- A contract's dependency report leaves out the value choices of columns
  nothing reads.
- A `LIMIT` below an `ORDER BY` that ties, or with none, makes the report
  not deterministic
  ([#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444), D10).

### The reference's options in one table

The options a plan may set, and the reference's choice at each, are now one
table in Lean (`core/Sverify/Core/Options.lean`, step 1a of
[#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444)), and
the parser reads it. `substrait-check --options` prints it. Plans are read as
before, with one addition: `variance` and `std_dev` of integers accept
`rounding: TIE_TO_EVEN`, as `avg` of integers does.

### Polars plans stream, with native expressions

The Polars engine now computes integer `POWER`, month arithmetic and
`date_trunc` of dates, `GREATEST` and `LEAST`, double sort, group and join
keys, and the aggregates `COUNT`, `MIN`, `MAX`, `BIT_AND`, `BIT_OR`,
`BIT_XOR`, `VARIANCE`, `STDDEV` and their `DISTINCT` forms as Polars
expressions, where it ran Python and numpy on each batch before, so these
plans run fully on Polars's streaming engine. A test checks every plan the
Polars tests run: a node on the in-memory engine fails it unless
`polars_engine.ALLOWED_FALLBACKS` lists it (`ARRAY_AGG`'s ordered list,
window frames). `Report.run(..., streaming="require")` refuses a plan with
such a node, and a routed run records them in `Route.fallbacks`.

Double `/` is Polars's own: by a constant it goes through the reciprocal and
is within 2 ulps (PL-3, from #608), and a subnormal divisor is refused on the
data. numpy, imported only when needed, keeps `%` of doubles (C's `fmod`)
and `ROUND(x, d)`'s division by `10^d` exact. `power(-inf, 0.5)` is `+inf`
and a difference of zeros the one zero, where Polars gives NaN and `-0.0`
([#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444)).

### Plans checked under Polars's semantics run natively on Polars

`verify(semantics="polars")` now checks an Ibis transformation under
`Profile.polars`, an evaluable profile in Lean
(`SubstraitLean/PolarsProfile.lean`): integer `//` and `%` floor, as Polars's
do, so a postcondition such as `x % 2 >= 0` is proved. The plan states
`division_type: FLOOR`, the checker reads it as Polars's remainder (proved on
64-bit integers), and `report.run(con, "polars", route="auto")` takes the
`native` route, with no shim. DuckDB and the other engines refuse such a plan
with the reason. `substrait-check --contract` answers `"profile": "polars"`,
so the re-check route can target Polars, and inferred preconditions work
under `semantics="polars"`
([#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444)).

### The Polars shims, proved (#444)

Each shim and guard of the translation from the reference to Polars
(`sverify._polars_shims`) now has a Lean theorem of its name,
`Polars.<name>` in `SubstraitLean/PolarsShims.lean`: the shimmed expression
gives the reference's value, and each guard flags exactly where the
reference's precondition fails. `Polars.written_faithful` and
`Rel.polars_sound` prove the error-side rows need no shim for a verified
plan. `substrait-check --options` reports these rows as `"evidence":
"proved"` with the theorem and the facts its model rests on.

### Polars runs the reference natively, with named shims

The Polars engine now runs integer `+`, `-`, `*`, division and remainder, and
`SUM` and `AVG` of a group as Polars's own operations. Where Polars 2.1.0
gives another value than the reference on inputs the reference does not raise
on, a named shim (`sverify._polars_shims.SHIMS`) gives the reference's:
truncating division and remainder, `ROUND`'s halves away from zero, `NULL` for
an empty `SUM`, the integer `AVG` in its declared type, one zero, each sort
key's NULL placement and stable ties. Each shim names the Polars fact it rests
on ([#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444)).

A double `SUM` or `AVG` now adds in Polars's own order, which the reference
allows (`sum_order = ANY`), so its last bits may differ from `Rel.eval`'s. A
sort key without a direction sorts ascending with NULLs last. `guards=` of
`run` and `to_lazy` also takes the issues to check by name, such as
`{"SUM overflow", "overflow to infinity"}` for the preconditions a report
assumes ([#575](https://github.com/AlexanderNenninger/substrait-lean/issues/575)).

### Polars runs every query on the streaming engine

Sverify now runs each Polars query on Polars's streaming engine, named
explicitly, so `POLARS_ENGINE_AFFINITY`, `pl.Config.set_engine_affinity`,
`POLARS_FORCE_STREAMING` and `POLARS_AUTO_STREAMING` no longer choose the
engine. A Polars `LazyFrame` given as a source is collected the same way.
Operators the streaming engine lacks still run on the in-memory engine inside
the streaming plan; `sverify.polars_engine.streaming_fallbacks` lists them
for a query
([#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444)).

### Proved float tolerances for `SUM` and `AVG`

The per-plan tolerance `--contract` reports for a double `SUM` or `AVG`
(`"epsilon"`) is now proved in Lean for every summation order the engines
use: trees of additions, DuckDB's constant runs and Polars's Kahan sum
([#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444),
[#85](https://github.com/AlexanderNenninger/substrait-lean/issues/85)). So is
the relative bound for values of one sign, and the propagation of `ε` through
`+`, `-`, `*` and `/` per engine
([#568](https://github.com/AlexanderNenninger/substrait-lean/issues/568)).
Routes that rest on these bounds report evidence `proved` where they reported
`tested`; elementary functions and `Float32` sums stay `tested`
([docs/float-bounds.md](docs/float-bounds.md#the-engines-orders-and-epsilon-444)).

### The realizability table (#444)

`docs/realizability.md` lists, for DuckDB and Polars and every option of
the catalogue, how a plan verified under the reference runs there: native,
after a shim (with its cost), up to an observation, within a float bound,
behind a precondition the reference raises on, or refused, with the theorem
or facts each row rests on, and the shim count per engine. It is generated
from `substrait-check --realizability` (`SubstraitLean/Obligations.lean`)
by `python -m sverify_dev.realizability --write`, and
`tests/test_realizability.py` checks it is current. `Rel.duckdb_refines`
states DuckDB's translation as a refinement of the reference, raise sets
included (`Lowering.lowerRel_raises`). `substrait-check --dependencies` and the
route's class list the Polars `null_order` shim only where a key leaves its
NULL placement unspecified.

### Routes and determinism in refreshes (#444)

- `Node.refresh(engine=..., route="auto")` and `sv.group(...).refresh(route=...)`
  take each node's proof to the engine by a route, as `Report.run` does,
  and refuse before anything runs where none applies
  (`sverify.errors.RouteError`). `StageRefresh.route` records the route and
  its class.
- A stored node whose result is not determined up to row order (its
  report's `deterministic`) is refused: its sink commits each epoch once,
  so a rerun must give the same rows (D10 of
  [core-semantics.md](docs/core-semantics.md#d10-determinism)). A node
  without a sink reports it.

### What a rerun must reproduce (#444, D20)

Each output now has two observations: the postcondition's
(`sv.equivalent` in `ensures`), and what a rerun must reproduce, which
the result's consumer states. Sinks take `reproducible=sv.equivalent(...)`
(`DeltaSink`, `IcebergSink` and custom sinks through `Sink.__init__`), with
rows as a multiset and exact values by default, since a sink commits each
epoch once. `refresh(reproducible=...)` and
`Report.run(..., route=..., reproducible=...)` state one for a run; a plain
run requires none and reports determinism. The engine's run-to-run
variation on the options the plan depends on (the `rerun` column of its
choices; for Polars's streaming float `SUM`, within the plan's bound) must
refine it, and a result not determined up to row order fails every
requirement. Otherwise the refresh or run is refused with the reason
(`RouteError`). `deterministic=True` asks for exact values. Where the
tables have no `rerun` for an option, it is read as exact and the route
reports `rerun_evidence="tested"`.

### Observations in postconditions, and routes to engines (#444)

- `sv.equivalent(rows=…, floats=sv.within(abs=…, rel=…, ulps=…), zeros=…, timestamps=…, strings=…, decimals=…, errors=…)`
  in `ensures` names what the result's consumer observes: rows as a multiset
  (the default) or a sequence, doubles exact or within a tolerance, one zero
  and one NaN, timestamps to a precision, strings up to NFC. Observations are
  ordered by refinement, component by component (`Observation.refines`), and
  `Observation.equal` compares two results up to one. Each other postcondition
  that depends on what the observation ignores says so
  (`CheckedCondition.ignores`), and the report is then not proved.
  Without `equivalent`, nothing changes.
- `Report.run(con, engine, route="auto")` chooses how the proof reaches the
  engine: natively where the plan was verified under the engine's profile,
  through the reference's translation, by the option-wise transfer check,
  or by a re-check under the engine's profile, and refuses the plan with the
  reason otherwise (`sverify.routes`, decision D13 of
  [core-semantics.md](docs/core-semantics.md)). The route goes into
  `Report.routes`; `route="native"` and the others take that route or refuse.
  `deterministic=True` refuses a plan whose result is not determined up to
  row order (D10). Each route carries the plan's class on the engine
  (`Route.cls`: refines, refines up to an observation, approx, shim or
  refused), and an engine that agrees with the reference only up to an
  observation the postcondition does not state is refused, or shimmed. A
  function the engine does not run refuses the plan with the reason. Before
  it runs, a routed run checks the preconditions, the inferred bounds and
  the assumed `SUM`s on the data (`Report.check_inputs`) and refuses a
  batch that breaks one, naming it (`PreconditionError`). Without `route`,
  `run` behaves as before.
- `semantics="polars"` checks an Ibis transformation under Polars's
  profile, once the checker has one.
- `sv.equivalent(elements="multiset")` ignores the order of a list's
  elements. A postcondition the checker does not prove, and that reads the
  value of `first` or `last` without an order or a list's element order,
  says it depends on that open choice.
- Engine profiles record the versions their facts were probed at (DuckDB
  2.0.0, Polars 2.1.0). A routed run on another version warns
  (`EngineVersionWarning`), and one on another major version is refused
  (`EngineVersionError`) until the probes are re-run (D14).

### Unspecified and clustered sort directions

A `SortRel` key may now leave its direction unspecified, read as ascending
with NULLs last, or be `SORT_DIRECTION_CLUSTERED`, any order with equal keys
adjacent; both were refused before. A window's or a measure's order still
states its direction. Lean's `Rel.AllowedP` states what each profile allows,
with `Rel.allowed_core` proving the reference within the core
([#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444),
`docs/core-semantics.md`, D6 and D8).

### Checking under Substrait's own semantics

`verify(semantics="substrait")` checks an Ibis transformation under
`Profile.substrait`, Substrait's semantics as its extension YAMLs state it
([#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444)):
each option at the plan's preference among the YAML's values, any of them
where the plan states none, two zeros and signed NaNs as IEEE 754 has them,
and open wherever the YAMLs say nothing. Lean proves it refines the core
(`Profile.substrait_le_core`). The reference's proof holds there when, at
every option the plan meets, Substrait allows nothing the reference does
not; otherwise `Report.transfer` names the options. `substrait-check
--profile-diff` lists where the two profiles differ, published in
[docs/core-semantics.md](docs/core-semantics.md#the-substrait-profile).

### Substrait's own test cases run against `Profile.substrait`

The function test cases of `substrait-io/substrait` v0.106.0 run against
Substrait's profile on every pull request ([#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444), step 4):
`python -m sverify_dev.substrait_cases`, with the ledger
`upstream/substrait-cases.json`. Of 1,317 cases, 631 agree, 625 are refused
and 61 disagree, each disagreement a wrong test case
([ST-13](https://github.com/AlexanderNenninger/substrait-lean/blob/main/upstream/bugs/ST-13.json), [ST-14](https://github.com/AlexanderNenninger/substrait-lean/blob/main/upstream/bugs/ST-14.json),
[ST-15](https://github.com/AlexanderNenninger/substrait-lean/blob/main/upstream/bugs/ST-15.json)).

The replay fixed four parser bugs. `negate` of an integer constant at the
least value of its type (`negate(-128::i8)`) now overflows by its `overflow`
option, where it folded to 128. A call with a list literal argument
(`cardinality([1, 2, 3])`) is read, where constant folding refused it.
`variance` and `std_dev` read their `distribution` as the leading enum
argument of their current signatures. A date minus an interval whose result
is typed as a timestamp of any precision is refused, as the date plus one is,
where it returned a date.

### Delta tables with dots in their names, and `uc://` sinks

A `DeltaSource` or `DeltaSink` whose path ends in a name with dots
(`.../homelab.metrics.orders`, or `uc://homelab.metrics.host_minute`) got a
default name with dots, which the DuckDB engine read as catalog.schema.table,
so the first refresh failed
([#451](https://github.com/AlexanderNenninger/substrait-lean/issues/451)).
The default name now replaces the dots with underscores
(`homelab_metrics_orders`), and for `uc://catalog.schema.table` it is the
table's name (`host_minute`).

`DeltaSink("uc://…")` no longer hangs in delta-rs 1.6.6's
`DeltaTable.is_deltatable`: it opens the table, and raises a `ValueError`
saying to register the table first when Unity Catalog doesn't have it, since
a sink can't create a table through the catalog. The `DeltaSource` docs note
that delta-rs takes the `unity_*` options in lowercase and that a MinIO
endpoint goes in the same options as the catalog's.

### A local `DeltaSink`'s commits log what they changed

A `DeltaSink` on a local path commits the files DuckDB wrote, and the Delta
history showed that commit as a `WRITE` with no `operationMetrics`, while
the same refresh on S3, a delta-rs MERGE, logged the rows it inserted and
deleted ([#453](https://github.com/AlexanderNenninger/substrait-lean/issues/453)).
The local commit now logs a write's metrics (`num_added_rows`,
`num_added_files`, `num_removed_files`, …) and, for a change, the ones
delta-rs's MERGE logs (`num_target_rows_inserted`,
`num_target_rows_deleted`, `num_target_rows_copied`,
`num_target_files_added`, …), with `operationParameters.sverify` set to
`merge` or `created`. The operation stays `WRITE`: delta-rs 1.6.6 refuses
another name.

### Touched frames are proved

Lean now proves the touched-frames strategy, which maintains window
aggregates over bounded RANGE frames of one time column by recomputing only
the rows near a batch's changes
([#458](https://github.com/AlexanderNenninger/substrait-lean/issues/458),
part of [#294](https://github.com/AlexanderNenninger/substrait-lean/issues/294)).
A window row depends only on the rows of its partition whose time lies in
its frame (`TouchedFrames.outRow_local`), so the rows outside
`[t0 - end, t1 - start]` keep their values and the rows inside come out the
same from the narrowed input (`TouchedFrames.framed_batch`). `status()` and
the refresh summary no longer say "tested, not proved", and
`NodeStatus.tested` is now `NodeStatus.framed`.

A window whose frames all end before the row (or start after it) lost the
output rows near the end of a batch's span: the recompute read too few
input rows. The span now always holds the row itself.

### A verify report runs the plan it checked

`Report.run(con, engine=None)` runs the plan a `sv.verify` report is about,
for an Ibis expression or a SQL query, with its `params` and `semantics`.
Running that plan used to take `sverify.contracts.plan_json`, outside the
public API. `Report.plan` holds the plan as Substrait JSON
([#461](https://github.com/AlexanderNenninger/substrait-lean/issues/461)).

### An Iceberg sink maintains its table

A streaming `IcebergSink` used to add a snapshot, a data file and a position
delete file on every refresh, so a two-row aggregate refreshed every minute
grew by some 1,440 snapshots and 2,900 files a day. `IcebergSink` now takes
`DeltaSink`'s maintenance options: `compact_every=N` compacts the table after
every N writes, rewriting the data files with position deletes and the small
files of each partition as data files of their live rows in one `replace`
snapshot, and dropping the delete files no data file reads.
`snapshot_retention=` then expires older snapshots (keeping `min_snapshots`
and the sink's own last one) and deletes the files only they referenced.
`maintain()` runs it on demand. The compaction snapshot carries the contract,
so a restarted job resumes past it, and downstream nodes read through it. With
`compact_every=4`, an aggregate refreshed 37 times holds at most 5 snapshots,
4 data files, 3 delete files and 41 files on disk, and equals a full
recompute throughout (`test_maintenance_keeps_a_streaming_sink_bounded`)
([#465](https://github.com/AlexanderNenninger/substrait-lean/issues/465)).

### A partitioned Iceberg sink takes only the change

An `IcebergSink` whose table is partitioned (identity, `day()` or any other
transform) writes each refresh as one snapshot of position deletes and new
rows in the partitions the change touches, as an unpartitioned table
already did ([#43](https://github.com/AlexanderNenninger/substrait-lean/issues/43)).
It used to overwrite the whole table in two snapshots on every refresh. The
deletes read only the data files of the partitions the deleted rows fall
in, each delete file is in the partition of its data file, and the other
partitions keep their files. Rows are split by partition without
`pyiceberg-core`, which pyiceberg 0.12 needs for every transform but
`identity`, so a `day()`-partitioned sink also works without it
([#466](https://github.com/AlexanderNenninger/substrait-lean/issues/466)).

### An Iceberg sink creates its table where and how you say

`IcebergSink` takes `location=`, `partition_by=` and `properties=`, and its
first write creates the table with them in one commit. A catalog without a
default location, such as Unity Catalog's Iceberg REST catalog on a schema
without a managed storage root, can now hold a sink, and a sink can create a
partitioned table itself (`partition_by=[("ts", "day"), ("host",
"identity")]`), which then takes each change in the partitions it touches
([#466](https://github.com/AlexanderNenninger/substrait-lean/issues/466)).
They apply only to a table the sink creates: a sink on an existing table
that differs from them warns once and leaves the table as it is
([#468](https://github.com/AlexanderNenninger/substrait-lean/issues/468)).

### Upstream bugs as JSON documents

The upstream bugs ledger is now one JSON document per bug,
`upstream/bugs/<id>.json`, in the format of `upstream/bug.schema.json`, and
the lift's backlog of tests is `python/tests/lift_backlog.json`, with a
reason for each test. `python -m sverify_dev.bugs` and `tests/test_bugs.py`
check both: the schema, unique ids that name their files, and that the files,
engine facts and tests they link to exist (#477).

### Checks on data no longer warn through pandas

The checks on data (`on_unproved="runtime"`, `requires` on bound tables, node
refreshes) counted violations with Ibis's `execute()`, which converts the count
through pandas. Under Ibis 12 and pandas 3.1 that printed a `Pandas4Warning`
about `future.infer_string`, in notebooks 4 and 5 of the tour among other
places. The counts are now fetched through Arrow
([#479](https://github.com/AlexanderNenninger/substrait-lean/issues/479)).

### A report's assumed SUM names its column

`Report.assumed` named an integer `SUM` it assumes fits 64 bits by Lean's
column index (`SUM of $2`), while the hint on the same report named the
column. The assumed line now names the column the `SUM` adds up, as the hint
does (`SUM of amount_cents`), and `Issue.column` holds it
([#480](https://github.com/AlexanderNenninger/substrait-lean/issues/480)). A
report on SQL text, and a `SUM` of an expression, keep Lean's notation.

### The installed wheel's tests skip the refusal-message scan

`test_refusal_messages.py` reads the repository's sources, which the Wheels
workflow's copy of the tests against the installed wheel doesn't have. It now
skips there, as `test_scripts.py` does, so the wheel builds pass again
([#483](https://github.com/AlexanderNenninger/substrait-lean/pull/483)).

### A sink recovers from a write that failed after its commit

A `DeltaSink` write that raised after its commit had landed, for example
reading the table's version back while the object store restarted, left
every later refresh of the node failing in the same process until a restart
([#488](https://github.com/AlexanderNenninger/substrait-lean/issues/488)).
The next refresh now finds the epoch the table committed in its transaction
version and writes on from that state, as a restarted job does. A write that
failed before its commit is replayed. This holds for every sink with a
`committed()` that reads the sink back.

### Rolling means, MIN over a sliding frame, window aggregates of expressions

Sverify verifies `AVG`, a `SUM` of doubles and `MIN` over a frame that does not
start at UNBOUNDED PRECEDING: rolling means over rows or over an interval, and
`MIN` over a sliding frame. DuckDB and Polars run them; DataFusion, which
slides a frame by retracting rows, still refuses them. A window aggregate's
argument may be an expression (`(t.qty * 2).sum().over(group_by="name")`): the
checker computes it in a projection under the window, so its overflow and
other issues are checked as a projection's
([#506](https://github.com/AlexanderNenninger/substrait-lean/issues/506)).

### A time of day plus an interval, and truncated

`t.ts.time() + ibis.interval(hours=1)` and `t.ts.time().truncate("h")` now
verify, and run on DuckDB. A time of day plus a constant interval wraps around
midnight both ways, as DuckDB computes it (`TIME '23:30' + INTERVAL 1 HOUR` is
`00:30`); an interval with months is refused. Truncation to an hour, minute,
second or millisecond is a floor of the microseconds. The SQL lift reads
DuckDB's `TIME ± INTERVAL` too. Other engines refuse both until #271
([#507](https://github.com/AlexanderNenninger/substrait-lean/issues/507)).

### typeof of a column is a constant

`t.qty.typeof()` now verifies: the Ibis producer folds `typeof` of a column to
DuckDB's name of its type (`BIGINT`, `DECIMAL(10,2)`, `VARCHAR[]`), a string
constant in the plan, so every engine gives the same name. `typeof` of an expression, a struct or a map is refused,
since the engine infers that type its own way
([#508](https://github.com/AlexanderNenninger/substrait-lean/issues/508)).

### `uc://` sinks tell a registered table without a Delta log apart

`DeltaSink("uc://…")` on a table Unity Catalog has registered, but whose
storage location has no `_delta_log/` yet, said the table was missing from
the catalog and to register it, which it already was
([#512](https://github.com/AlexanderNenninger/substrait-lean/issues/512)).
The sink now says the location has no Delta table yet, with delta-rs's
reason, and that the first version must be written there (for example with
`write_deltalake` and the catalog's READ_WRITE keys). The catalog's
`TABLE_NOT_FOUND` and `SCHEMA_NOT_FOUND` keep the message to register the
table.

### A refresh that fails while committing changes nothing

A refresh that failed after DuckDB had updated a view's state in place (an
out-of-memory error, say) left the view ahead of its recorded source
versions, and the retry in the same process applied the batch a second
time: duplicated rows, then `changes delete rows that are not in the
inputs` or delta-rs's `rows failed validation check` in a sink. The commit
now updates the Python side first and DuckDB's state last, in one
transaction, and restores the old tables, versions and states on any
failure, so the retry applies the batch once
([#515](https://github.com/AlexanderNenninger/substrait-lean/issues/515)).

### A Delta source dropped and created again rewrites its sinks

A Delta source dropped and created again at the same path starts its
versions over. Its sinks had committed a higher epoch, so each refresh
skipped the write as "already committed" and kept the old table's rows,
with no error, in the same process and after a restart
([#516](https://github.com/AlexanderNenninger/substrait-lean/issues/516)).

The contract now records each Delta source's table id (`metaData.id`,
`Contract.table_ids`). When a source's id changed, or its version went
down, the sink's rows come from another table: the refresh recomputes the
node and overwrites the sink, so it holds a full recompute of the new
table. `DeltaSource.changes` reads the new table's snapshot when the table
was created again since the version asked for (the report says
"created again"), and a restarted job doesn't resume from a state stored
from the old table.

### Two processes refreshing the same `DeltaSink` no longer write a change twice

`DeltaSink` read the epoch the table had committed, then loaded the table
again and committed, so a commit by another process in between went
unnoticed. Two pods of one job during a rolling deploy, or a cron run
overlapping a slow one, could both write the same change, or write an older
change on top of a newer state, and later refreshes kept the duplicate rows
([#517](https://github.com/AlexanderNenninger/substrait-lean/issues/517)).

The commit is now conditional. It is made on a snapshot whose transaction
version (`app_id`) is still the one the refresh read, and every commit that
changes rows carries the transaction, so delta-rs's conflict check rejects a
concurrent one. The process that loses raises
`sverify.errors.ConcurrentWriteError`, naming the sink, and its write is not
committed. Its next refresh skips the state the other process committed, or
writes the whole table. This holds for local (native) commits and for
MERGE. A sink of your own raises the same error to get the same recovery.

### Exact median, quantiles, mode and arg_min/arg_max

Sverify now verifies the exact quantiles, the mode and `arg_min`/`arg_max`
([#53](https://github.com/AlexanderNenninger/substrait-lean/issues/53)), from
Ibis (`median()`, `quantile(q)`, `mode()`, `argmin()`, `argmax()`) and from
DuckDB's SQL (`median`, `quantile_cont`, `quantile_disc`, `quantile`,
`mode(x ORDER BY …)`, `arg_min`, `arg_max`), and runs them on DuckDB:

- `quantile_disc(x, q)` is the value at position `⌈n·q⌉` of the values in
  order; `quantile_cont(x, q)` and `median(x)` interpolate between the two
  neighbours at `(n−1)·q`, of doubles or of integers converted. `q` is an
  exact decimal in `[0, 1]`. Contracts know a median or quantile lies within
  its column's range.
- `mode` breaks ties by its own `ORDER BY`, and is refused without one;
  Ibis's `mode()` takes the smallest of the most frequent values.
- `arg_min(x, y)` is `x` at the row with the smallest `y`, over the rows where
  neither is NULL; ties are the engine's choice unless a key settles them, as
  for `first()`.

What DuckDB 2.0.0 does with each is recorded as engine facts
(`duckdb-quantile-disc`, `duckdb-quantile-cont-interpolation`,
`duckdb-mode-ties`, `duckdb-arg-min-nulls`). Other engines refuse them until
[#271](https://github.com/AlexanderNenninger/substrait-lean/issues/271), and
approximate quantiles stay refused
([#469](https://github.com/AlexanderNenninger/substrait-lean/issues/469)).
H2O's groupby q6 and the catalogue's median and arg_max queries now verify.

### A recreated Iceberg source no longer leaves its sinks stale

An Iceberg table dropped and created again under the same identifier is
another table, even where its sequence numbers reach the old ones. An
`IcebergSource` now records the table's UUID with each version it reads,
and sinks record it in their contract (`Contract.table_ids`), as Delta
sources do with their table id since
[#516](https://github.com/AlexanderNenninger/substrait-lean/issues/516). A
refresh then reads the new table in full, and a restarted job recomputes
its nodes instead of resuming from rows of the old table
([#533](https://github.com/AlexanderNenninger/substrait-lean/issues/533)).

### Two writers of one `IcebergSink` no longer apply a change twice

An `IcebergSink` now commits only while the table still holds the epoch it
read, as a `DeltaSink` does since
[#517](https://github.com/AlexanderNenninger/substrait-lean/issues/517). When
two processes refresh the same sink, the one that commits second raises
`ConcurrentWriteError`, also where pyiceberg would retry its commit on top
of the other writer's snapshot, and where both create the table. Its next
refresh writes the whole table, or skips the state the other writer
committed
([#534](https://github.com/AlexanderNenninger/substrait-lean/issues/534)).

### Window variance, unordered STRING_AGG, signed Ibis frame offsets, divisor suggestions

`VARIANCE` and `STDDEV` (of a sample or a population) now verify over a
window ([#54](https://github.com/AlexanderNenninger/substrait-lean/issues/54)).
Over a frame they are the reference's own two passes, which DuckDB runs
exactly; other engines refuse them for now (#271).

`group_concat()` / `STRING_AGG` without an order verifies: the strings may come
in any order, so `verify` reports the plan as not deterministic and proves no
postcondition about it. DuckDB joins them in the input's order.

Ibis windows with a negative offset count the other way, as Ibis means them:
`following=-1` is `1 PRECEDING`. Ibis's own SQL writes `-1 FOLLOWING`, which
DuckDB refuses ([IB-4](upstream/bugs/IB-4.json)).

`verify` now proposes a precondition for a division by an aggregate: each value
at least 1 (or 0.01 for a decimal) for a `SUM`, and the column NOT NULL for a
grouped `COUNT` (`_.size >= 1`, `_.user_id.notnull()`).

### Polars refuses `regexp_match` patterns with flags or lookarounds

The Polars engine counted the entries of `regexp_match` by asking Polars, so it
ran patterns with `(?i)`, named groups or lookarounds, where the reference
model raises a bad-regex error (`Text.simpleRegex`). It now counts groups as the SQL writer
does and refuses those patterns too, in one definition shared by both
([#544](https://github.com/AlexanderNenninger/substrait-lean/issues/544)).

### `QUANTILE_CONT` between `-inf` and `+inf` raises (#561)

`QUANTILE_CONT` and `MEDIAN` whose neighbouring values are `-inf` and `+inf`
now raise a domain error in the reference, as a NaN created from numbers does
(`AggFn.makesNan`). IEEE's interpolation, and DuckDB's, is NaN there; the
reference used to clamp it to `+inf`, so engines disagreed. A plan that may
meet it is reported as a possible domain error, ruled out by a precondition
that bounds the column, and the SQL sverify writes for DuckDB raises where
the interpolation is NaN and no value is. Per D17, this changes the reference
and ships in a minor version bump.

### More of `ε`: scalar rules, thresholds and relative bounds

`epsilon_by_engine` now carries `ε` through `abs`, `FLOOR`, `CEIL`, `ROUND`,
casts to integers and `sqrt`, each by a rule proved in
`float-bounds/FloatBounds/Propagate.lean`
([#568](https://github.com/AlexanderNenninger/substrait-lean/issues/568)). A
comparison is exact where its sides' ranges, widened by `ε`, do not meet, so a
filter or key on it keeps the same rows; the contract reports per engine
whether every filter, key and sort does (`"rows_exact"`). A column whose
range leaves out zero gets a relative bound too, and a difference of nearly
equal values gets none
([docs/float-bounds.md](docs/float-bounds.md#through-arithmetic)).

### Doubles: no operation creates `±∞` (#575)

The reference now raises where an operation on finite doubles overflows to
`±∞`: `+`, `-`, `*`, `/` and `power` (`1e308 * 10`, `power(0, -1)`), `exp`
past `709.78`, and a `SUM`, `AVG`, variance or covariance of finite values.
`verify` rules the error out by an inferred precondition, as for a `SUM` that
leaves 64 bits: a `SUM` or `AVG` of bounded values over a bounded number of
rows (`max_rows`) is proved finite (#85's error bounds), and elsewhere
`Report.assumed` lists the precondition ("stays finite where its inputs
are") and the job checks it on the data: the SQL sverify writes for DuckDB
raises `overflow to infinity` where it fails, and so does the Polars engine.
With `infer=False` it is an error that makes the report unproved. A plan verified
with `semantics="duckdb"`, where DuckDB's `±inf` is the answer, makes no such
assumption, and `Report.run` writes no check of it. `±∞` from
the data passes through as before. So a plan verified under the reference
creates no NaN and no `±∞` its inputs did not hold
([#575](https://github.com/AlexanderNenninger/substrait-lean/issues/575),
fact `duckdb-double-overflow`, spec gap `ST-9`).

### `Report.run` refuses an overflow to `±∞` before the run (#575)

`report.run(con, engine)` now checks the assumption that no operation on
finite doubles gives `±∞` on the data before the run, as it already did for
an assumed `SUM`: it runs the proved DuckDB translation first and refuses the
batch with a `PreconditionError` that names the operation, so nothing runs on
the engine. A refresh of several nodes stays atomic per node: the node whose
batch overflows writes nothing, while the stored nodes upstream of it, whose
results it reads, keep the epoch they committed.

### Bounds of one double operation, and `exp`

A double `+`, `-`, `*`, `/` or `exp` whose inputs' bounds keep the result
below the largest double no longer needs a "stays finite" check on the data,
and chains of them have bounds
([#582](https://github.com/AlexanderNenninger/substrait-lean/issues/582)).
`exp` propagates `ε` too, trusted to one ulp of the platform's `libm`
([docs/float-bounds.md](docs/float-bounds.md#one-operations-bounds-and-overflow-582)).

### Preconditions that relate columns are used in proofs (#597)

A precondition of any shape, such as the implication
`(_.a <= 0) | (_.b < 0)`, is now kept whole as a fact about each row. A
postcondition that restates it is proved wherever the plan carries it
through: projections that keep its columns, filters, sorts, limits, joins
and `UNION ALL`s whose inputs all have it. Under a filter or in a `CASE`
branch, the disjuncts that cannot be TRUE drop out and the rest narrows the
columns: under `t.filter(_.a > 0)` the implication gives `b <= -1`, also
when `a` or `b` may be NULL. Before, these postconditions were reported as
"TRUE or FALSE". Filter conditions are kept whole the same way. Steps 1 and
2 of #597; see `docs/guide.md`.

### `AND` and `OR` evaluate both operands, and the report says so (#604)

An error in either operand of `AND` or `OR` may raise, whatever the other
operand's value, as DuckDB and Polars evaluate both (decision D19 in
`docs/core-semantics.md`). The checker already analysed both operands. A
plan such as `filter((x != 0) & (10 // x > 1))` was proved only under the
precondition `x != 0` that `verify` inferred, and `Report.run` did not check
it, so a batch with `x = 0` raised on the engine (now refused: see the next
entry). The report now flags an error inside an `AND` or `OR`
(`Issue.under_and_or`) and suggests guarding the operation itself:
`(CASE WHEN x <> 0 THEN 10 // x END) > 1`, in Ibis
`ibis.cases((_.x != 0, 10 // _.x)) > 1`, which is proved without the
precondition.

### `Report.run` checks the preconditions first (#604)

`report.run(con, engine)` checks the report's preconditions on the tables
before the run, with or without `route=`: `requires` and the bounds `verify`
inferred. A batch that breaks one is refused with a `PreconditionError`
that names it, and nothing runs, as the reference's first guarantee promises.
Before, a plan proved under an inferred precondition (such as `x != 0` for
`filter((x != 0) & (10 // x > 1))`) ran on the batch and raised on the engine.
`check_inputs=False` skips the check for a caller that has made it already,
and gives up the guarantee on data that breaks a precondition.
`Node.refresh` already checked them on each batch.

### Constants that raise raise for the whole plan (#609)

A constant subexpression that raises, such as `1 // 0 = 1` in a later
`CASE WHEN`, now makes `verify` report the plan as raising, whatever the data
and whichever branch the rows take. DuckDB evaluates a `CASE`'s constant
conditions when it plans the query, so such a plan raised on any data, an
empty table included, though `verify` had proved it. The issue is flagged
`constant`, and the report says no precondition rules it out (D21). This
changes the reference and ships in a minor version bump (D17).

### `ABS` of a narrow integer

`verify` no longer crashes on `abs` of an `int8`, `int16` or `int32` column ([#616](https://github.com/AlexanderNenninger/substrait-lean/issues/616)). The model checks `ABS` at the column's width, as DuckDB does: `abs(-128::TINYINT)` raises, where the model gave 128 and the written plan returned it as a BIGINT, and the inferred bound stays within the column's type: `v >= -127` for an `int8`. An inferred bound never reaches `2**63`, and a SQL comparison of a narrow column with a constant that fits it compares the column itself, so such a bound in `requires` is used by the proof.

### The smallest BIGINT in messages

Reports and counterexamples print the smallest `BIGINT`, `-9223372036854775808`, as an integer; they showed it as the double `-0.000000d` ([#619](https://github.com/AlexanderNenninger/substrait-lean/issues/619)).

### Rankings with their own ORDER BY are refused

The SQL lift refuses `rank`, `dense_rank`, `row_number`, `percent_rank` and `cume_dist` with an `ORDER BY` of their own (`cume_dist(ORDER BY id) OVER (… frame)`), which DuckDB ranks within the frame. They were lifted as a plain rank over the partition, a wrong result in Lean and in the written SQL ([#625](https://github.com/AlexanderNenninger/substrait-lean/issues/625)).

### Three SQL lift refusals

The SQL lift refuses `x IN map(…)`, which it read as `FALSE`; an `INTERVAL '… ago'`, whose `ago` SQLGlot drops from a single unit (upstream/bugs/SG-8.json); and a cast to `TIMESTAMP(p)` for p from 0 to 3 or 7 to 9, which DuckDB keeps at seconds, milliseconds or nanoseconds where the lift kept microseconds. Each gave a wrong result in Lean and in the written SQL ([#626](https://github.com/AlexanderNenninger/substrait-lean/issues/626)).

### Times in nanoseconds are refused

A table with a column of times in nanoseconds (`time64[ns]`, DuckDB's `TIME_NS`) is refused when it is added: Ibis's time type has no unit, so the plan read the column as microseconds while the engine kept the nanoseconds, and a `::TIME` cast was lost ([#627](https://github.com/AlexanderNenninger/substrait-lean/issues/627)). Cast such columns to `time64[us]` first.

### Decimals in lists and structs print with their scale

Rows and counterexamples print a decimal inside a list or struct with its scale: `[1.0, 2.5]` for a `DECIMAL(4, 1)[]`, which printed as `[10, 25]` ([#628](https://github.com/AlexanderNenninger/substrait-lean/issues/628)). The values `Rel.eval` and the written plans compute were right.

### Reports and refusals in the user's terms (#655)

- Issues name columns and the Ibis or SQL operator (`total // qty`,
  `sum(x)`, `x / 0`) where Lean's notation said `($3 / $2)` or `$1`, and a
  domain error of a double `SUM` names its cause (NaN from +inf and -inf).
- An inferred precondition says where it came from: `requires t: (_.qty !=
  0) (inferred from total // qty)`, and a batch that breaks it is refused
  with the fix (filter those rows first, a CASE, or state it).
- The AND/OR hint writes out the guard for the user's division; the
  "it comes from it divides by 0" hint names the constant divisor.
- No more "assumes … stays finite" next to "may fail: division by zero"
  for the same operation; the NULL hint names the nullable columns and is
  dropped where none is; an unproved key says to add `sv.unique(...)`.
- An engine setting refuses only where the plan relies on it (a sort's
  NULLS LAST is spelled out, so `default_null_order` warns), and the
  refusal gives the `SET GLOBAL …` that restores it.
- A refused transfer leads with "verify with semantics='reference' to run
  on polars".
- Function refusals use the Ibis or SQL name (`median() or quantile()`,
  `re_extract()`), say which engine runs it and link #271 in full;
  `now()`, `current_timestamp` and `random()` in SQL are refused as
  non-deterministic; the SQL lift quotes the SQL, not SQLGlot's node.
- Refusals name a stored node by its transform (`mean (stored as m)`), and
  the fix for a non-deterministic result is kept on every route.

### Inferred preconditions are errors by default: `on_inferred=` (#655)

A precondition sverify infers to rule out a runtime error (`amount * 2` needs
`_.amount < 2**62`, `total // qty` needs `_.qty != 0`) is no longer assumed
silently, since checking it on the data refuses batches the user never asked
to refuse. `sv.verify` and `sv.transform` take `on_inferred=`:

- `"error"` (the default): the plan is not proved without it. The report
  lists each one under `needs:` (`Report.needed`) with where it came from and
  the fixes: declare it in `requires` (each run then checks it on the data),
  or rewrite so no row needs it (filter those rows first, or a CASE). A
  transform raises `VerificationError`, and `Report.run` and `refresh` refuse
  the plan with the same text.
- `"warn"`: assumed and checked on the data as before, with an
  `InferredPreconditionWarning` naming each one.
- `"silent"`: assumed and checked as before.

`infer=False` still turns inference off: an overflow is then an error whose
hint names the bound. Declared `requires` are checked on the data as before.
`SUM`s assumed to fit and double operations assumed to stay finite
(`Report.assumed`) are not inferred preconditions and keep their run-time
checks.

### Route classes: exact, observed, shim, refused (#655)

A route's class (`Route.cls`) is one of four: `exact` (every result the
engine gives is one the reference allows; was `refines`), `observed` (equal
to one up to an observation; was `refines_up_to` and `approx`, since a
tolerance is an observation of doubles), `shim` and `refused`. An observed
route keeps the observation in `Route.observation` (its components, and the
tolerance the plan's bound gives) and whether that bound is proved in
`Route.bound_proved`. Messages and docs say "observation" where they said
`q`; sverify reads a choices row's `"observation"` and `"rerun_observation"`
keys, and still the checker's `"q"` and `"rerun"`. `docs/realizability.md`
labels its cases the same way.

### Doubles into a sink work without extra settings (#655)

A sink's `reproducible` now defaults to rows as a multiset, doubles within
the bound the checker proves for the plan (`Report.epsilon`), and other
values exact: `sv.equivalent(floats="plan")`, the new `floats="plan"`
level. A run whose `ensures` names no observation checks the engine against
the same default, except in the double columns a proved postcondition
reads, which keep their exact value. So a mean into a `DeltaSink` refreshes
on DuckDB and Polars with no `reproducible=` and no `ensures`. A sink whose
consumers need the same bits on a rerun states `reproducible=sv.equivalent()`.
A refusal over a tolerance names the smallest one that passes.

### Suggestions that make a plan verify (#655)

- A postcondition that fails only where a column is NULL (`TRUE or NULL`)
  gets an `IS NOT NULL` precondition on the input column it reads
  (`length(s) >= 0` needs `_.s.notnull()`), inferred and reported under
  `on_inferred` like a bound: listed under `needs:` by default, assumed with
  `"warn"` or `"silent"`. A postcondition that may also be FALSE no longer
  gets the NOT NULL advice.
- A result not determined up to row order names the `sv.unique(...)` that
  determines it, the partition (or grouping) and order columns of its
  windows and ordered aggregates (`Report.ties`); a route refused for a rerun
  carries it in `Route.suggested` and its message.
- A route refused because the plan's bound on doubles exceeds a stated
  tolerance (in `ensures` or `reproducible=`) names the `sv.max_rows(N)`
  under which it fits, the bound growing linearly with the rows, or says
  that no row cap does (`Route.suggested`).

### Unproved plans no longer run silently (#655)

`Report.run`, `Node.refresh` and a group's `refresh` refuse a plan whose
report is not proved, with what was not proved in the user's terms:
`refused on duckdb: not verified: may fail: domain error: sum(x) (see
report.errors)` (`sverify.errors.RouteError`). `unverified=True` runs it
anyway and says so: an `UnverifiedRunWarning`, the route `"unverified"` in
`Report.routes` or `StageRefresh.route`, and `sverify.verified: false` in
the result's schema metadata. `route="auto"` is the default: every run
chooses how its proof reaches the engine (`sverify.routes.choose`), and
`route=None` is gone.

### A verified plan for any Substrait consumer

`report.to_substrait(format="json" | "binary")` returns the verified plan for
any conforming consumer of Substrait 0.106, with each option the proof
depends on pinned in the plan, and its contract (`requires`, declared,
inferred and assumed, and `ensures`, with a manifest) as metadata in the
plan's `advanced_extensions`. `shims="apply" | "annotate" | "refuse"`
decides what happens at a spec gap: rewrite it into well-specified
Substrait, ship it as an assumption, or refuse. `sv.from_substrait` reads an
export back and proves its contract again; `report.substrait_contract()`
gives the contract as JSON for a sidecar, and `sverify.errors.ExportError`
names the gap a refusal meets
([#664](https://github.com/AlexanderNenninger/substrait-lean/issues/664),
[docs/guide.md](docs/guide.md#exporting-to-substrait)).

### Proved file pruning: Iceberg, string bounds, NaN and implied predicates

`IcebergSource` takes `where=` as `DeltaSource` does: the source is the rows
on which the condition is TRUE, and snapshots, native scans and appends read
only the data files whose statistics do not rule it out. Both sources now
also skip files by string bounds, which Delta and Iceberg may cut to
prefixes, for `=`, `<`, `<=`, `>`, `>=` and `IN` of a string column and a
literal. `SubstraitLean/Pruning.lean` proves the criterion against the exact
statistics semantics, with NULL counts, NaN left out of double bounds and
truncated string bounds, and that every plan linear in the source gives the
same result from the files kept (`Rel.eval_pruned`). For `amount * 2 > 100`,
pyarrow's statistics pushdown reads every file and sverify skips those with
`amount <= 50` (`test_iceberg_where_skips_files_the_reader_would_scan`).

A node now also prunes from predicates its view implies on a source and the
query does not state. With `o.ts >= c.since` in a join of orders and
customers, and `since >= DATE '2026-01-01'` among the customers'
preconditions, the orders source reads only orders from 2026 on and skips
older files. Lean derives the predicate from the preconditions, Delta CHECK
constraints and source conditions, and proves that the view's result is the
same (`Rel.need_eval` in `SubstraitLean/Implied.lean`). `Report.implied`
lists the predicates a transformation implies on its inputs
([#81](https://github.com/AlexanderNenninger/substrait-lean/issues/81)).

### Per-expression guard elimination

Guard elimination dropped the run-time checks of a whole plan or none of
them (`Report.guard_free`). A report now lists the expressions that cannot
raise on data that meets the preconditions, `Report.unchecked`, and
`to_sql(plan, dialect, unchecked=report.unchecked)` leaves out only their
checks: in `SELECT a // b, a * b` with `b >= 1`, the division loses its
`CASE` and the product keeps its overflow check. `Rel.evalG_marks` in
`SubstraitLean/Guards.lean` proves the result unchanged
([#83](https://github.com/AlexanderNenninger/substrait-lean/issues/83)).

### The chaos suite fails again on the signatures of #515, #516 and #517

Their fixes are on main, so `python/tests/chaos/known.json` no longer lists them, and a scenario that hits one again fails the run.

### A crash-injection suite for pipeline execution

`python/tests/chaos/` fails refreshes on purpose: an exception or a SIGKILL at
each step of a refresh (reading a source, the engine, the pipeline's state,
the cursors, a Delta or Iceberg sink before, during and after its commit),
an object store that goes away and comes back, sources that change or
vanish mid-refresh, and two processes racing on one sink. After each, the
same process or a fresh one refreshes, and every sink must equal a full
recompute of its inputs, with its epoch the sum of the versions it records.
Each failed scenario streams a record to a JSONL ledger, and
`python -m sverify_dev.chaos summarize` groups the failures by signature.
`poe test-chaos` runs it; `qa` and CI leave it out. It found
[#515](https://github.com/AlexanderNenninger/substrait-lean/issues/515),
[#516](https://github.com/AlexanderNenninger/substrait-lean/issues/516) and
[#517](https://github.com/AlexanderNenninger/substrait-lean/issues/517).

### Examples and searchable ledgers on the docs site

The docs site has two new sections. Examples
([docs/examples.md](docs/examples.md)) shows sverify's features in eight short
steps: a contract proved and run, SQL through `sv.verify`, inferred
preconditions refusing a bad batch before the run, routes to Polars and their
classes, doubles within a tolerance, a reproducible sink kept up to date,
a plan checked under DuckDB's profile, and Substrait's own semantics. Ledgers
renders the upstream ledger (bugs and Substrait spec gaps), DuckDB's and
Polars's characterization facts, the checklist's coverage per engine and the
realizability table from their JSON at build time, one anchor per entry, so
the site's search finds an entry by id, engine, function, option or text, and
the ledgers' index filters them. The README and the tour's notebooks describe
routes, observations, reproducible sinks, the inputs checked before a run and
the stricter reference.

### No more hangs when DuckDB frees a resident table

A refresh could hang for good in `sverify._duckdb.cursor`: opening a cursor
holds the module's lock, and when the garbage collector ran then, a
resident table's finalizer (`forget`) waited on the same lock. The lock is
now reentrant, and `collect` keeps what a finalizer queues while it runs
(`tests/test_duckdb_lock.py`).

### `homelab_qa.sh` takes its worker count, niceness and directory prefix from the environment

`PYTEST_XDIST_AUTO_NUM_WORKERS`, `HOMELAB_QA_NICE`, `HOMELAB_QA_PREFIX` and `HOMELAB_QA_CHECK_GENERATED` override the defaults (6, 10, `substrait-lean`, true). The Lean build and the tests run in separate memory scopes, the build's capped by `HOMELAB_QA_BUILD_MEMORY_MAX`, so the background chaos run can build at 8 GB and test at 2 GB beside one QA run.

### Notebook 5 no longer pins SQLGlot

`05_pipelines_and_engines.py` pinned `sqlglot==30.27.0`, which conflicts with
sverify's `sqlglot~=30.17.0` from PyPI, so the notebook couldn't be published
for 0.4.0. It now takes SQLGlot from sverify.

### `power(-inf, y)` raises for a fractional `y`

`power(-inf, y)` for a finite `y` that is not an integer is now a domain
error of the reference, as `power(-8, 0.5)` already was. IEEE 754 gives `+inf`
(`y > 0`) or `0` (`y < 0`), as DuckDB does, but Polars's `** 0.5` gives NaN;
raising lets every engine run a verified plan without a shim. A plan that may
meet it is reported as a possible domain error, ruled out by a precondition
such as `x > float("-inf")` on the base. Integer exponents keep IEEE's value
(fact `duckdb-R15-power-neginf`). Per D17, this changes the reference and
ships in a minor version bump.

### DuckDB's statistical aggregates are proved

DuckDB's `VAR_*`, `STDDEV_*`, `COVAR_*` and `CORR` (Welford's update with
Chan's merge) are proved to have the properties the reference allows, so
their `stat_algo` row rests on a proof
([#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444),
[docs/float-bounds.md](docs/float-bounds.md)). Polars's stay tested.

### Tie order is open in the reference

The reference that plans are verified under leaves the order of ties open
(`tie_order`, `tie_pick`); the deterministic profile fixes it (D24,
[#679](https://github.com/AlexanderNenninger/substrait-lean/issues/679)).
`verify` proves postconditions and keys over every order of the ties: a
postcondition over a window, `first()`, `group_concat()` or a `LIMIT` over
ties is proved when it holds for every order, where the report used to say
`undetermined`. `Report.tie_places` names each window, ordered aggregate and
`LIMIT` whose order is not total.

### Reports as data for tools built on sverify

What sverify-dbt, a package that checks dbt projects with sverify, needed
from the public API
([#177](https://github.com/AlexanderNenninger/substrait-lean/issues/177);
the gaps left open are [#699](https://github.com/AlexanderNenninger/substrait-lean/issues/699) to [#710](https://github.com/AlexanderNenninger/substrait-lean/issues/710)):

- `sverify.errors.Unsupported` is the one class every refusal raises: the
  SQL lift's and the Ibis producer's, the SQL writer's and the Polars
  translator's derive from it. `sverify.engines.Unsupported` is the same
  class; before, `verify`'s refusals of SQL escaped
  `except sverify.engines.Unsupported`.
- `Report.needs` lists the preconditions `on_inferred="error"` needs as
  `Needed` records: table, column, comparison, bound, the condition as SQL
  and as the Python `requires` takes (`code`, `_.qty != 0`), and the
  runtime error each rules out.
- `CheckedCondition.reason` says why a postcondition is not proved, as a
  code (`"not_a_key"`, `"may_be_false"`, `"may_be_null"`, `"ties"`, …), and
  `CheckedCondition.condition` is the condition as it was given.
- `verify(tables=...)` takes DuckDB's type names (`{"id": "BIGINT", "name":
  "VARCHAR NOT NULL"}`) beside Ibis's.
- The SQL lift reads `IS [NOT] TRUE` and `IS [NOT] FALSE`.
- The checker's pipes close when it stops, so a script no longer ends with
  a `ResourceWarning`.

### Deterministic runs name the open ties

`choose(deterministic=True)`, an incremental refresh and a sink's
`reproducible=` ask for the deterministic profile (D24,
[#679](https://github.com/AlexanderNenninger/substrait-lean/issues/679)). A
plan whose ties stay open is refused there, and the reason names each window,
ordered aggregate or `LIMIT` (`Report.tie_places`). Without them the plan
runs with the engine's own order of the ties, which every proof covers. The
catalogue accepts any order the reference allows (`substrait-check
--eval-choices`, `sverify.testing.lean_choices` and `allows_rows`), so
`iot-downsample` and `pa-string-agg` match on DuckDB without `tie_order`.

### Reading a contract's proof without running it

For tools that read a proof, such as an editor, a CI step or dbt
([guide](docs/guide.md#checking-without-running), #682):

- `ContractedTransform.check(**schemas)` proves a transform's contract for
  input schemas and returns the `Report`. It raises no `VerificationError`
  and reads no data. `sv.ContractedTransform` is exported, the type
  `@sv.transform` returns.
- `Report.route(engine)` gives the route a run would take and the plan's
  class there (exact, observed, shim or refused), without running it.
- `Report.inputs` gives the schemas of the input tables.
- `CheckedCondition.message`, `Issue.message`, `Issue.assumption` and
  `Report.notes` give the lines `str(report)` prints.
- `Issue.suggested` gives the preconditions that rule an issue out, per
  table, as data.
- The `SVERIFY_COUNTEREXAMPLES` environment variable sets the counterexample
  budget of `sv.verify`, transform calls and `check`; 0 skips the search.
  The default stays 200.

### One model for doubles; every route has a class

Stating no observation, `sv.equivalent(floats="plan")` and the plan's own
bound are one observation (#689). `report.observation` prints it with the
bound, `equivalent(floats=plan, ≤ 2.2e-10)`, and `report.observation.equal`
compares doubles within it. A postcondition that reads a double keeps its
exact value under a stated `floats="plan"` as it does without one.

`verify` checks a stated tolerance (`abs`, `rel` or `ulps`) and
`floats="exact"` against the plan's bound on each engine
(`report.floats_on`). The report's `observes:` line shows the plan's bound
beside the tolerance and the engines that meet it; where none does, the plan
is not proved and the line gives the reason and a tolerance that would do.
A run used to refuse a too-tight `rel` or `ulps` only at run time.

A route prints `rows='multiset'` for a plan with no `ORDER BY`, and the
Substrait manifest's `class` is `observed` for a plan with a bound on its
doubles, as its routes are. `Observation`'s repr is its `equivalent(...)`
form.

Every verified run records one of the four classes in `Route.cls`: a plan
whose options have no row in the engine's tables, such as a `LAG` over a
unique key, is `exact` on tested evidence (#696).

### Docs: Ibis `//` floors and `%` truncates, and a hint for the pair

The guide has a section, "Integer division in Ibis and SQL", with the quotient and remainder of `-7` under each front end and semantics ([#693](https://github.com/AlexanderNenninger/substrait-lean/issues/693)). A report carries a hint when one plan uses Ibis `//` and `%` on the same operands, since `q * d + r == x` fails for negative `x`. Ten wrong statements and gaps in the README, `docs/` and the `Contract` docstring are fixed ([#698](https://github.com/AlexanderNenninger/substrait-lean/issues/698)).

### `MIN` and `MAX` of doubles run on Polars

`MIN` and `MAX` of doubles, as aggregates and as window functions, run on
Polars by `route="auto"` ([#697](https://github.com/AlexanderNenninger/substrait-lean/issues/697)).
Polars's `min` and `max` skip NaN and may keep either zero
([polars-min-max-nan](characterization/polars/facts/polars-min-max-nan.json),
[polars-min-max-zero](characterization/polars/facts/polars-min-max-zero.json)):
the translation gives `MAX` of a group with a NaN as NaN, the greatest double,
and reads both results with one zero. The shim `max_nan_greatest` and
`Polars.min_ignore_nan` are proved in `SubstraitLean/PolarsShims.lean`, and
the route's class is `shim`.

### Ranks need no key, and keys pass through joins

`RANK`, `DENSE_RANK`, `PERCENT_RANK` and `CUME_DIST` give tied rows the same
value, so a window of them is deterministic without a key on its order
(`window_tieFree`).

Columns that an inner join's condition or a filter's equality ties together
count as one column for keys (`KeyOn.eqVariants`,
[#694](https://github.com/AlexanderNenninger/substrait-lean/issues/694)).
After `p JOIN customers c ON c.customer_id = p.customer_id`, a key on
`p.customer_id` is a key on `c.customer_id` too, so a dbt model that projects
the dimension's column proves `unique(customer_id)`, and a window ordered by
`revenue DESC, c.customer_id` is determined. A left join's right copy stays
out: its unmatched rows hold NULL there.

Both come from the API critique
([#686](https://github.com/AlexanderNenninger/substrait-lean/pull/686),
[#679](https://github.com/AlexanderNenninger/substrait-lean/issues/679)).

### Reports and exceptions in your terms, hints a proof has checked

- A report names each issue by the expression you wrote: Ibis's `//` is one
  issue, `(price - cost) * 100 // price`, where it was ten about the
  reference's rewrite of it; a column computed on the way has its name
  (`ts - lag(ts)`, `sum(amount)`, `mean(temp_c) or std(temp_c)`), never a
  position like `$1`; a cast reads `CAST(amount AS DECIMAL(10, 2))`, an
  interval `ibis.interval(minutes=5)`, and conditions print `datetime(9999, 1,
  1)` where they printed `datetime.datetime(9999, 1, 1, 0, 0)`
  ([#687](https://github.com/AlexanderNenninger/substrait-lean/issues/687)).
- A report's first line is its verdict, `proved` or `NOT proved:` with what
  is missing, counted (`Report.verdict`). A `VerificationError`'s message is
  that count, then one line per finding with its hint, each hint once; the
  full report is `e.report`.
- Route lines lead with the class, in words: `shim (integer division
  rewritten to truncate); evidence proved`, `observed: doubles within
  abs=2e-07; evidence tested`. `Route.reason` keeps the long form.
- The ties note names functions in your transformation's language, and
  messages say "the checker" or "sverify" where they said "Lean".
- `sv.approx` checks its condition when you call it, an Ibis typing error in
  a condition names the condition (`ensures condition 2, …, does not
  type-check`), and a checker built before a change to the Lean sources
  raises `CheckerVersionError` with the command that rebuilds it.
- Every hint carries code a proof has checked, or there is none
  ([#688](https://github.com/AlexanderNenninger/substrait-lean/issues/688)):
  bounds that rule an overflow out are verified again before they are shown;
  a key is suggested on the input it comes from only where it proves the
  output's key, and a key lost through a join says so; a postcondition that
  fails only on a NULL output suggests allowing it
  (`(_.sd_t >= 0) | _.sd_t.isnull()`); the AND/OR hint fires only on an `&`
  or `|` you wrote; the ties note suggests a `unique(...)` only where it
  determines the result.

### Guarded double arithmetic raises nothing, and keeps its sign

Under `semantics="duckdb"`, `+`, `-`, `*` and `/` of doubles no longer
report a domain error. DuckDB gives NaN for `inf - inf`, `0 * inf` and
`inf / inf`, and the lift writes that NaN as a `CASE` around the
operation. The check now sees that the `CASE` rules the NaN out: a
condition joined with `AND` leaves its `ELSE` branch with alternatives
(`Expr.cstrAlts`), and `x ≠ 0` or `x ≠ ±inf` rule out a NaN case
([#702](https://github.com/AlexanderNenninger/substrait-lean/issues/702)).
A query's own `CASE WHEN x <> 0 AND y <> 0 THEN x * y END` benefits too.

A sum or product of non-negative doubles, and a quotient of one by a
positive one, is proved at least `0`: rounding keeps the sign. `x * y` of
`x, y ≥ 0` used to be bounded below by `-8.9e-16`, so `SUM(qty * price) >= 0`
was not proved. The three facts this rests on are proved in
`float-bounds/` ([#441](https://github.com/AlexanderNenninger/substrait-lean/issues/441)).

### The SQL lift reads md5 and sha256

DuckDB SQL with `md5(s)` or `sha256(s)` is lifted as the digests the Ibis
producer already wrote for `hexdigest`, where it used to be refused. A
dbt surrogate key from `dbt_utils.generate_surrogate_key` now verifies, and
its `not_null` test is proved
([#725](https://github.com/AlexanderNenninger/substrait-lean/issues/725)).

## 0.4.0 (2026-11-03)

### Breaking changes

Upgrading from 0.3.0, check these first. Each has its own entry below.

- `sv.sql(query)` uses the reference semantics by default, as `sv.verify` and
  `@sv.transform` do (#411). Write `sv.sql(query, semantics="duckdb")` where
  you relied on DuckDB's NaN and `±inf`.
- SQL strings are DuckDB's SQL, read by sverify's own lift. DataFusion's SQL
  planner (#211) and Isthmus (#253) are gone as frontends:
  `sverify.engines.isthmus_json`, `sverify.engines.SQL_PRODUCERS`,
  `sv.connect(sql_producer=...)`, `SVERIFY_ISTHMUS` and `sverify.engine.to_sql`
  are removed. In DuckDB's SQL `7 / 2` is 3.5; write `7 // 2` for integer
  division. `sverify.engines.to_sql` writes SQL from a checked plan.
- `@sv.transform(strict=True)` is `@sv.transform(infer=False)`, and
  `ContractedTransform.strict` is `.infer`, with the opposite truth value
  (#409). `strict=` still works and warns.
- `sv.references(col, table, other)` is
  `sv.references(col, to=other_table.other)` (#412). The positional form still
  works and warns.
- `Connection.datafusion` is deprecated and warns (#413). Run DataFusion
  through `engine="datafusion"`.
- Integer overflow at the declared width is an error that makes a report
  unproved, where it was a warning (#202). Inferred bounds (#244) discharge
  most of it; for the rest, the report's hint names the bound to add to
  `requires`. An integer `SUM` that may overflow is listed in
  `Report.assumed` and checked on the data.
- A double divided by zero raises (#204), and no operation creates a NaN
  (#257): `verify` reports both unless the plan rules them out. Bound the
  divisor or the operands in `requires`, or filter.
- Strings have fewer than 2³² characters, and `substring` with an offset or
  length outside that range is an error (#336). `verify` reports it for a
  column offset unless `requires` bounds it, for example
  `_.start >= -2**32` and `_.start < 2**32`.
- Arithmetic on `FLOAT` (fp32) is refused (#208); cast to `DOUBLE` first.
- No wheels for Intel macOS. There pip and uv build sverify from the sdist,
  which needs [elan](https://github.com/leanprover/elan).
- The maintainer tooling (`sverify.coverage`, `sverify.catalogue`,
  `sverify.fuzz`, `sverify.duckdb_fuzz`, `sverify.slt`, `sverify.examples`)
  is no longer in the wheel.

### DuckDB writes Delta and Iceberg sinks

When a node runs on DuckDB, its `DeltaSink` and `IcebergSink` have DuckDB
write the Parquet files, and sverify commits them with the contract and the
epoch, exactly once as before. The state and the rows never pass through
Python. A Delta change rewrites only the files that hold deleted rows and
adds a file of the new rows, in one commit with delta-rs's statistics; an
Iceberg change is a data file with field ids and a position delete file.
Other engines, partitioned or remote tables, and an overwrite by another
plan write through delta-rs and pyiceberg as before.

A Delta sink no longer mistakes its own constraint for a foreign one when the
node's guarantee has a decimal number: Delta stores `x >= 0.0` as `x >= 0`
(#173).

### Incremental views keep their state in DuckDB

On DuckDB, an incremental view's state no longer lives in Python: DuckDB
holds it between refreshes, and the view's rows are a DuckDB view of it. On
every engine, states and changes are added up by one plan Lean checks (a
union, grouped by every column, with the weights summed), so they group rows
as the model compares them: one NaN, `-0.0` equal to `0.0`, lists by their
elements. Sinks compute their change with the same plan (#173).

A view's rows, and what a sink writes, come in no particular order, as a
SQL query's do; before, they kept the order in which rows first appeared.

### Refreshes on DuckDB cost what changed

On DuckDB, a refresh no longer rebuilds a view's whole state. The merge plan
adds the change to the state rows it touches, and DuckDB replaces those rows
in place, in one transaction for every view: a refresh that changes ten rows
of a view of ten million costs about ten rows. Sinks write the sum of the
view's changes since the state they wrote. A view whose new contents a
recomputed view or `refresh(audit=True)` reads first is still merged in full
(#173).

### Delta and Iceberg tables read natively by DuckDB

On DuckDB, a `DeltaSource` or `IcebergSource` is no longer loaded into
Python. The pipeline holds the Parquet files of the table's version, chosen
by sverify's own pruning (#81, #108), with the rows that deletion vectors or
position delete files remove, and DuckDB reads them with `read_parquet`.
Refreshes keep the table as the files of the new version. Partitioned tables,
Delta column mapping, renamed Iceberg columns, equality deletes, object
stores and the other engines read through Arrow as before.
`scripts/bench_io.py` measures reading, refreshing and writing at scale (#173).

### The reference is a relation: an engine returns an allowed result or raises

`docs/reference-semantics.md` now defines correctness through the set of
results the reference allows for each input (`Rel.Allowed`,
`core/Sverify/Core/Allowed.lean`). The set holds more than one result where the
reference leaves a choice to the engine: the order of rows and of ties,
`FIRST`/`LAST` and `distinct(on=)` without an order, the order in which a double
`SUM` or `AVG` adds (#85), and the statistical aggregates. `Rel.eval` is one
allowed result (`Rel.eval_allowed`); a plan without choices allows only its
rows (`Rel.allowed_perm_eval`); rewrites are refinements (`Rel.Refines`); and
the DuckDB shim and guard elimination return allowed results. The page also
lists where the reference overrides Substrait (one zero, one NaN, the size
hypothesis), states principle 3 as "Every engine can follow it with reasonable
effort", and notes that `fp32` arithmetic is refused until #417.

### Integer overflow is an error at the declared width

Breaking: `+`, `-`, `*` and negation of integers whose result does not fit
its declared type (`BIGINT`, or `INTEGER`, `SMALLINT`, `TINYINT`) raise, on
every engine, where a plan omits `overflow` or asks for `ERROR` (#202). An
overflow `verify` cannot rule out makes the report unproved; it was a "may
wrap around" warning. Inferred bounds (#244) discharge most of these, and the
report's hint names the bound to add to `requires` for the rest. The
arithmetic sverify adds itself (0-based `row_number`, `find`, floor
division) is proved free of overflow, under the hypothesis that a window
reads fewer than 2⁶² rows (#254).

### An integer `SUM` that may overflow is an assumption checked on the data

`verify` no longer treats a possible integer `SUM` overflow as a warning. Where
the plan bounds a group's rows (a `VALUES` list, a `FETCH` count, an aggregate
without groups) and `requires` bounds the column, the overflow is ruled out.
Elsewhere sverify assumes each sum fits 64 bits, as it assumes inferred bounds
(#244), and lists it in `Report.assumed`; the SQL it writes checks it on the
data while the job runs. With `infer=False` it is an error that makes the
report unproved. A row cap (`sv.max_rows`, #219) discharges it statically. A
window `SUM` or `AVG` whose frame may hold both `+inf` and `-inf` is now
reported as a domain error, as the grouped one is (#257).

### A double divided by zero raises

`x / y` and `x % y` on doubles raise on a zero divisor, as on integers, when
the plan omits `on_division_by_zero` or asks for `ERROR` (#204). `verify`
reports "division by zero" unless the plan rules it out (`y > 0` in
`requires`, a filter, `NULLIF(y, 0)` or `CASE WHEN y <> 0`). A plan that asks
for `IEEE`, `LIMIT` or `NULL` gets that. Under `semantics="duckdb"`, SQL
divides as DuckDB does, giving `±inf` or NaN.

### Fixed: aggregates of double constants, casts between dates and timestamps

The reference computed two kinds of plans wrongly (#201). An aggregate of a
double constant read the constant as an integer: `SUM(CAST('inf' AS
DOUBLE))` is now `inf`, and `avg(42) OVER ()` is `42.0` (#205). A cast
between a date and a timestamp kept the number of days or microseconds: a
date now becomes midnight of that day, and a timestamp rounds down to its
day, before 1970 too. A comparison of a date with a timestamp without a cast
is refused (#206).

### Lists compare element by element

`<`, `>`, `ORDER BY`, `MIN` and `MAX` on lists order them lexicographically,
a proper prefix first (#207). A NULL element that decides a comparison makes
it NULL (`[1, NULL] < [1, 3]`); in `ORDER BY`, `MIN` and `MAX` NULL elements
sort after every other value
([reference semantics](../docs/reference-semantics.md)).

### Arithmetic on `FLOAT` (fp32) is refused

The reference computed `FLOAT` arithmetic in doubles, so `2e38::FLOAT / 0.1`
gave `2e39` where every engine gives `inf`. Arithmetic on `FLOAT`s and casts
to `FLOAT` are refused until binary32 is modelled (#208, #417). Reading a
`FLOAT` column, comparing it and widening it to `DOUBLE` are exact and keep
working; cast to `DOUBLE` first to compute with it.

### `avg` of integers follows the plan's output type

An `avg` of integers whose plan declares an integer result, as Substrait's
`avg` of `i64` does, is the exact mean truncated toward zero; a declared
`fp64` result is the mean as a double (#209). Other output types are refused.

### `substring` counts a negative start from the end

A plan that omits `negative_start` counts a negative start from the end of
the string, as DuckDB does: `substring('hello', -2, 2)` is `'lo'` (#209).
A plan that asks for `LEFT_OF_BEGINNING` gets that, and `ERROR` is refused.
The SQL writers and Polars rewrite the start before calling the engine's
`substring`.

### SQL strings are DuckDB's SQL, through sverify's own lift

`sv.sql`, `sv.verify` of a SQL string, SQL conditions in contracts, Ibis's
`Table.sql` and `Backend.sql`, and `sverify.engines.substrait_json` now read
**DuckDB's SQL** and plan it with sverify's own SQLGlot lift
(`sverify.sql_lift`, #239). DataFusion's SQL planner is gone as a frontend
(#211); DataFusion stays an execution backend (`engine="datafusion"`), and SQL
strings no longer need the `datafusion` extra.

This changes what some SQL means. In DuckDB's SQL, `/` divides as doubles
(`7 / 2` is 3.5; integer division is `//`), `1.5` is a `DECIMAL(2, 1)` rather
than a double, and NULLs sort last in both directions. A double divided by
zero raises under the reference semantics, the default (#411), and is `±inf`
or NaN with `semantics="duckdb"`. The entries for #240 list what the lift
reads; anything else is refused, saying what. Write those queries in Ibis
meanwhile.

### Row caps prove integer SUMs fit

A row cap `sv.max_rows(n)` in `requires` now proves integer `SUM`s fit 64
bits (#219): a `SUM` of values in `[-m, m]` over at most `n` rows, with
`n · m < 2⁶³`, is no longer an assumption checked on the data
(`Report.assumed`). Lean carries the caps through filters, unions, limits,
aggregates and joins. A join on a `unique` key of its right side keeps the
left side's rows (`Rel.capJoins_eval`), where a product would be far too
large. Caps are now:
- proved from the record counts of a Delta or Iceberg table's files;
- checked on every batch of an incremental view;
- proved in `ensures`.

`Report.rows` bounds the output's rows, and the SUM hint names the cap that
proves a sum fits.

### Casts between doubles, decimals and integers keep their bounds

- `CAST(x AS DECIMAL(p, s))` of a double whose bounds are known no longer
  reports a failed cast or a precision overflow when the casts of the bounds
  fit: after `WHERE f BETWEEN 0 AND 100`, `CAST(f AS DECIMAL(10, 2))` is safe
  (#223).
- `CAST(d AS DOUBLE)` of a decimal keeps the decimal's bounds, as
  `CAST(n AS DOUBLE)` of an integer already does. TPC-H Q08's contract is now
  proved, and Q14's division can no longer be by zero.
- The reference computes these conversions exactly (the nearest double,
  halves to even; `round(x · 10ˢ)` in doubles for the cast to a decimal) and
  states what they keep: monotone, within `2⁻⁵³` relatively, exact for
  integers up to `2⁵³`, which survive the round trip to a double and back.

### Benchmark catalogue refreshed for 0.4.0

The catalogue's 54 benchmark queries were probed again on 0.4.0. 53 are accepted and 53 now have a contract, of which 46 are proved and 49 run as verified SQL on DuckDB (#229). New contracts: TPC-DS q27 and q36 (ROLLUP lifts since #306) and H2O groupby q9 (`corr`). A query written in SQL now states its contract as SQL conditions.

TPC-H q11, q14 and q20 state row caps from the specification's largest scale factor. Each query still short of proved or verified SQL says why in its TOML, with the issue that would close it: SUMs bounded by row caps (#470), RANK over a ROLLUP (#471), keys through a FULL JOIN (#472) and ROW_NUMBER filters projected past their ties (#473).

### The SQL written for DuckDB is proved to return the reference's rows or raise

`Rel.duckdb_shim_sound` (`core/Sverify/Core/Profile.lean`) proves that DuckDB,
running the SQL sverify writes, returns `Rel.eval`'s rows or raises, for any
plan, with no contract needed (#185). Engine profiles state what DuckDB
computes for each function, and where it differs from the reference the
written SQL compensates ([engine profiles](../docs/engine-profiles.md)). The
query catalogue records, for each benchmark query, whether it is verified SQL
on DuckDB (`verified_sql` in [`catalogue/INDEX.md`](../catalogue/INDEX.md),
#229).

### Plans with `NOT IN` subqueries and decimals are written

A plan with DECIMAL arithmetic is written for the engines only if it reads
back as the same plan. A `NOT IN (subquery)`, or a `CASE` of several
branches, grew on every reading, so such a plan stopped at "this decimal
arithmetic cannot be written for the engines yet" (#238, TPC-H Q16's
shape). It is written now.

### `AVG` of a DECIMAL as a double

DuckDB SQL that averages a DECIMAL column, such as TPC-H Q1's
`avg(l_quantity)`, is now verified. DuckDB returns a DOUBLE, and so does
the plan: the exact sum, converted to a double, divided by the count. NULL
without values. Over windows it is still refused.

### Plans with decimals and a negated double are written

A plan with DECIMAL arithmetic is written for the engines only if it reads
back as the same plan. Negating a double, or taking its `ABS`, broke that,
so such plans (TPC-DS q89, for one) stopped at "this decimal arithmetic
cannot be written for the engines yet". They are written now.

### The SQL lift reads dates and timestamps

The SQL lift now reads dates and timestamps (#240): `EXTRACT`, `date_part`,
`year()` and its kin, `DATE - DATE`, `datediff('day', …)`, `date_trunc` of
a date, and a date or timestamp plus or minus a constant interval. Adding
months clamps to the month's last day, as in DuckDB. DuckDB types
`DATE ± INTERVAL` and `date_trunc` of a date as TIMESTAMPs. They compare
exactly with dates, but as an output column or next to a timestamp column
they need a cast of a date column to a timestamp the model lacks yet, and
are refused.

### The SQL lift reads GROUPING SETS, ROLLUP and CUBE

The SQL lift now reads `GROUP BY` with `GROUPING SETS`, `ROLLUP` and `CUBE`, alone or next to plain keys, and `GROUPING(…)` in the select list, HAVING, ORDER BY and window functions (#240). Each grouping set becomes its own aggregate, with NULL for the keys the set leaves out and the value of each `GROUPING(…)` as a constant. The aggregates are joined with `UNION ALL`, as DuckDB computes them. On empty input, the empty set's grand-total row is kept.

Two fixes came with it:
- A window function's `PARTITION BY` and `ORDER BY` may now be expressions, not only columns. The plan computes them as columns first, since the model reads them as columns.
- In an `ORDER BY` expression, a bare name is the output column of that name, as in DuckDB. For example, `ORDER BY CASE WHEN s > 0 THEN customer END` where `s` is an alias.

TPC-DS q27 and q36 now pass: 51 of 54 benchmark queries agree.

### The SQL lift refuses joins it would have read wrongly

The sqllogictest replay found queries the SQL lift read wrongly (#240). It now refuses them instead:
- **`ASOF JOIN` and `POSITIONAL JOIN`:** the lift read these as the inner join of their `ON`, or as a cross join. An ASOF join keeps each left row's latest match; a POSITIONAL join pairs rows by position.
- **`t.*` with `JOIN … USING`:** SQLGlot leaves the `USING` columns out of the right table's `t.*`, where DuckDB keeps them. `SELECT *` and listed columns still work.
- **Ordering comparisons (`<`, `<=`, `>`, `>=`) of structs:** DuckDB orders them field by field, with NULLs last, and the model's order differs. Lists still compare as DuckDB's, and equality still works.

Other queries the replay found read wrongly are refused or fixed too:
- **Clauses SQLGlot attaches to a table:** `TABLESAMPLE`, `PIVOT`, and the comma joins of a FROM-first query (`FROM a, b SELECT …`) are now refused. The lift used to read only the table and drop them.
- **Numbers with an underscore not between two digits** (`1__2`, `1._5`): DuckDB reads such an underscore as the start of an alias, SQLGlot as a digit separator (upstream/LEDGER.md SG-4). These are refused.
- **A constant that doesn't fit its cast's type** (`200::TINYINT`, `12.5::DECIMAL(2,1)`): the lift now writes the cast instead of an out-of-range literal. A string read as a decimal is read exactly, so `'1e38'::DECIMAL(38,0)` no longer goes through a double.
- **INTERVAL output columns:** these are refused, because the model holds intervals as microseconds while DuckDB keeps months and days apart.
- **Casts to the `NULL` type:** refused.

### The SQL lift reads numeric functions, DISTINCT and FILTER in aggregates

The SQL lift now reads (#240):
- **Numbers:** `power` (`**`, `pow`), `abs`, `round`, `floor`, `ceil`, `sign`, `isnan`, `greatest`, `least`, `nullif`, and `sqrt`, `exp`, `ln`, `log`, `log2`, `log10`, `sin`, `cos`, `tan`, `asin`, `acos`, `atan`.
- **Comparisons:** `IS [NOT] DISTINCT FROM`.
- **Aggregates:** `DISTINCT` in every aggregate, and `FILTER (WHERE …)`.

They have DuckDB's meanings:
- `power` and the elementary functions compute in doubles;
- `log(x)` is base 10;
- `greatest` and `least` leave NULLs out;
- `sign` is a TINYINT, 0 for NaN;
- `isnan(NULL)` is NULL.

Outside their domain (`sqrt(-1)`, `ln(0)`), DuckDB gives NaN or `-inf`. The plan states that preference and then `ERROR`, the reference's, which the model takes, so `verify` reports such rows as possible errors.

### The SQL lift reads strings

The SQL lift now reads strings (#240): `length`, `substring`/`substr` (from
1; a negative start counts from the end), `trim`/`ltrim`/`rtrim` (spaces,
or the characters given), `strpos`/`instr`/`position`, `contains`,
`starts_with`, `ends_with`, `prefix`, `suffix`, `LIKE`/`ILIKE` and their
`NOT`, `||`, `concat` (which leaves NULLs out), `replace`, `repeat`, `left`,
`upper` and `lower`. A LIKE pattern must be a constant without a backslash:
DuckDB's LIKE has no escape character, and the model's has one. `reverse`
is refused, because DuckDB reverses grapheme clusters.

### The SQL lift reads CTEs, subqueries and more joins

The SQL lift now reads (#240):
- **CTEs:** non-recursive `WITH`, inlined where each is read; a later CTE may read an earlier one.
- **Uncorrelated subqueries:** a scalar subquery (the checker must prove it has at most one row: an aggregate without groups, or `LIMIT 1`), `x [NOT] IN (SELECT …)` with SQL's rules for NULLs, and `EXISTS (…)`.
- **More joins:** `SEMI`, `ANTI`, `RIGHT` and `FULL` joins.

A subquery that reads a column of the query around it (a correlated subquery) is refused, saying so; write it as a join, or as a `SEMI` or `ANTI` join.

### The SQL lift reads window functions

The SQL lift now reads window functions (#240):
- **Ranking:** `row_number`, `rank`, `dense_rank`, `percent_rank`, `cume_dist` and `ntile`.
- **Values:** `lag` and `lead` (a constant offset, and a default), `first_value`, `last_value` and `nth_value`.
- **Aggregates:** `sum`, `avg`, `count`, `min` and `max` over a window, including windows over a query's aggregates (`rank() OVER (ORDER BY sum(x))`).
- **Frames:** `ROWS` and `RANGE` frames with integer offsets, and DuckDB's default frame: to the current row and its peers with an `ORDER BY`, the whole partition without.

`ntile` is DuckDB's, the SQL standard's buckets: 6 rows in 4 tiles are 1 1 2 2 3 4. The lift writes it from `row_number` and `count`, because the model's own `ntile` is DataFusion's. Named windows (`WINDOW w AS …`), `GROUPS` frames, `EXCLUDE`, `IGNORE NULLS` and `DISTINCT` in a window are refused.

### `NTILE` deals out buckets as SQL does

`NTILE(k)` now follows the SQL standard, as DuckDB, Spark and Snowflake
compute it: the first `n % k` buckets hold one row more. It used to follow
DataFusion's formula, which spreads the larger buckets out (`ntile(4)` of
10 rows gave `1 1 1 2 2 3 3 3 4 4`; now `1 1 1 2 2 2 3 3 4 4`). DataFusion
is refused for `NTILE` for now. `verify` still proves `1 ≤ NTILE ≤` the
row's number.

### The DuckDB replay's ledgers come from the SQL lift

`characterization/duckdb/*.json` now record the sqllogictest replay through the SQL lift on `main`, with #338's fixes (#240). Over 121 areas and 46,283 queries: 8,449 agree, 265 disagree, 22,931 refused, 14,638 skipped. The README's summary table is regenerated.

The replay itself:
- logs queries slower than 10 s;
- writes its summary table again: it no longer fails on `probes.json`.

Two lift regressions from #338 are fixed:
- A string read as a decimal rounds half away from zero past the scale, as DuckDB does, instead of being refused.
- A double constant is folded into a decimal where the decimal holds it exactly (`1e1::DECIMAL(38,0)`).

### `AVG` of a DECIMAL over a window as a double

`avg(d) OVER (...)` of a DECIMAL column in DuckDB SQL is now verified, as a
DOUBLE the way DuckDB types it, and arithmetic with it is in doubles (as in
TPC-DS q89's `sum_sales - avg_monthly_sales`).

### DuckDB's SQL writes the proved lowering

Where DuckDB computes a function differently from the reference, the SQL
sverify writes for DuckDB is now the template the Lean build generated and
proved (`substrait-check --lowering-table`, read by `sverify.sql.lowering`):
the guards for NaN and ±inf, the elementary functions' domains, division and
`%` by zero, `MIN % -1`, `<<`, and `overflow` = `SILENT` or `SATURATE`. The
hand-written versions in `sverify.sql.duckdb` are gone. Polars no longer
raises on a shift of NULL by an out-of-range amount, which the reference
leaves NULL (#241).

### Integer overflow can wrap around or clamp when a plan asks

A plan may now set `overflow` to `SILENT` (wrap around) or `SATURATE` (clamp)
on integer `add`, `subtract`, `multiply` and `negate`, at the declared width
(`i8` to `i64`); before, these were refused (#255). Nothing raises for them,
so `verify` reports no overflow. DuckDB runs them in 128-bit arithmetic, with
templates the Lean lowering generator found and proved (`SATURATE`) or a
hand-written, proved schema (`SILENT`); the other engines refuse them for now
([#241](https://github.com/AlexanderNenninger/substrait-lean/issues/241)).

### DuckDB's functions probed for the options they implement

`substrait-check --outcomes` evaluates each row of a projection over `VALUES`
under the reference and prints the value or the error raised. The maintainer
tool `python -m sverify_dev.probe` uses it to run DuckDB's arithmetic and
elementary functions on edge cases under every combination of
`error_on_division_by_zero` and `ieee_floating_point_ops`, and to keep the
Substrait options whose outcomes match
(`characterization/duckdb/probes.json`, FACTS R15). It corrected two facts:
double division by zero is IEEE under DuckDB's defaults, and `MIN % -1`
raises (#242).

### DuckDB's profile says what DuckDB computes, and the lowering compensates

`Profile.duckdb` now states DuckDB 2.0's behaviour where the probes found it
differs from the reference: NaN for operations on doubles that have no value
(`∞ - ∞`, `0 · ∞`, `∞ / ∞`, `sqrt(-1)`), `-∞` for a logarithm of 0, IEEE
division by zero for doubles (`ieee_floating_point_ops`, a new setting),
`atan2(0, 0) = 0`, `MIN % -1` raising, and the shifts. The generated lowering
to DuckDB guards each of them, every guard proved by the kernel, and
`Rel.duckdb_sound` is restated for DuckDB's IEEE mode, with the SQL printer
trusted for `MIN % -1` and `<<`, which it writes out. The lowering generator
keeps its results in `SubstraitLean/LoweringCache.lean`
(`substrait-check --lowering-cache`), so builds try each known template first
(#242).

### Engine facts as JSON documents, with provenance

What DuckDB does, judged against the reference semantics, is now one JSON
document per finding in `characterization/duckdb/facts/`, in the format of
`characterization/fact.schema.json`: the engine version checked, what the
engine and the reference do, a status, and each check's date, method, tool
and evidence (DuckDB's tests at their commit, the replay ledgers, the probe
verdicts of `probes.json`). DataFusion 51's findings from the replay are in
`characterization/datafusion/facts/`. `characterization/<engine>/FACTS.md`
is generated from them by `python -m sverify_dev.facts --write`.

### Inferred bounds against overflow

Contracts no longer have to state the bounds that rule out integer overflow
(#244). For `amount * 2` on a `BIGINT`, sverify infers `_.amount < 2**62`,
proves the contract with it, and treats it as a precondition: it is checked
on the data at call time and on every refresh, or proved from Delta and
Iceberg file statistics, and reports list it as inferred. The inference
covers `+`, `-` and `*` with constants or bounded columns, negation, `abs`,
narrow integers and timestamp truncation (#379), through projections,
filters, joins and `MIN`/`MAX`. Lean proves the contract again with the
inferred bounds, so a wrong inference only fails the proof. Where no single
bound exists (the product of two columns, a `SUM`, a value from another
contracted transformation), the report's `Issue.hint` suggests one.
`@sv.transform(infer=False)` and `sv.verify(..., infer=False)` require
explicit bounds.

### Inferred preconditions for more runtime errors

Sverify now infers preconditions for runtime errors besides integer
overflow, as #244 does for overflow. Each is the weakest per-column
condition, marked "(inferred)", checked on the data or proved from metadata,
and switched off by `infer=False`:
- division and remainder by zero: `(_.b != 0)`;
- domain errors: `sqrt`, logarithms, `asin`/`acos`, a fractional power;
- casts out of range: to narrower integers, and from doubles to `BIGINT`;
- `repeat` counts;
- decimal precision of `+`, `-` and `*`;
- date arithmetic.

Where no single bound exists (`∞ / ∞`, `substring` offsets counted from
either end, the sum of two unbounded decimals), the hint suggests one and
nothing is assumed ([docs/guide.md](docs/guide.md#inferred-bounds)).

### Suggested preconditions for unproved postconditions

An unproved postcondition that compares a value with a constant now comes
with the precondition on the inputs under which it holds: `_.doubled <= 100`
with `doubled = qty * 2` reports "would hold with `(_.qty < 51)` in the
requires of 'items'". Sverify proves each suggestion before showing it and
never assumes one. `CheckedCondition.suggested` and `Report.suggestions`
carry them as code, for editors and language servers (#291).

### Decimals in reports keep their scale

`verify`'s "known about the output" showed a decimal column's bound as its
internal unscaled integer: TPC-H Q6's `revenue` read "an integer ≥ 450000".
It now reads "a decimal(38, 4) ≥ 45.0000", with the column's type (#250).

### Dates: the reference's own range

Date arithmetic is now checked against the reference's dates, the SQL
standard's 0001-01-01 to 9999-12-31, instead of the (much wider) range
DataFusion computes. Adding days or months that leaves them raises "outside
the reference's dates" on every engine, and `verify` reports it. With
constant operands, such as TPC-H Q6's `DATE '1994-01-01' + INTERVAL 1 YEAR`,
the written SQL no longer carries a range check at all (#251).

### More divisors proved non-zero

`verify` now proves a divisor non-zero from more preconditions:
`(b < 0) | (b > 0)`, `(b != 0) | b.isnull()`, and a product `b * c` of
factors each known to be non-zero. Each needed a guard before.

### What DuckDB SQL lifts to is generated and proved

The Lean build now generates, for DuckDB's `/` (of integers and of doubles),
`%` of doubles, `log`, `sign`, `greatest` and `least` (which skip NULLs) and
casts between BIGINT and DOUBLE, and the aggregate `avg` of BIGINTs, the Substrait expression each lifts to under
`semantics="duckdb"` and `"reference"`, and proves it means what DuckDB's
function means (`SubstraitLean/DuckDBSQL.lean`, `LiftSearch.lean`). With
DuckDB's semantics, `±∞` and NaN results are stated exactly, as guarded
constants: `log(0)` is `-∞`, `x % 0.0` is NaN. `substrait-check --lift-table`
prints the table as JSON, for the SQL lift to read; a function the model
cannot state is listed as refused, with the reason (DuckDB's `CAST` of a double
to an integer rounds half to even)
([#268](https://github.com/AlexanderNenninger/substrait-lean/issues/268)).

DuckDB's `avg` of integers sums them exactly before dividing; with DuckDB's
semantics it now lifts to `CAST(sum(x) AS DOUBLE) / count(x)`, proved equal,
where Substrait's `avg` of doubles would round as it sums (values beyond 2⁵³).

### DuckDB's elementary functions and power lift exactly, and the lift has a cache

With `semantics="duckdb"`, `sqrt`, `exp`, `ln`, `log`/`log10`, `log2`, the
trigonometric functions and `power` now lift to what DuckDB computes, NaN and
`±∞` included (`sqrt(-1)` and `asin(2)` are NaN, `ln(0)` is `-∞`, a negative
base to a fractional power is NaN), each proved
([#268](https://github.com/AlexanderNenninger/substrait-lean/issues/268)). The
lift generator keeps a cache of the templates it found
(`SubstraitLean/LiftCache.lean`, regenerated with `substrait-check
--lift-cache`), tried first on the next build: a build with the cache takes
15 s where a search from scratch takes about 3 minutes. A template the search
does not reach can be seeded by hand there; it is still proved by the kernel.

### The SQL lift reads Lean's generated DuckDB lift table

With `semantics="duckdb"`, the SQL lift now writes what Lean's generated lift table says for each construct it covers (#268): `/`, `%` of doubles, `log`, `sign`, `greatest` and `least`, casts between BIGINT and DOUBLE, and `avg` of integers. Lean generates each entry and proves it means what DuckDB computes. `substrait-check --lift-table` exports the table, and the lift reads it from the checker sverify ships with.

The entries state NaN and ±inf exactly, as DuckDB computes them, instead of refusing them or raising:
- `%` of doubles is no longer refused: by zero, or of an infinity, it is NaN.
- `log(0)` is `-inf`, and `log` of a negative is NaN.
- `inf / inf` is NaN.

A contract that NaN or an infinity would break fails to prove, and one they can't break still proves. `avg` of integers is the exact sum divided by the count, in doubles, as DuckDB computes it.

The other constructs keep their hand-written rules until their entries are generated. The reference semantics is unchanged.

### Decimals

`DECIMAL(p, s)` columns, literals and arithmetic are verified, in Ibis and in
SQL (#27, #67). The reference computes them exactly: `+` and `-` at the
larger scale, `*` at the sum of the scales, and an overflow of the precision
is an error, which `verify` rules out from the columns' declared precision.
Casts to a smaller scale round half away from zero, to an integer truncate,
and to and from doubles round once. `SUM`, `MIN`, `MAX` and `AVG` work in
groups and windows; `AVG` is `DECIMAL(p + 4, s + 4)`, rounded half away from
zero. Division of decimals is refused. DuckDB runs decimal plans and
compensates where its own types or rounding differ
([engine profiles](../docs/engine-profiles.md)); Polars, Spark and Snowflake
refuse them for now.

### Chapter 16 of the tour folded into chapter 17

The tour's appendix on DataFusion's quirks (`16_datafusion_semantics.py`)
described DataFusion as the SQL frontend it no longer is (#211). Its parts
that still matter now live in chapter 17 (`17_backend_semantics.py`), as a
new section 8 on DataFusion as a backend: when DataFusion evaluates an
expression (E1–E5), and the soundness gaps found while sverify planned SQL
with DataFusion (D1–D11), each re-checked live against `verify` and the
model and ranked most severe first. Most of those gaps closed with the lift;
what remains is that DataFusion wraps integer overflow silently where the
model raises, which `verify` reports as `may fail: overflow`.
`catalogue/pitfalls.toml`'s `quirks` now name chapter 17's entries.

### DuckDB is the test oracle; the docs describe SQL as DuckDB SQL

The tests check the reference model and the engines against DuckDB, the Tier 1
engine, wherever they used to run raw SQL or Ibis's SQL on DataFusion as an
oracle. DataFusion keeps the tests about it as a backend: checked plans
running on it, and the native behaviours that motivate a refusal.
`sverify.engine.run_sql` (internal) is gone. Raw DuckDB SQL over a
connection's tables is `sverify.testing.duckdb_sql`, and an Ibis expression's
own DuckDB SQL is `sverify.testing.duckdb_ibis`. The coverage harness's
`DATAFUSION_SQL` and `NO_DATAFUSION_SQL` are replaced by one list,
`NO_DUCKDB_SQL`: the cases where DuckDB's own SQL computes something other
than the plan. `sverify.testing.parse_row` is private now (`parse_rows`
stays). The README, `python/README.md`, `docs/reference-semantics.md`, the
tour's chapters 12 and 14 and the agent skills describe SQL as DuckDB SQL,
read by sverify's lift with `semantics="duckdb"` or `"reference"`, and
DataFusion as an optional backend.

### Bounded state for time buckets: `arrives_within` and retention by watermark

`sv.arrives_within("ts", hours=2)` in `requires` bounds how late a source's
rows arrive. It is checked on every batch at refresh: a row before the
watermark (the largest `ts` seen minus the lateness), or a NULL, rejects the
batch. A node that aggregates by `ts.truncate(...)` or `ts.bucket(...)` then
drops the buckets that end at or before the watermark from its state once its
sink has written them, and keeps at most `⌈lateness / width⌉ + 1` open. Lean
proves that a final bucket's delta is empty for every admissible batch and the
bound (`SubstraitLean/Retention.lean`). The refresh report gives the open and
retired buckets and the bound. `DeltaSink` keeps the retired buckets
(`Sink.keeps_retired`); with other sinks the node keeps every bucket (#294).

### The last of DataFusion's SQL path is gone

sverify no longer monkey-patches Ibis's DataFusion SQL compiler: the two
patches (sub-second interval literals, integer `//`) changed Ibis for every
user of Ibis-on-DataFusion and served only the internal
`sverify.engine.to_sql`, which is removed as well. The one `to_sql` left is
`sverify.engines.to_sql`, which writes SQL from a checked plan. The query
catalogue runs each query on DuckDB itself rather than DataFusion
(`status.json` records it as `native`), and no longer asks DataFusion's SQL
planner whether a query plans.

### Integer division overflow at narrow widths

`MIN // -1` at TINYINT, SMALLINT and INTEGER (`-128 // -1` is 128, which a
TINYINT cannot hold) is now reported as an overflow, as it already was for
BIGINT, and the plans sverify writes raise there, as DuckDB does (#334).
Integer division at a narrow width is now checked at that width, like `+`,
`-`, `*` and negation. The sqllogictest replay also sees `verify`'s warnings
for queries that read no table, such as `SELECT 7 // 0` (#333): `verify`
reported those all along, but the replay's check went through
`sverify.sql`, which refuses such queries.

### `round(x, d)` at every number of digits

`round(x, d)` of a double now means what DuckDB computes for every `d`
(#335): below zero it divides by an exact power of ten and multiplies back,
so `round(42.0, -1000)` is 0, not NaN, and `round(521924.889, -5)` is
`500000.0`, not `499999.99999999994`. A result that would not be finite
falls back to 0 (for `d < 0`) or to `x` (for `d ≥ 0`). The plans sverify
writes now include `round` with digits for a double literal, which they
refused before ("unsupported function round/2"). DataFusion rounds
otherwise, so it refuses `round(x, d)` until #271.

### `substring` out of range is an error, and strings have fewer than 2³² characters

- The size hypothesis for strings is now 2³² characters (it was 2⁶²); relations
  a window reads keep 2⁶² rows (#336).
- `substring` with an offset outside `[-2³², 2³²)` or a length of `2³²` or more
  is an error in the reference semantics, as DuckDB raises. `verify` reports it
  as a domain error unless the offset's bounds rule it out, for columns and
  constants alike, and the written plans raise there on DuckDB and Polars. The
  lift no longer refuses such constants.

### GREATEST and LEAST check in linear time

`GREATEST(a, b, c, …)` and `LEAST(…)` used to be read as a chain of conditionals, each of which copied the one before. With ten arguments, the checker ran for minutes, and a plan written back held thousands of copies of each argument (#340). They're now one operation per pair, `BinFn.greatest`/`least`, which `Expr.eval_greatest` proves is the conditional it replaces. Thirty arguments check in well under a second.

The contract checker keeps its precision. `GREATEST(x, 0)` is still known to be at least 0, and Ibis's `clip` to stay within its bounds; `pickAbs` is proved sound. Written plans carry `greatest`/`least` as single calls, run natively:
- DuckDB, Spark and DataFusion: their own `GREATEST`/`LEAST`, which skip NULLs;
- Snowflake: `GREATEST_IGNORE_NULLS`;
- Polars: the same comparison as before, now one step per pair.

Greatest and least of lists are written as the conditional, as before.

### Set operations in SQL

DuckDB SQL with `UNION`, `EXCEPT` and `INTERSECT`, each with or without `ALL`,
now verifies, in subqueries and CTEs too, with `ORDER BY` and `LIMIT` over the
whole operation (#344). The branches meet at DuckDB's common column types, and
take the first branch's names. NULLs count as equal, and with `ALL`, `m` and
`n` copies of a row leave `min(m, n)` (`INTERSECT ALL`) or `max(m − n, 0)`
(`EXCEPT ALL`), as in DuckDB. DuckDB's `TABLE t` shorthand, which SQLGlot does
not parse, is written out as `SELECT * FROM t` first. In the sqllogictest
replay, the `setops` area went from 18 agreeing queries to 79, none disagreeing.
`UNION BY NAME` is still refused.

### Windows over every column are deterministic

A window partitioned by every column of its input, such as
`ROW_NUMBER() OVER (PARTITION BY` every column`)`, is now reported as
deterministic without a key. Rows tied in such a partition are equal, so how
an engine breaks the ties cannot change the result (`window_allColumns`,
proved). So `INTERSECT ALL` and `EXCEPT ALL`, which number the copies of each
row this way, are deterministic too, with or without keys on their inputs.

### Lists in DuckDB SQL: literals, indexing, UNNEST

The SQL lift reads DuckDB's list literals (`[1, 2, 3]`, nested ones too),
`l[i]` with a constant index (from 1, from the end for a negative `i`, NULL for
`0` and out of range), and `UNNEST(l)` in the select list (one row per
element, none for a NULL or empty list) (#348). Lean's results match DuckDB's.
DuckDB's SQL writer has no lists yet (#94), so these plans are checked against
DuckDB's own result but not run back; the sqllogictest ledgers now count such
agreements apart ("Oracle A only"). Lists of computed elements, of DECIMALs,
slices and an untyped `[]` are refused with a reason.

### Contracts on rollups: `MIN`, `MAX` and `AVG` of a group

More of a rollup's contract is proved before any data runs.

- `MIN` and `MAX` of doubles are accepted (#371). DuckDB orders doubles as
  the reference does, `-∞ < … < +∞ < NaN`; Polars and DataFusion refuse them
  until #271.
- `MIN`, `MAX`, `AVG` and `SUM` of a column that is never NULL, over a group
  without a filter, are never NULL (#372).
- `MIN ≤ MAX` for measures of the same values on one group, and an integer
  `AVG` with an integer result lies between them (#372).
- A decimal `AVG` and an integer `AVG` with an integer result lie within their
  values' bounds (#237). TPC-H Q17's `0.2 * avg_qty` is now proved not to
  overflow.
- A conversion of integers to doubles keeps their bounds: `CAST(x AS DOUBLE)`
  of `x` in `[0, 1000]` is in `[0.0, 1000.0]`.

An `AVG` of doubles, including the mean of integers as a double, rounds and
can step past its values (the mean of three `0.1` is `0.10000000000000002`),
so it gets no bound from its inputs here. Error bounds for it come with #85.

### Runtime-checked postconditions on nodes

`on_unproved="runtime"` now works on nodes built from sources (#373). The
postconditions Lean could not prove are checked at every refresh, on the full
result the first time and then on the rows each batch inserts (keys on the
new state), before the sink commits. A violation raises `PostconditionError`
and the refresh writes nothing. Before, building such a node raised
`VerificationError`. The transform's report marks these postconditions as
checked on data (`CheckedCondition.checked`), and the refresh report lists
them as `ensures` lines next to the preconditions. Downstream transforms
assume only proved postconditions, so a node with checked ones is stored with
`.write` before another transform reads it. An incremental view of an eager
result checks them on every batch too.

### Custom sources resume from the cursor their sink recorded

A sink now records the cursor of each source next to its version
(`Contract.cursors`). A `sverify.io.Source` that implements
`restore(cursor)`, the whole table as of a recorded cursor, starts there
after a restart: the stored nodes resume from their sinks, the first
refresh reads only what is new since, and the sink writes that change.
`from_query`, `from_files` and `FlightSource` implement it. A source without `restore`, or
whose cursor is gone (`restore` returns None), is read in full again and
written once, as before. `Source.snapshot` also serves the versions whose
batches the source still keeps (#374).

### Arrow Flight sources

`sverify.io.flight.FlightSource` reads a table of a numbered batch log on an
Arrow Flight server: each refresh streams the batches after the last one
read, registers them with the engine without a copy, and reads the batches
the server dropped past its retention as deletes. `FlightLog` is a small
in-memory server for that log, and the [guide](docs/guide.md) documents the
protocol for other servers. `pip install 'sverify[flight]'` (#375).

### A source with `schema=` proves contracts without reading

`Source.schema()` returns the schema given as `schema=` without reading the
source, so building a node proves the transform's contract whatever the state
of the source, and the first read happens at the first refresh (#376).

### Delta sinks maintain their tables and resume past maintenance

`DeltaSink` takes `checkpoint_interval`, `log_retention`, `compact_every`
and `vacuum_retention`, and `DeltaSink.maintain()` compacts and vacuums by
hand. The maintenance commits carry the contract of the sink's last commit.
A restarted job now resumes from a table whose commits after the sink's
last one change no rows: `OPTIMIZE`, `VACUUM`, property and constraint
changes, by `maintain` or another writer. It used to recompute the node and
overwrite the table. An Iceberg sink resumes past `replace` snapshots
likewise (#377).

delta-rs 1.6.6 hangs in `history()` and `set_table_properties()` against an
S3 server in the same Python process, such as moto's `ThreadedMotoServer`
(`upstream/LEDGER.md` DL-1). Run moto as its own process.

### One-line refresh summaries

`Refresh.summary()` gives one line per node for the log of a job that
refreshes often, such as "paid: orders@v1→v2, Δ trusted (change feed),
requires checked on 1 row(s) (3 proved from metadata), merge v3: +1 −0"
(#378). Postconditions a node checks on its output (`on_unproved="runtime"`)
show as "2 ensures checked on data", and a node's time buckets (#294) as
"bucket: 3/3 bucket(s) open, 1 retired". `str(refresh)` keeps the full report. A node's line becomes its full
entry when the refresh did something notable (`StageRefresh.notable`): its
first refresh, a source recomputed without a change feed, a schema change
(`SourceRefresh.schema`), or a sink overwriting its table.

### Overflow hints name the bound to add

A report's overflow hints now name the column and propose bounds (#379),
in `Report.hints` and as `hint:` lines. A truncated or binned timestamp or
date gets a lower and an upper bound on its column, such as
`_.ts >= datetime(2000, 1, 1)` and `_.ts < datetime(2100, 1, 1)`, which clear
the overflow. An integer `SUM` that is checked while the job runs gets the
range Lean knows for the column it adds up and the largest group whose sum
then fits 64 bits, or, for an unbounded column, a bound to add and the group
size it allows. No contract can state a group's size, so the hint says so.
The general hint stays for overflows the new ones do not cover.

### GREATEST and LEAST of date and timestamp constants run as dates again

`LEAST(DATE '1992-01-01', DATE '1991-01-01')` and its timestamp counterpart returned the integer code of the result on DuckDB (`7670`, `662693025000000`), whenever every argument was a constant (#381, a regression of #355). The plan Lean writes back now writes two constants in the call's own kind, as it does elsewhere, so they are dates and timestamps to the engines. Lean's own results were right throughout.

### TIME constants, substring ranges and retention under a projection

- `TIME '13:45:21'`, `CAST('…' AS TIME)` and a string compared with a `TIME`
  column now lift to a TIME literal, so queries that compare a `TIME` column
  with a constant verify. Constants DuckDB raises on, and `24:00:00`, are
  refused (#386).
- `substring` with a constant offset outside [-2³², 2³²) or a constant
  length of 2³² or more is refused: DuckDB raises there, and the model has
  no such error yet (#336).
- Retention engages for an aggregate under a filter or a projection, such as
  a per-mille-to-percent `select` after the `aggregate` (#394).

### `arrives_within` lets a source's own retention through

A delete before the watermark no longer rejects the batch when its row is in
a bucket every retiring view has made final: it is the source's own
retention, such as a `FlightSource` floor or a Delta `VACUUM`. The views and
their sinks keep those buckets, and the report counts the expired rows. Lean
proves the result is the full recompute over the rows the source received
(`Retention.expiry_sound`). A delete before the watermark in a bucket that is
still open rejects the batch (#395).

### Clearer contracts API and messages

- A `requires` key that names no input raises a `ValueError` naming the key,
  the inputs and a close match, where it raised a bare `KeyError`. A
  transformation with one input takes a plain list,
  `requires=[_.amount >= 0]` (#408).
- `@sv.transform(infer=False)` turns off bound inference, as on `sv.verify`.
  `strict=True` still works and warns that it is deprecated (#409).
- `sv.references("cust", to=customers.id)` names the referenced column with
  an Ibis column or a `(table, column)` pair. The positional form
  `references(col, table, other)` warns that it is deprecated (#412).
- `Connection.datafusion` is deprecated: the DataFusion session is an
  internal of the DataFusion engine (#413).
- Refusals give their reason in terms of the reference semantics, with the
  issue to follow and a workaround, and no longer cite DataFusion's
  behaviour (#410).
- An unproved condition says why in words: "it may be FALSE on some rows",
  and where it may be NULL, how to declare the column NOT NULL. This
  replaces "(it is TRUE or FALSE)"; `CheckedCondition.why` has the text
  (#176).

### The reference semantics is the default everywhere

Breaking: `sv.sql(query)` now uses sverify's reference semantics by default,
as `sv.verify` and `@sv.transform` do; DuckDB's semantics (NaN and ±inf as
DuckDB computes them) is an explicit opt-in, `semantics="duckdb"` (#411).
Write `semantics="duckdb"` on `sv.sql` calls that relied on the old default.
SQL transformations and SQL conditions in `sv.verify` and `@sv.transform`
were lifted with DuckDB's semantics too, and now follow the new `semantics=`
parameter of each, which defaults to the reference. `Report.semantics`, and a
`semantics:` line in the printed report, say which semantics a check used.

### Narrow arithmetic on constants keeps its width

In `(10::TINYINT * 10::TINYINT) * x`, the parser treated the inner product as
a 64-bit value because it reads no column, so the outer multiplication was
not checked at 8 bits: `verify` missed the overflow and the written plan
returned 1000 where DuckDB raises. A call's declared output type now gives its
width (#419), as a column's does, at TINYINT, SMALLINT and INTEGER and for
`+`, `-`, `*`, negation and division.

### Inferred bounds on eager tables

`@sv.transform` on an eager table (an `ibis.memtable`, or any plain Ibis
expression that is not a contracted result) now infers the bounds that rule
out overflow, checks them on the table's data, and proves the contract, as
`sv.verify` does. Hints name the bound as a `requires` of the parameter
([#430](https://github.com/AlexanderNenninger/substrait-lean/issues/430)).

### Fixed: `avg` of a nullable integer under `semantics="duckdb"`

An `avg` of an integer column that may be NULL failed its proof with
"division by zero", because DuckDB's `avg` is lifted as the sum divided by
the count, and the count of a group whose values are all NULL is 0. The lift
now states that such a group's average is NULL, as DuckDB returns it, so
nothing can fail (#434).

### Fixed: reports on a DATE beyond the year 9999

A transformation with a DATE column whose range passes Python's limits, such
as `CAST(ts AS DATE)` of a TIMESTAMP, raised `OverflowError` while describing
its facts. Bounds outside the years 1 to 9999 now go without saying: the
column is "any date" (#435).

### A transformation with an `ibis.param` says how to bind it

A contracted transformation whose body uses an `ibis.param` failed with a
bare `KeyError` from Ibis. It now raises a `TypeError` naming the parameter:
transformations don't bind parameters yet (#354), so prove the expression
with `sv.verify(expr, params={param: value})` or write the values as
`ibis.literal(...)` (#440).

### Fixed: Ibis's DuckDB `create_table` failed on a fresh install

A fresh install resolved SQLGlot 30.18 or later, from which SQLGlot reads a
`DROP`'s names where Ibis 12 doesn't put them, so `con.create_table(...)` on
Ibis's DuckDB backend raised a DuckDB syntax error. sverify now requires
`sqlglot~=30.17.0` until Ibis follows
([upstream/LEDGER.md](../upstream/LEDGER.md) SG-7, #442).

### Fixed: SQL reports described timestamps and dates as integers

The facts of a SQL transformation described its timestamp and date columns
as "any integer", the model's codes for them. They now read as the same
columns written in Ibis do, "any timestamp" and "a date in [...]" (#452).

### Numeric functions: `sqrt`, logarithms, trigonometry, `sign`, bitwise operations

Ibis's `sqrt`, `exp`, `ln`, `log`, `log2`, `log10`, `sin`, `cos`, `tan`,
`asin`, `acos`, `atan`, `atan2`, `cot`, `degrees`, `radians`, `sign`,
`isinf`, `e` and `pi`, and the bitwise `&`, `|`, `^`, `~` and shifts, are
verified (#48). The functions compute as C's libm does, and contracts treat
their results as doubles. Outside a function's domain (`sqrt` of a negative,
the logarithm of 0, `asin(2)`, `atan2(0, 0)`, a shift by more than 63) the
reference raises a domain error, which `verify` reports unless a filter or
`requires` rules it out: `t.filter(_.x > 0).select(_.x.ln())` is proved.
DuckDB and Polars run them all; Spark runs `sqrt` and the bitwise operations,
Snowflake `&`, `|` and `^`, and both refuse the rest.

### Regular expressions and digests

Ibis's `re_extract` and `re_replace` (DuckDB's `regexp_extract` and
`regexp_replace`, with or without the flag `'g'`) and `hexdigest('md5')` and
`hexdigest('sha256')` are verified on DuckDB (#50). Patterns must be
constants in the subset `Text.simpleRegex` accepts, which now includes
non-capturing groups `(?:…)`. Proofs treat these functions as black boxes,
but Lean evaluates them: regular expressions with RE2's leftmost-first
matching and DuckDB's edge cases (`''` where nothing matches, `\1` in the
replacement, empty matches), and the digests as lowercase hex. So
ClickBench Q28 and dbt's surrogate key now verify. DuckDB's `hash()` and
Ibis's URL parts (`host()`, …) are refused, and the other engines refuse
all of these until #271. The DuckDB SQL of `\b` in a pattern now raises on
non-ASCII text, as `\d`, `\w` and `\s` already did, since RE2 and Rust
disagree there.

### `any()` and `all()`

Ibis's `any()` and `all()` of booleans are now verified, as `MAX` and `MIN`
(`BOOL_OR` and `BOOL_AND`): NULLs are skipped, and a group without a
non-NULL value gives NULL (#53).

### Bit aggregates

`bit_and()`, `bit_or()` and `bit_xor()` of integers are verified: the
64-bit operation folded over the non-NULL values, NULL for a group without
one. They run on DuckDB, Polars, DataFusion, Spark (`BIT_AND`, …) and
Snowflake (`BITAND_AGG`, …) (#53).

### Covariance and correlation

Ibis's `cov()` and `corr()` (DuckDB's `COVAR_SAMP`, `COVAR_POP` and `CORR`)
are verified on DuckDB, grouped, with DuckDB's own algorithm (#54). `CORR`
is NULL for fewer than two pairs and where one side's values are all equal,
as the SQL standard says, rather than DuckDB's NaN, and an infinite value
raises, since a deviation from the mean would be NaN. The other engines refuse
them until #271.

### Variance and standard deviation

`var()` and `std()` of doubles and integers, of a sample or a population
(`how="pop"`), are verified on every engine (#54). Each engine uses its own
algorithm for now, so results may differ in the last bits, and a contract
can rely only on the value being a non-negative double, or NULL: for no
values, and for a sample of one value. A NaN passes through; an infinite
value raises, since its deviation from the mean would be NaN. Variances over
windows are refused.

### `distinct(on=)`, and `first()`/`last()` without an order

Ibis's `distinct(on=…)` and `first()`/`last()` without `order_by` (DuckDB's
`FIRST`/`LAST` with no `ORDER BY`) are now verified rather than refused
(#55). They take any row's value, so the report says the result is not
`deterministic`, and proves nothing about it, unless the grouping (`on`)
columns form a key. Each column is chosen on its own: `distinct(on="name")`
may keep `a` from one row and `b` from another, so a fact about every input
row, such as `a <= b`, need not hold of the result. They run on DuckDB for
now; the other engines refuse them until #271.

### `first()` and `last()` with an order

Ibis's `first(order_by=…)` and `last(order_by=…)` (DuckDB's `FIRST(x ORDER
BY …)`) are verified: the first or last non-NULL value in that order, NULL
without one (#55). Without `order_by` they are any row's value and stay
refused. Where rows tie in the order, the report says the result is not
`deterministic`, unless the grouping and order columns form a key. They run
on DuckDB for now; the other engines refuse them until #271.

### `group_concat()` with an order

Ibis's `group_concat(sep, order_by=…)` (DuckDB's `STRING_AGG(x, sep ORDER
BY …)`) is verified: the non-NULL strings in that order, joined by a constant
separator, and NULL without values (#55). Without `order_by` the order is
the engine's, so it stays refused. As for `first()` and `last()`, rows that
tie in the order make the report not `deterministic` unless the grouping and
order columns form a key. It runs on DuckDB for now; the other engines refuse
it until #271.

### `ibis.param` values for `verify`

`sverify.verify` takes `params={param: value}`, as Ibis's
`execute(params=...)` does, and binds each `ibis.param` to its value before
compiling (#58). The report is about the expression with those values, and
says so: `Report.params` lists them, and the report notes that its proofs
hold for those values only. A parameter left unbound is still refused, now
with a reason that says to pass `params`.

### Refusals say why

`random()`, `uuid()`, `now()`, `today()`, `typeof()`, `ibis.param` and
`try_cast` were refused with "X is not supported". The message now gives
the reason and what to do instead, for example to pass the time in as a
column or constant (#58).

### `try_cast()`

Ibis's `try_cast()` (Substrait's `failureBehavior: RETURN_NULL`, SQL's
`TRY_CAST`) is verified for a double to an integer and an integer to a
narrower integer (#58): NULL where `cast()` would raise, so `verify` reports
no "cast out of range" for it. A double still truncates toward zero, as the
reference's `cast()` does, where DuckDB's own `TRY_CAST` rounds. `TRY_CAST`
to a DECIMAL, of a DECIMAL to an integer, and of strings is refused. It runs
on DuckDB for now; the other engines refuse it until #271.

### Casts of rounded aggregates keep their bounds

With a row cap (`sv.max_rows`), a cast of a `SUM` or `AVG` of doubles keeps
the aggregate's proved error bound (#85, #223). `CAST(AVG(cpu) AS BIGINT)` of
`cpu` in `[0, 100]` is in `[0, 100]`, and `verify` no longer reports that the
cast may fail, nor a cast to a decimal that the bound keeps within its
precision. A `SUM` of integers cast to doubles carries each conversion's
rounding in its bounds.

### Contracts on `SUM` and `AVG` of doubles, up to rounding

Rollups of doubles get proved bounds (#85).

- `sv.max_rows(n)` caps an input's rows, checked on the data. With a cap, a
  `SUM` or `AVG` of doubles in `[lo, hi]` is bounded by the exact result's
  interval widened by the proved rounding error (`docs/float-bounds.md`).
- `sv.approx(cond)` states a postcondition up to that rounding:
  `sv.approx(_.cpu_avg <= 100)` is proved where `_.cpu_avg <= 100` is not,
  and runs as `_.cpu_avg <= 100.0001`. A report hints at it when an exact
  claim fails only by rounding.
- Signs are exact without a cap: a `SUM` or `AVG` of values `≥ 0` is `≥ 0`.

### Proved error bounds for floating-point aggregates

The `float-bounds/` package proves error bounds for `SUM`, `AVG`, `VAR_*`,
`STDDEV_*`, `COVAR_*` and `CORR` of doubles (#85), in the standard model of
rounding with its underflow term. A sum of `n` values is within
`γ n · Σ(|xᵢ| + 2⁻¹⁰²²)` of the exact one, sequentially or in shards; the
co-moment behind the variance family is within `64 · n² · u · B²` for each of
the two-pass, textbook and Welford/Chan algorithms (DuckDB's), so the bound
holds whatever an engine uses. See `docs/float-bounds.md`.

### Generic properties of statistical aggregates

`VAR_*`, `STDDEV_*`, `COVAR_*` and `CORR` now have proved generic properties
that any common algorithm keeps (#85): `NULL` where the reference says, a
variance `≥ 0`, the result within `(128 n² u B² + 12 n u B²) / d` of the
exact one, and `|CORR| ≤ 1 + ε` when both variances are bounded below. The
reference allows any result with them (`StatProps`), so DuckDB's Welford,
Polars' blockwise two-pass and the reference's own two-pass all agree with
it. Engine profiles can name a stricter algorithm (`Profile.statAlgo`).
A computed double's bound now carries through `CAST(x AS BIGINT)` with row
caps, and `SUM(CAST(x AS DOUBLE))` of integers gets the summation bound.
See "Statistical aggregates" in `docs/reference-semantics.md`.

### Statistical aggregates within bounds that scale with the spread

`VAR_*`, `STDDEV_*`, `COVAR_*` and `CORR` may now differ from the exact result
only by bounds that scale with the spread of the values (`StatProps`,
`docs/reference-semantics.md`). For `10⁶` values near `10⁶` that vary by about
`1`, the variance is within about `2 · 10⁻²`, where the earlier bound allowed
`1.4 · 10⁴`. The bounds are proved for two-pass and for DuckDB's algorithm;
the textbook formula `Σx² − (Σx)²/n` falls outside them.

### Variance bounds that scale with the spread

`float-bounds/` proves tighter variance bounds for three algorithms (#85):
two-pass, Lean's own, is within `8 n u S + 80 n² u² Σx²` of the exact sum of
squared deviations `S`, Welford's update within one thread within
`32 n u √(S Σx²) + 104 n² u² Σx²`, and DuckDB's parallel aggregation (Welford
in each thread, Chan's merge with a fused multiply-add) within
`148 n u √(S Σx²) + 3961 n² u² Σx²`. The covariance has the analogues, for
two-pass and for DuckDB's parallel aggregation, in `√(S_xx S_yy)`,
`√(Σx² S_yy)` and `√(Σy² S_xx)`. They stay useful for values far from zero
with a small spread, where the generic bound does not. The
standard model of rounding now states that a double rounds to itself.

### Lists run on DuckDB

Plans with lists now run on DuckDB as well as Polars (#94): list columns and
literals, list elements and `length`, `collect()` (ordered or not, NULLs
skipped) and `unnest`. The written SQL keeps Lean's order: each row's
elements come out in list order, and ties in a `collect` order fall to the
row order, so an order-dependent step above sees the same rows Lean does.
Snowflake and Spark still refuse lists, until #271; structs and lambdas stay
Polars-only for now.

### Struct fields, list elements and lambdas

Ibis's struct fields (`t.s.a`), list elements (`t.l[0]`, a constant index,
negative from the end), `length()` of a list, and `map`, `filter` and
`contains` on lists are verified (#94). A lambda may read only its element
and constants, so `contains(v)` needs a constant `v`. A NULL element matches
only NULL in `contains`. `verify` reports an error in a lambda's body on any
element as the row's. Polars runs them; for DuckDB, see "Lists run on
DuckDB". This also fixes the Ibis producer reading `t.select(a=t.s.a)`
as the table's first column.

### A batch updates a source table at the cost of the change

Applying a batch to a pipeline's copy of a source table no longer groups the
whole table. A batch of inserts appends them, and deletes touch only the rows
equal to a deleted row. On the metrics benchmark (2.4 million rows, one minute
of samples per refresh) this was about 200 ms of a 365 ms refresh.

### A stale checker fails with a clear message

`substrait-check --version` prints the checker's protocol, and sverify checks
it once per process: a checker older or newer than the package raises
`sverify.errors.CheckerVersionError`, which says how to rebuild it (`uv sync`
or `lake build substrait-check`), where a stale build used to fail later with a
`KeyError`.

### `inf - inf` and `0 * inf` are NaN under `semantics="duckdb"`

With DuckDB's semantics, `+`, `-` and `*` of doubles now lift to what DuckDB
computes: NaN for `inf - inf`, `-inf + inf` and `0 * inf`, as `/` already
gave for `inf / inf` and `0 / 0`. Lean's generated lift table states them
exactly (`DuckFn.addDouble`, `subDouble`, `mulDouble`), so the plan Lean writes
back runs on DuckDB and gives NaN too, where it used to raise "domain error".
The reference semantics still raises there (#257).

### Engine facts: JSON only, and an `io` layer

The facts in `characterization/<engine>/facts/` are the record: the generated
`FACTS.md` overviews, `python -m sverify_dev.facts --write` and their step in
the `Generated files` workflow are gone; `python -m sverify_dev.facts` checks the
documents. `fact.schema.json` has a layer and an area `io` (how an engine reaches
data: extensions, catalogs, object stores, credentials) and a status
`workaround`. The first: DuckDB's `unity_catalog` extension's ATTACH ignores a
named secret unless it names it (`duckdb-IO1`) and ignores the vended `endpoint_url`, so a
MinIO behind Unity Catalog needs DuckDB's `s3_endpoint` settings (`duckdb-IO2`);
its `delta` reader is then denied with the table-scoped keys (`duckdb-IO3`, open).

### A fast default test suite

`poe test` runs the fast Python tests on 2 workers: it leaves out the tests
marked `slow` (engine agreement on many queries, long streams, replays, and the
Spark tests) and runs a tenth of each Hypothesis test's examples (the `dev`
profile, `SVERIFY_PROFILE`). `poe test-all` and `poe qa` run every test with
the full counts, as CI does; CI splits the `core` tests into three shards
(`SVERIFY_SHARD`, `python/tests/conftest.py`).

### Nightly wheels

Each night, when `main` has changed, the Wheels workflow builds and tests the
wheels for every platform and publishes them as the rolling
[`nightly` pre-release](https://github.com/AlexanderNenninger/substrait-lean/releases/tag/nightly),
versioned `<next minor>.dev<commits>+g<sha>`. Install them with
`uv add "sverify>=0.4.0.dev0" --find-links https://github.com/AlexanderNenninger/substrait-lean/releases/expanded_assets/nightly`
or `pip install --pre sverify --find-links …`; `python/README.md` has the
details. Each build's wheels stay on the release for 30 days, so a pinned wheel
URL works that long. They never go to PyPI.

### No more Intel macOS wheels

Wheels exist for Linux (x86_64, aarch64) and macOS on Apple silicon (arm64).
On an Intel Mac, pip and uv build `sverify` from the sdist, which needs
[elan](https://github.com/leanprover/elan).

### The tour is five notebooks

The tour has three workflows (duplicate payments, sensor alerts, an orders
mart) and two guides: contracts (chapters 4 to 8 merged) and pipelines and
engines (chapters 9 to 12 merged). The start page and the chapters on how it
works moved to `docs/how-it-works.md`. Chapter 17 is now
`catalogue/backend_semantics.py`.

### Windows over time frames recompute only the rows near the change (tested)

A node of window aggregates over bounded RANGE frames of one time column
(`range=(-ibis.interval(minutes=5), 0)`) recomputes only the output rows
whose frames a batch's rows fall in, from the input rows those frames read.
This strategy is tested, not proved: `status()` and the refresh summary say
"touched frames recomputed (tested, not proved)", and the lemma it rests on
is #458 (#294).

### Touched groups read only the touched time range

When one of an aggregate's group keys is a fixed-width time bucket
(`ts.truncate("m")`, `ts.bucket(...)`), recomputing the touched groups reads
the input through the range those buckets cover, so the engine skips the
other rows while it scans. The semi-join on the keys still picks the exact
rows, and a touched NULL bucket reads the whole input.

### Aggregates recompute only the groups a batch touches

A node that ends in a `GROUP BY` over an input with delta rules no longer
recomputes and diffs its whole result on every refresh. It takes the group
keys of the input rows the batch inserts or deletes, recomputes those groups
(a semi-join on the keys) and replaces their rows, for any measure: MIN, MAX,
AVG, COUNT, SUM and the rest. Lean proves the split
(`TouchedGroups.touched_sound`). `status()` and the refresh summary say which
strategy ran. Other nodes without delta rules are still recomputed and
diffed, and #248 stays the issue for delta rules of aggregates.

### Windows recompute only the partitions a batch touches

A node whose window functions share one `PARTITION BY` (with the partition
keys among its columns) recomputes only the partitions a batch touches, the
way an aggregate recomputes its touched groups. Lean proves it from
`windowEval_sharded` (`TouchedGroups.touched_window_sound`), for inputs
without ties on the partition and sort columns. Windows with different
partitions, or none, are still recomputed and diffed.

### `division_type: TRUNCATE` is accepted

A plan whose `modulus` states `division_type: TRUNCATE` was refused,
although the remainder already takes the dividend's sign. It is now
accepted; `FLOOR` is still refused, as the model does not compute it.

### `approx_nunique` is refused

Ibis's `approx_nunique()` was translated as the exact `nunique()`. Each
engine computes its own estimate, so no plan gives the same answer
everywhere; it is now refused, with a hint to use `nunique()` for the exact
count.

### Isthmus support removed

sverify no longer compiles SQL strings with Isthmus (substrait-java's
Calcite-based compiler). Its frontends are Ibis and SQL through sverify's
own producers (#211, #231). `sverify.engines.isthmus_json`,
`sverify.engines.SQL_PRODUCERS`, `sv.connect(sql_producer=...)` and the
`SVERIFY_ISTHMUS` variable are gone. SQL strings need the `datafusion` extra
until the SQLGlot frontend replaces DataFusion's producer.

### Maintainer tooling leaves the wheel

The coverage harness, the query catalogue, the fuzzers, DuckDB's
sqllogictest replay and the example pipelines (`sverify.coverage`,
`sverify.catalogue`, `sverify.fuzz`, `sverify.duckdb_fuzz`, `sverify.slt`,
`sverify.examples`) were internal, and only the tests and CI used them. They
now live in `python/tools/sverify_dev` in the repository and are no longer
installed with sverify: about 4,000 lines fewer in the wheel.

### Fixed: a sink kept another plan's rows after the plan changed

If you use 0.3.0 and change a node's transform while keeping its sink,
upgrade. The sink recorded which plan wrote each state, but only compared
the state's epoch (the sum of the source versions) when deciding what to
write. So a job restarted with a new plan, at source versions the sink had
already committed, skipped the write: the table kept the old plan's rows and
its contract, while the node held the new plan's state. On the next source
change it merged the new plan's change on top of the old plan's rows, and
the table was wrong from then on, without an error. This affected
`DeltaSink`, `IcebergSink`, `sink_from` and sinks of your own that override
`committed()`.

A sink whose last commit came from another plan (`Contract.plan` differs) is
now overwritten with the new plan's whole state, and the refresh reports the
write as `overwrite`. `DeltaSink` replaces the table's schema and drops the
CHECK constraints it added for the old plan that the new one does not prove,
then adds the new plan's in the commit that records the epoch, so a job
stopped in between writes the state again. `IcebergSink` replaces the
table's schema in the overwrite's transaction. Constraints that another
writer added still stop the write.

A table is affected if you restarted a job with a changed plan before its
sources moved on. If it has not written a change since, the first refresh
after upgrading overwrites the table. If it has, that MERGE recorded the new
plan, and the fix cannot tell the table is wrong: delete the table, or point
the sink at a new location, and refresh to write it in full.

### Fixed: a node without a contract is planned again after a schema change

A node of a plain function, such as `orders.pipe(lambda t: t.select(t.id))`,
counted as contracted, so a dropped column, or a column widened beyond what
its values used to fit, raised `SchemaError` instead of planning the node
again. It is now planned again and recomputed, and its sink is overwritten.

### Changed: no operation creates a NaN

A NaN in your data still passes through, but an operation on numbers no
longer makes one where IEEE would. `inf - inf`, `0 * inf`, `inf / inf`,
`fmod(inf, y)`, a negative number to a fractional power, `sin`, `cos` or
`tan` of an infinity, and a grouped double `SUM` or `AVG` of both `+inf` and
`-inf` now raise a domain error on DuckDB, Polars, Spark and Snowflake, and
`verify` reports "domain error" unless the plan rules it out. So a job with
no NaN in its inputs has none in its outputs. For double arithmetic on
columns `verify` cannot bound, add bounds such as `_.x < 1e300` and
`_.x > -1e300` to `requires`. Adding a constant, or a whole-number power,
needs none. A plan that asks for `on_domain_error: NAN` is refused, and
`on_division_by_zero: IEEE` still gives NaN for `0.0 / 0.0`, as it asks.
DataFusion still gives NaN where the others raise (#257).

### Fixed: `%` of doubles gave wrong values

A plan that takes the remainder of doubles, such as `x % 2.5`, passed the
check but was evaluated on the doubles' internal codes, so its values were
wrong (`7.5 % 2.0` came out as a 300-digit integer). It is now C's `fmod`,
as DuckDB, DataFusion and Spark compute `%`: the result has the sign of the
dividend (`-7.5 % 2.0` is `-1.5`), a NaN gives NaN, an infinite dividend
raises (see above), and an infinite divisor gives the dividend. The value is exact. A zero
divisor is an error, as for integers, so `verify` reports "division by zero"
unless the plan rules it out (`WHERE y <> 0.0`). The Polars translation gives
the same results, although Polars' own `%` takes the divisor's sign.
Substrait itself defines no `modulus` of doubles (#203).

Substrait defines no `modulus` of doubles, so plans now call sverify's own
`sverify_fmod` for it, which the Ibis producer and the SQL lift emit for `%`
of doubles and which DataFusion runs as its own `%`. sverify still reads the
`modulus` of doubles that DataFusion's producer writes (#256).

## 0.3.0 (2026-11-01)

### Licensed under the MPL-2.0

sverify now has a license, the Mozilla Public License 2.0; 0.2.0 and earlier
were published without one. You can use sverify in open and proprietary
products alike. If you distribute changes to sverify's own files, they stay
under the MPL. The vendored `ibis_substrait` stays under Apache-2.0.

### Nodes compose left to right with `.pipe`

A job now reads in the order its data flows
([#189](https://github.com/AlexanderNenninger/substrait-lean/issues/189)).
It adds to the API and changes nothing that exists.

```python
paid_orders = orders.pipe(paid).write(DeltaSink("lake/paid"))     # chain, then store
enriched = paid_orders.pipe(enrich, customers=customers)          # fan-in by keyword
regional = paid_orders.pipe(
    sv.sql("SELECT o.*, c.region FROM orders o JOIN customers c ON c.cid = o.cid"),
    customers=customers,
)                                                                 # SQL is a step
quick = orders.pipe(lambda t: t.filter(_.amount > 0))             # no contract
sv.group(paid_orders.pipe(daily_totals), enriched).refresh()      # fan-out
```

- `Node.pipe(step, /, **inputs)`, and `pipe` on every source in
  `sverify.io`, apply a step to the node: the chained node fills the step's
  first table parameter, and the other inputs come by keyword. It builds the
  same node and plan as the call form `paid(orders)`, which stays public.
  A missing, duplicate or unknown input raises `TypeError` naming the step's
  parameters.
- A step is a contracted transform, a plain function from Ibis tables to an
  Ibis table (a transform with no contract), or `sv.sql(query)`.
- `sv.sql(query, *, as_=None)` without tables is a step whose inputs are the
  tables the query reads (not its CTEs, and each once). The keyword inputs
  bind their own names, and the chained node binds to the one table left
  over. A table with no input, an unused chained node, a keyword the query
  doesn't read, or an `as_` that isn't the table left over raises
  `TypeError`. `sv.sql(query, orders=orders)` inside a transform is
  unchanged.
- The README, the tour and the API reference lead with `.pipe`.

### Your own sources and sinks

Writing a source or a sink no longer means knowing sverify's internals
([#156](https://github.com/AlexanderNenninger/substrait-lean/issues/156)).

- `sverify.io.Source`: implement `read(since)`, which returns new rows and a
  cursor as a `Batch` (`kind="append"`, `"snapshot"` or `"changes"`).
  sverify numbers the reads as versions, keeps the table, and hands nodes
  the exact change. The refresh report says what the batches assume, and
  `refresh(audit=True)` reads the table again in full to check it, also
  when no batch arrived. `from_query(fn, cursor_on=...)`, `from_frame(fn)`
  and `from_files(path)` build one.
- `sverify.io.Sink`: implement `write(change)`, which gets a `SinkChange`
  (rows added and removed, or the whole table, and the contract), and
  optionally `committed()`. Exactly-once skipping and contract recording
  happen once, in the base class. `sink_from(fn)` hands the whole table to
  a function. Nodes reading a stored node of your own sink read what was
  written, with its exact changes. `DeltaSink` and `IcebergSink` are now
  subclasses, and every sink reports a `SinkWrite` (new mode `"update"`;
  `version` may be None).
- The full protocol for table formats is public as
  `sverify.io.VersionedSource`, with `Snapshot` and `SourceBatch`, whose
  `unchanged`, `from_changes` and `from_snapshot` build what `changes`
  returns. `Pipeline` no longer special-cases `StaticSource`: any source
  with a `digest` gets it recorded.
- `sverify.io.Storage` holds object store options shared by several tables:
  a mapping, or a function returning fresh options whenever a table is
  opened, so expiring tokens renew; `repr` shows option names only.
  `DeltaSource` and `DeltaSink` take one, or a function, as
  `storage_options`.
- A sink's `app_id` now defaults to `sverify:<sink name>` (it was the
  node's name, which is the same unless it clashed with a source's).
- `Contract.from_json` ignores fields it does not know, so contracts can
  gain fields without breaking the readers of this version.

### A pytest plugin for transforms and contracts

`sverify.testing` is now public
([#180](https://github.com/AlexanderNenninger/substrait-lean/issues/180)), and
installing sverify registers a pytest plugin (the `pytest11` entry point
`sverify`, off with `-p no:sverify`).

- `assert_contract(node)` asserts that every contract in a node's lineage is
  proved. With `data=` it runs the node on those rows: test data that breaks
  a precondition is reported with its rows, the output is checked against
  the postconditions, and with `expected=` it is diffed against the expected
  rows (missing and unexpected rows, as bags).
- `assert_engines_agree(node, data)` runs the node on every installed engine
  and diffs their results.
- `cases(node, max_rows=5)` is a Hypothesis strategy of input tables that
  meet a node's preconditions, for property tests of the code around it.
  It needs the new `testing` extra (`pip install 'sverify[testing]'`).
- The fixtures `sv_source(rows, schema, name=...)` (an in-memory source,
  also `sverify.testing.source`) and `sv_engine`, which runs a test once per
  installed engine (`installed_engines()`), or per engine of
  `--sv-engines=duckdb,polars`.

`python/tests/test_plugin_example.py` is an example test file, and
`python/tests/test_tour.py` tests the tour's transforms with the plugin.

### Ibis string functions

More of Ibis's string API is checked and runs on every engine
([#49](https://github.com/AlexanderNenninger/substrait-lean/issues/49)):
`lpad`/`rpad`, `repeat`, `reverse`, `replace`, `ilike`, `ascii`,
`levenshtein`, `right`, `find` with a start, `join` (`concat_ws`),
`find_in_set`, `capitalize` and slices. Each has the meaning of Ibis's
DataFusion SQL, by code point. A `repeat` past 2³¹ − 1 bytes is an
`overflow` error, which the checker rules out for a constant string with a
bounded count.

- Polars computes all of them exactly. DuckDB, Snowflake and Spark raise
  "non-ASCII text differs between engines" for `reverse`, `ascii`,
  `levenshtein` and `ilike` on non-ASCII text, and refuse `replace` with an
  empty pattern.
- `translate` is refused: DataFusion translates grapheme clusters.

### Fixes

- Written plans keep a projected literal's declared type: doubles,
  timestamps and typed NULLs no longer come out integer-typed
  ([#96](https://github.com/AlexanderNenninger/substrait-lean/issues/96)).
- The tour notebooks declare the extras they use (`sverify[datafusion]`,
  `sverify[datafusion,polars]`), so they run in their own sandbox, as molab
  runs them
  ([#197](https://github.com/AlexanderNenninger/substrait-lean/issues/197)).

## 0.2.0 (2026-11-01)

A new public API, built around transforms that compose
([#164](https://github.com/AlexanderNenninger/substrait-lean/issues/164)).
It is a clean break: the old names are gone, with no deprecated aliases. The
proofs, the Lean model and what each engine computes are unchanged.

### Transforms compose; there is no pipeline object

```python
import sverify as sv
from sverify.io import DeltaSink, DeltaSource

orders = DeltaSource("s3://lake/orders")
p = paid(orders).write(DeltaSink("s3://lake/paid"))      # stored, and a source downstream
r = revenue(p).write(DeltaSink("s3://lake/revenue"))

r.refresh()                    # DuckDB in memory by default
r.refresh(engine="polars")     # or "datafusion", "spark", a Spark session
r.to_arrow(); r.to_polars(); r.to_pandas(); r.table
```

- A contracted transform (`@sv.transform`) called on a source or a node
  builds a `Node`. The contract is checked when the node is built: a link
  whose upstream guarantees don't imply the downstream assumptions raises
  `CompositionError` at once. Called on Ibis tables, a transform still
  returns an Ibis expression.
- Without a `.write` between transforms, they fuse into one plan and one
  incremental view, and the intermediate rows are never stored.
- `.write(sink)` stores a node, in the middle of a job or at its end, exactly
  once per state. It returns a node that downstream transforms read as a
  versioned source (Delta's Change Data Feed, Iceberg's snapshots), building
  on the contract its own stage proved.
- `refresh()` on any node brings its whole lineage up to date, upstream
  first, refreshing every node once per call and writing every stored node
  once. A restarted job rebuilds the same nodes; the first refresh resumes
  each stored node from its table.
- The engine is chosen at refresh time, not when the job is built.
  `"spark"` and Spark sessions are new as engines for maintained results.
- `sv.group(a, b).refresh()` refreshes several outputs against the same
  source versions and shares the stored nodes they read; `.status()` reports
  on each.
- `node.plan` is the plan Lean checked, for `sverify.engines`.

### SQL models

A transform's body can be SQL over its inputs, by keyword name:

```python
@sv.transform(requires={"orders": ["amount_cents >= 0"]}, ensures=["revenue_cents >= 0"])
def revenue(orders):
    return sv.sql("""
        SELECT region, coalesce(sum(amount_cents), 0) AS revenue_cents
        FROM orders GROUP BY region
    """, orders=orders)
```

`sv.sql(query, **tables)` returns an Ibis table, so a SQL model is an
ordinary node. It fuses with its neighbours, can be stored with `.write`,
composes with Ibis transforms on either side and reads several inputs. Its
schema and plan come from DataFusion's SQL producer, or Isthmus's without
DataFusion, and work on the placeholder tables nodes are built from. A query
the producer can't plan, or a plan Lean refuses, raises `Unsupported` saying
which part; without either producer the error names the `datafusion` extra.

### A small namespace

`import sverify as sv` holds eleven names: `transform`, `sql`, `verify`,
`unique`, `references`, `Report`, `Changes`, `group`, `connect`, `asof_join`
and `Node`. Three submodules hold the rest:

- `sverify.io`: `DeltaSource`, `DeltaSink`, `IcebergSource`, `IcebergSink`,
  `SinkWrite`, `Contract`, `StaticSource`.
- `sverify.engines`: running plans, SQL dialects and plan tools.
- `sverify.errors`: the exceptions.

Every other module (`sverify.incremental`, `sverify.contracts`,
`sverify.engine`, `sverify.sql`, `sverify.partition`, the per-engine modules,
`sverify.ibis_substrait`, `sverify.catalogue`, `sverify.coverage`,
`sverify.fuzz`, `sverify.testing`, `sverify.counterexample`,
`sverify.display`, `sverify.examples`, `sverify.io.delta`,
`sverify.io.iceberg`) is internal and may change in any release.

### Other changes

- Sinks no longer take a view: `DeltaSink(uri)`, `IcebergSink(catalog,
  identifier)`, attached by `node.write(sink)`. There is no public
  `sink.write()`: refresh writes. Delta and Iceberg sinks report through one
  type, `SinkWrite` (it replaces `IcebergWrite`).
- Sources and sinks take `name=`, the table's name in the plans that read
  them. It defaults to the last part of the URI or identifier.
- `StaticSource.apply(sv.Changes(...))` changes some rows of an in-memory
  source; the next refresh gets exactly that change, where `replace` makes
  it diff the whole table. `StaticSource` takes `name=`.
- A node without delta rules (left join, aggregate, window, `DISTINCT`,
  `LIMIT`) is recomputed and diffed, as views were inside a `Pipeline`. The
  standalone `IncrementalView`'s refusal (`NotIncremental`) is no longer on
  the public path.
- Incremental views over SQL strings become transforms whose body is
  `sv.sql(...)`.
### Fixes

- Arithmetic on double literals (`3.0 / 2.0`, a `CASE` of double literals
  plus `1.0`) used the integer operators on the literals' codes, which gave
  false proofs; the parser now reads a double literal, a cast to a double or
  such a `CASE` as a double
  ([#97](https://github.com/AlexanderNenninger/substrait-lean/issues/97),
  [#155](https://github.com/AlexanderNenninger/substrait-lean/pull/155)).
- Booleans are ordered FALSE < TRUE, as DataFusion orders them; `b < TRUE`
  was NULL in the model
  ([#154](https://github.com/AlexanderNenninger/substrait-lean/issues/154),
  [#155](https://github.com/AlexanderNenninger/substrait-lean/pull/155)).
- A bare double literal (`SELECT 1.5 AS c`) is written as an `fp64` literal,
  not as an integer holding its code, and `substrait-check` prints such a
  column as doubles. `0.0` and `CAST(NULL AS DOUBLE)` still come out with an
  integer column type (part of
  [#96](https://github.com/AlexanderNenninger/substrait-lean/issues/96),
  [#166](https://github.com/AlexanderNenninger/substrait-lean/pull/166)).
- A `DeltaSink` refused its second write when a guarantee had parentheses
  that Delta drops when it stores a CHECK constraint
  (`(x IS NULL) OR (x > 0)`).

### Moved

| 0.1 | 0.2 |
|---|---|
| `sv.Pipeline`, `pipe.source`, `pipe.view`, `pipe.refresh` | transforms on sources, `node.write(sink)`, `node.refresh()`, `sv.group(...)` (`Pipeline` is internal: `sverify.incremental`) |
| `sv.IncrementalView(con, query, name)`, `view.apply`, `view.rows()` | a transform on a `StaticSource`, `source.apply(sv.Changes(...))`, `node.refresh()`, `node.to_arrow()` (`IncrementalView` is internal) |
| `pipe.view(..., resume=source.stored())` | build the nodes again; the first refresh resumes |
| `DeltaSink(uri, view).write()` | `node.write(DeltaSink(uri))`, written by `refresh` |
| `IcebergSink(catalog, identifier, view).write()` | `node.write(IcebergSink(catalog, identifier))` |
| `sverify.io.SinkWrite`, `sverify.io.IcebergWrite` | `sverify.io.SinkWrite` |
| `sv.StaticSource` | `sverify.io.StaticSource` |
| `sv.Changes` | `sv.Changes` (unchanged) |
| `sv.connect`, `sv.transform`, `sv.verify`, `sv.unique`, `sv.references`, `sv.Report`, `sv.asof_join` | unchanged |
| `sv.run_plan` | `sverify.engines.run` |
| `sv.run_substrait_json` | `sverify.engines.run_substrait_json` |
| `sv.create_table` | `sverify.engines.create_table` |
| `sv.table_rows` | `sverify.engines.table_rows` |
| `sv.ENGINES` | `sverify.engines.ENGINES` |
| `sv.SQL_PRODUCERS` | `sverify.engines.SQL_PRODUCERS` |
| `sv.Connection` | `sverify.engines.Connection` |
| `sv.substrait_json` | `sverify.engines.substrait_json` |
| `sv.isthmus_json` | `sverify.engines.isthmus_json` |
| `sv.written_plan` | `sverify.engines.written_plan` |
| `sv.delta_plans` | `sverify.engines.delta_plans` |
| `sverify.sql.to_sql`, `Dialect`, `Unsupported` | `sverify.engines.to_sql`, `Dialect`, `Unsupported` |
| `sverify.sql.duckdb.DUCKDB`, `sverify.sql.snowflake.SNOWFLAKE`, `sverify.sql.spark.SPARK` | `sverify.engines.DUCKDB`, `SNOWFLAKE`, `SPARK` |
| `sverify.partition.run_sharded` | `sverify.engines.run_sharded` |
| `sverify.spark_engine.run` | `sverify.engines.run_spark` |
| `sverify.spark_engine.SPARK_CONF` | `sverify.engines.SPARK_CONF` |
| `sv.VerificationError` | `sverify.errors.VerificationError` |
| `sv.PreconditionError` | `sverify.errors.PreconditionError` |
| `sv.PostconditionError` | `sverify.errors.PostconditionError` |
| `sv.CompositionError` | `sverify.errors.CompositionError` |
| `sv.NotIncremental` | `sverify.errors.NotIncremental` |
| `sv.SqlError` | `sverify.errors.SqlError` |
| `sverify.incremental.SchemaError` | `sverify.errors.SchemaError` |
| `sverify.incremental.AuditError` | `sverify.errors.AuditError` |
| `sv.Issue`, `sv.References`, `sv.Unique` | internal (`sverify.contracts`); `sv.unique` and `sv.references` build them |
| `sverify.io.ColumnStats`, `sverify.io.stats_facts`, `sverify.io.Stored` | internal (`sverify.io._common`, `sverify.incremental`) |
