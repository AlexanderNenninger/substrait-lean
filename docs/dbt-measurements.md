# sverify-dbt on public dbt projects

Sverify measured [sverify-dbt](../dbt/README.md) on two public dbt projects for the 1.0 evidence gate ([#1487](https://github.com/AlexanderNenninger/substrait-lean/issues/1487)). Each run reports three numbers: the models sverify-dbt reads, the declared tests it proves, and the test queries `sverify_proved` leaves out of a run.

The projects are fetched at a pinned commit into a temporary directory and never vendored. [`dbt/scripts/measure.py`](../dbt/scripts/measure.py) does the work, on homelab (`homelab-run --detach`), because Cal-ITP's project is large:

```text
cd dbt
uv run python scripts/measure.py jaffle_shop
uv run python scripts/measure.py calitp
uv run python scripts/measure.py calitp --types scripts/measure_types/calitp.yml --origins catalog declared
uv run python scripts/measure.py jaffle_shop --overlay scripts/measure_overlays/jaffle_shop.yml
uv run python scripts/measure.py calitp --types scripts/measure_types/calitp.yml --origins catalog declared --transpile
```

dbt 1.12.6 and the DuckDB adapter ran every measurement. sverify-dbt reads DuckDB projects only, so a project written for another warehouse is parsed as DuckDB SQL.

## The projects

| Project | Commit | Warehouse it targets | Data in the run |
|---|---|---|---|
| [dbt-labs/jaffle_shop](https://github.com/dbt-labs/jaffle_shop) (the classic project) | `fd7bfac` | DuckDB-compatible | its seeds, built with `dbt build` |
| [Cal-ITP/data-infra](https://github.com/Cal-ITP/data-infra), `warehouse/` | `546e354` | BigQuery | none: compiled only |

The classic jaffle_shop stands in for its successor, [dbt-labs/jaffle-shop](https://github.com/dbt-labs/jaffle-shop), which needs dbt 2. [GitLab's analytics project](https://gitlab.com/gitlab-data/analytics) went private (it now redirects to a sign-in), and Cal-ITP's warehouse is the public project closest to it in size: 628 models and 351 declared tests, on BigQuery.

## Results

### jaffle_shop

| | Count | Share |
|---|---|---|
| Models read | 5 of 5 | 100% |
| Declared tests | 20 | |
| Tests proved | 5 | 25% |
| Tests not proved | 14 | 70% |
| Tests not checked | 1 | 5% |
| Test queries skipped by `sverify_proved` | 5 of 20 | 25% |

dbt ran the 20 tests in 1.45 s on DuckDB, and the 5 skipped ones took 0.29 s of it (20%). All of dbt's tests passed.

A dollar saving depends on the warehouse. Each skipped test is one query the warehouse does not bill, so the saving per run is the cost of a query on the warehouse in use times the skipped count, and DuckDB's seconds are the stand-in here.

### Cal-ITP

Sverify-dbt needs a column type for every source column: from `catalog.json` or from a `data_type` in the sources' YAML. Cal-ITP declares none, so the project as published has no types. The types file [`dbt/scripts/measure_types/calitp.yml`](../dbt/scripts/measure_types/calitp.yml) supplies them. It lists 5,379 columns of 182 source tables, taken from the catalog Cal-ITP publishes at [dbt-docs.dds.dot.ca.gov](https://dbt-docs.dds.dot.ca.gov/catalog.json), each with its origin (`catalog`). No column carries an inferred type, so the third reading below equals the second.

The file lists the columns behind two judgment calls on types and one omission:

- `NUMERIC` and `BIGNUMERIC` (about 1,576 columns) become `DECIMAL(38,9)`.
- `TIMESTAMP` becomes `TIMESTAMPTZ` and `DATETIME` becomes `TIMESTAMP`.
- One `GEOGRAPHY` column (`state_highway_network.wkt_coordinates`) has no DuckDB type and stays untyped.

Two models do not compile under dbt-duckdb (dbt reports an error for each, and `measure.py` leaves out each with its descendants). They count in the denominator as the class "doesn't compile under dbt-duckdb", and so do the 2 tests declared on them.

| Models | As published | With catalog types |
|---|---|---|
| Total | 628 | 628 |
| Read | 6 (1.0%) | 13 (2.1%) |
| Refused, needs the warehouse's column types | 617 | 9 |
| Refused, doesn't compile under dbt-duckdb | 2 | 2 |
| Refused, dialect (the SQL is not DuckDB's) | 3 | 598 |
| Refused, other | 0 | 6 |

| Tests | As published | With catalog types |
|---|---|---|
| Declared | 351 | 351 |
| Proved | 0 | 0 |
| On a model that needs column types | 347 | 0 |
| On a model whose SQL is not DuckDB's | 0 | 347 |
| On a model that does not compile under dbt-duckdb | 2 | 2 |
| On a source or seed | 2 | 2 |
| Test queries skipped | 0 | 0 |

With the refusals that come only from reading a BigQuery project as DuckDB set apart (the dialect class and the two uncompiled models), the typed run reads 13 of the 28 models left, 46%. Refusals of the sverify class remain in that denominator: the 9 models that still need column types and the 6 others. Reading BigQuery SQL is the Snowflake and BigQuery lift's job ([#866](https://github.com/AlexanderNenninger/substrait-lean/issues/866), After 1.0). Cal-ITP therefore measures how much of a BigQuery project's SQL is also DuckDB SQL. It says little about sverify-dbt on a DuckDB project.

The dialect refusals, by root cause (the typed run):

- 350 models: `DuckDB cannot plan the compiled SQL: Parser Error: zero-length delimited identifier`. The compiled SQL quotes with BigQuery's backticks.
- 35 models: `timestamp_seconds` does not exist in DuckDB.
- Most of the rest: `the compiled SQL does not parse: Expecting )`.

The full list is in each run's JSON record (`top_root_causes`).

### jaffle_shop with source assumptions

The tests of jaffle_shop sit on its staging models, and none sits on a seed, so sverify-dbt finds no key and no non-null column under them. [`dbt/scripts/measure_overlays/jaffle_shop.yml`](../dbt/scripts/measure_overlays/jaffle_shop.yml) adds what a user would declare on the seeds, applied on top of the pinned commit with `--overlay`:

- `unique` and `not_null` on `raw_customers.id`, `raw_orders.id` and `raw_payments.id`.
- `not_null` on `raw_orders.user_id`, `raw_payments.order_id` and `raw_payments.amount`.
- `accepted_values` on `raw_orders.status` and `raw_payments.payment_method`, with the values of the project's own staging tests.
- `relationships` from `raw_orders.user_id` to `raw_customers.id` and from `raw_payments.order_id` to `raw_orders.id`.

dbt still runs these 13 tests, and all of them pass, so each assumption holds on the data.

| | As published | With source assumptions |
|---|---|---|
| Declared tests | 20 | 33 |
| Proved | 5 | 13 |
| The project's own 20 tests, proved | 5 (25%) | 13 (65%) |
| All declared tests, proved | 5 of 20 (25%) | 13 of 33 (39%) |
| Test queries skipped | 5 of 20 | 13 of 33 |
| Test time skipped on DuckDB | 0.29 of 1.45 s | 0.80 of 2.42 s |

The 8 staging tests (`unique` and `not_null` on each key, `accepted_values` on `status` and `payment_method`) turn proved: each is a rename of the seed column that carries the same test. The 13 tests on seeds are dbt's to run, and `sverify_proved` never skips them.

The 7 tests that stay open, in both readings:

| Test | Status | Why |
|---|---|---|
| `orders.not_null(customer_id)` | not proved | sverify-dbt reads the tests on the models `orders` reads, so it needs `not_null(customer_id)` on `stg_orders`. The seed's `not_null(user_id)` then proves that test, but the suggestion is a test on the staging model, not a seed assumption. |
| `orders.relationships(customer_id)` | not checked | sverify-dbt proves no foreign key of a model's result. dbt runs it. |
| `orders.not_null(amount)` and the four `*_amount` columns | not proved | `orders` left-joins the per-order payment sums, so each amount is NULL for an order without payments. The data has none, and the plan does not say so. A proof needs an assumption that every order has a payment and a join analysis that uses it, which sverify does not have. |

### Cal-ITP transpiled to DuckDB

`--transpile` rewrites each model's compiled SQL in the manifest from BigQuery to DuckDB with [SQLGlot](https://github.com/tobymao/sqlglot) (`read="bigquery"`, `write="duckdb"`), mechanically and with no hand edits. A model SQLGlot fails on keeps its BigQuery SQL. The run also uses the 5,379 catalog types.

| | Count | Share |
|---|---|---|
| Models | 628 | |
| SQLGlot transpiles | 583 | 93% |
| SQLGlot fails on | 41 | 7% |
| Models read | 66 | 10.5% of 628 |
| Transpiled models read | 64 | 11% of 583 |
| Tests on transpiled models | 347 | |
| Tests proved | 0 | 0% of 351 |

Of the 351 declared tests, 5 sit on models sverify-dbt reads (2 not proved, 3 not checked). The other 346 sit on refused models: 210 on dialect refusals, 107 on other refusals, 25 on models that need column types, 2 on models that do not compile and 2 on sources.

Models by class after transpiling: 66 read, 100 need column types, 2 do not compile under dbt-duckdb, 299 dialect, 161 other. With the dialect class and the 2 uncompiled models set apart, the rate is 66 of 327 (20%).

The top refusal causes after transpiling:

- 87 models: a source or ref still has no column types (the catalog lacks those tables).
- About 230 models: SQLGlot's DuckDB output does not parse (`Required keyword: … missing`), mostly in one construct repeated across the models.
- 40 models: `TRY_CAST` of a non-string.
- 39 models: `UNHEX(MD5(…))`, which sverify cannot read yet.
- 17 models: `st_geogpoint` does not exist in DuckDB.
- 12 models: a string cast to a decimal (#27).

SQLGlot can change what a query means. A translation is correct when BigQuery and DuckDB agree on the function, the types, the NULL handling and the timestamp zones. Sverify checks the translated SQL as DuckDB SQL, and no oracle here compares it with BigQuery, so a number read from a transpiled model says what the DuckDB reading proves and nothing about BigQuery. The read rate therefore bounds how much of Cal-ITP the SQLGlot translation delivers.

## What the numbers say

- On a DuckDB project (jaffle_shop), sverify-dbt reads every model and proves a quarter of the declared tests.
- Source column types decide the second run. Typing 5,379 columns lifted Cal-ITP's reading from 6 models to 13 and cut the refusals that need column types from 617 to 9 and raised the dialect refusals from 3 to 598. A project on DuckDB gets them from `dbt docs generate`.
- Dialect decides the first. A BigQuery project reads at 2.1% raw and 46% with the dialect set apart. The 598 dialect models are not in it, so the BigQuery lift decides how far the rate moves.
- jaffle_shop's rate depends on what the seeds declare: 25% as published, 65% of the project's own tests with the seeds' keys and values declared. The 7 tests left need sverify's own work.
- Transpiling with SQLGlot lifts Cal-ITP's reading from 2.1% to 10.5%. It proved no test, because 346 of the 351 sit on models still refused.
- No test was proved on Cal-ITP, so nothing was skipped there. The proof rate waits on a project that sverify-dbt can read, and on the lift.

## Reproducing

`measure.py` takes the commit from `PROJECTS` and prints one JSON record per run: models by class with the top root causes, tests by class, and the savings. A run clones the project into a temporary directory, runs `dbt deps`, applies the types file when `--types` is given, then builds (jaffle_shop) or compiles (Cal-ITP, with `dbt_utils.get_column_values` answered by a stub, since there is no warehouse to ask), then loads and checks the project with `counterexamples=0`.
