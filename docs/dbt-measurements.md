# sverify-dbt on public dbt projects

Sverify measured [sverify-dbt](../dbt/README.md) on two public dbt projects for the 1.0 evidence gate ([#1487](https://github.com/AlexanderNenninger/substrait-lean/issues/1487)). Each run reports three numbers: the models sverify-dbt reads, the declared tests it proves, and the test queries `sverify_proved` leaves out of a run.

The projects are fetched at a pinned commit into a temporary directory and never vendored. [`dbt/scripts/measure.py`](../dbt/scripts/measure.py) does the work, on homelab (`homelab-run --detach`), because Cal-ITP's project is large:

```bash
cd dbt
uv run python scripts/measure.py jaffle_shop
uv run python scripts/measure.py calitp
uv run python scripts/measure.py calitp --types scripts/measure_types/calitp.yml --origins catalog declared
```

dbt 1.12.6 and the DuckDB adapter ran every measurement. sverify-dbt reads DuckDB projects only, so a project written for another warehouse is parsed as DuckDB SQL.

## The projects

| Project | Commit | Warehouse it targets | Data in the run |
|---|---|---|---|
| [dbt-labs/jaffle_shop](https://github.com/dbt-labs/jaffle_shop) (the classic project) | `fd7bfac` | DuckDB-compatible | its seeds, built with `dbt build` |
| [Cal-ITP/data-infra](https://github.com/Cal-ITP/data-infra), `warehouse/` | `546e354` | BigQuery | none: compiled only |

The classic jaffle_shop stands in for its successor, dbt-labs/jaffle-shop, which needs dbt 2. GitLab's analytics project went private, and Cal-ITP's warehouse is the public project closest to it in size: 628 models and 351 declared tests, on BigQuery.

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

Two judgment calls changed a type, and the file lists the columns:

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

## What the numbers say

- On a DuckDB project (jaffle_shop), sverify-dbt reads every model and proves a quarter of the declared tests.
- Source column types decide the second run. Typing 5,379 columns lifted Cal-ITP's reading from 6 models to 13 and moved 600 refusals from "needs column types" to "dialect". A project on DuckDB gets them from `dbt docs generate`.
- Dialect decides the first. A BigQuery project reads at 2.1% raw and 46% with the dialect set apart. The 598 dialect models are not in it, so the BigQuery lift decides how far the rate moves.
- No test was proved on Cal-ITP, so nothing was skipped there. The proof rate waits on a project that sverify-dbt can read, and on the lift.

## Reproducing

`measure.py` takes the commit from `PROJECTS` and prints one JSON record per run: models by class with the top root causes, tests by class, and the savings. A run clones the project into a temporary directory, runs `dbt deps`, applies the types file when `--types` is given, then builds (jaffle_shop) or compiles (Cal-ITP, with `dbt_utils.get_column_values` answered by a stub, since there is no warehouse to ask), then loads and checks the project with `counterexamples=0`.
