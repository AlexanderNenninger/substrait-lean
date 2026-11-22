# sverify-dbt

> Sverify-dbt is a working prototype, and so is sverify, which it builds on.
> Their proofs and code still need a human audit before anyone relies on their
> results.

Sverify-dbt proves a dbt project's data tests and model contracts before
the models run. It reads the project after `dbt compile`, checks each
model's compiled SQL with [sverify](https://github.com/AlexanderNenninger/substrait-lean/blob/main/python/README.md) against the tests on
the models and sources it reads, and reports per model which tests hold on
every run, which may fail and why, and which source tests would let it prove
more. A test it proves can be left out of `dbt build`: it rests on
[`contract_sound`](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/theorems/contract_sound.md) and [`Rel.keys_sound`](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/theorems/keys_sound.md), applied to the model's compiled SQL
under `semantics="duckdb"` ([proofs.md](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/proofs.md)).

It reads DuckDB projects (dbt-duckdb). The other adapters wait on sverify's
other engines, which don't run every function DuckDB does yet
([the issue that tracks them](https://github.com/AlexanderNenninger/substrait-lean/issues/271)).

## Installation

Sverify-dbt is published with sverify, at the same version, from
[substrait-lean](https://github.com/AlexanderNenninger/substrait-lean)'s
releases on:

```bash
# skip: installs software on the reader's machine
pip install sverify-dbt dbt-duckdb
```

## Usage

Compile the project, then check it:

```bash
# skip: needs a dbt project
dbt docs generate   # writes target/catalog.json, where the column types come from
dbt compile --full-refresh   # also after a `dbt run`: a plain compile renders `{{ this }}`
sverify-dbt check .
```

Without the catalog, sverify-dbt takes types from each column's `data_type`
in the YAML. A seed has types in the catalog once `dbt seed` has loaded it and
`dbt docs generate` has run. It refuses a model whose inputs have none. After a `dbt run`, a plain `dbt compile`
renders each incremental model's `is_incremental()` branch, which reads
`{{ this }}`; sverify-dbt refuses it and asks for `dbt compile --full-refresh`.

On the sample project in [`examples/shop`](examples/shop):

```
stg_orders (models/staging/stg_orders.sql)
  proved before the model runs (dbt build may skip them):
    not_null(order_id)
    unique(order_id)
    not_null(customer_id)
    accepted_values(status)
    dbt_utils.accepted_range(amount)

customer_revenue_by_category (models/marts/customer_revenue_by_category.sql)
  proved before the model runs (dbt build may skip them):
    dbt_utils.accepted_range(books)
  contract: columns and types match
    primary_key(customer_id): proved
  note: rows may tie in an ORDER BY of a window or ordered aggregate, so DuckDB picks the order: a test that depends on it is not proved

orders_with_city (models/marts/orders_with_city.sql)
  proved before the model runs (dbt build may skip them):
    not_null(order_id)
    unique(order_id)

org_depth (models/marts/org_depth.sql)
  refused: sverify cannot read WITH RECURSIVE yet (#320)

subscription_arr (models/marts/subscription_arr.sql)
  proved before the model runs (dbt build may skip them):
    dbt_utils.accepted_range(arr)
```

`--selectors` adds a selector, `sverify_proved`, to the project's
`selectors.yml` (keeping the others), and `dbt build` skips the tests it
selects:

```bash
# skip: needs a dbt project
sverify-dbt check . --selectors
dbt build --exclude selector:sverify_proved
```

`sverify-dbt suggest` prints the tests that would let sverify prove more,
as a dbt properties file to merge into the project's YAML: what each model
needs, and the tests on its inputs under which an unproved test would hold,
each with its reason as a comment (`--output FILE` writes it). Where a NULL comes through an expression of the model, such as `cast(ordered_at as date)`, it also tries `not_null` on the columns of the inputs that no test covers, and names the ones the proof needs. Merge them
by hand, and tighten a bound where your data allows:
[`examples/shop/PROOF-STATUS.md`](examples/shop/PROOF-STATUS.md) shows one.

```bash
# skip: needs a dbt project
sverify-dbt suggest .
```

The other options of `check`:

| Option | What it does |
|---|---|
| `--select MODEL ...` | Report on these models (their upstream models are checked too); not with `--selectors`, which needs the whole project |
| `--format text\|json\|github\|sarif\|junit` | How to print the result (default `text`): `github` is one annotation per finding on the model's file, `sarif` a code-scanning log, `junit` a suite per model; `sverify check` forwards its own |
| `--timeout SECONDS` | Seconds for the whole project check (default `$SVERIFY_TIMEOUT`, else no limit); exit 4 past it |
| `--memory-limit SIZE` | DuckDB's memory limit, such as `2GB` (default `$SVERIFY_MEMORY_LIMIT`); exit 4 past it |
| `--json` | Print the result as JSON (`--format json`): the document of `sverify check --format json` ([`cli.schema.json`](../python/src/sverify/schemas/cli.schema.json)), with each model as an item and `findings`, `exit`, `status`, `adapter` and `dbt_version` beside the project's own keys |
| `--counterexamples N` | Small inputs to try per unproved test (default 200; 0 skips the search) |
| `--fail-on` | Exit 1 on a contract mismatch, an unproved constraint, or a refused model with an enforced contract, whose contract sverify could not check (`contract`, the default; stderr names the refusal); `unproved`: also on any unproved test; `refused`: all of that, and exit 3 when a model was refused (sverify cannot read it); `never` |
| `--target-path` | The target directory, if not `target` |

Exit codes, as in `sverify check`: 0 holds, 1 something is not proved, 2 usage (no manifest, an unknown model, another adapter), 3 a model is refused under `--fail-on refused` or the check is unsupported, 4 past `--timeout` or `--memory-limit`, 6 an error (the checker is missing, an I/O failure) with its message on stderr.

The same from Python:

```python
# skip: needs a compiled dbt project at path/to/project
import sverify_dbt

result = sverify_dbt.check("path/to/project")
print(result)
result["stg_orders"].by_status("proved")
result.write_selectors("path/to/project/selectors.yml")
```

## How a project becomes contracts

Each model is checked on its own, the way dbt builds it. Its compiled SQL is
`sverify.verify`'s query, under DuckDB's semantics (`semantics="duckdb"`),
over its `ref`s and `source`s. Their column types come from
`target/catalog.json` when `dbt docs generate` wrote one, else from the
`data_type`s in the YAML (a seed's `column_types` among them), and for a
model from DuckDB's types for its SQL.

- The tests on what a model reads are its preconditions (`requires`).
  `dbt build` runs them first and skips the models downstream of a failure,
  so they hold whenever the model runs. A test with severity `warn`, or
  thresholds (`error_if`, `fail_calc`), lets the build go on, and counts only
  once it is proved.
- The model's own tests are its postconditions (`ensures`). A proved test
  holds on every run whose inputs pass their tests.
- An enforced contract (`contract: {enforced: true}`) is checked too: its
  columns and types against the model's result, and its constraints
  (`not_null`, `unique`, `primary_key`, `check`) as postconditions, before
  dbt's own check at build time.

Only tests carry from one model to the next. A key that sverify proves of a
model's result, but that no test states, is unknown to the models
downstream; add the test and it carries.

The tests sverify-dbt reads:

| Test | Condition on each row |
|---|---|
| `not_null`, `dbt_expectations.expect_column_values_to_not_be_null` | `c IS NOT NULL` |
| `accepted_values`, `dbt_expectations.expect_column_values_to_be_in_set` | `c IS NULL OR c IN (...)` |
| `dbt_expectations.expect_column_values_to_not_be_in_set` | `c IS NULL OR c NOT IN (...)` |
| `dbt_utils.accepted_range`, `dbt_expectations.expect_column_values_to_be_between` | `c IS NULL OR (c >= min AND c <= max)`, strict where the test says |
| `dbt_utils.not_accepted_values` | `c IS NULL OR c NOT IN (...)` |
| `dbt_utils.not_empty_string` | `c IS NULL OR trim(c) <> ''` |
| `dbt_expectations.expect_column_values_to_[not_]match_regex[_list]` | `c IS NULL OR regexp_matches(c, re)`, joined by `match_on` (any or all) |
| `dbt_expectations.expect_column_values_to_[not_]match_like_pattern[_list]` | `c IS NULL OR c LIKE p`, joined by `match_on` |
| `dbt_expectations.expect_column_value_lengths_to_equal`, `…_to_be_between` | `c IS NULL OR length(c) …` |
| `dbt_expectations.expect_column_pair_values_A_to_be_greater_than_B`, `…_values_to_be_equal` | `coalesce(A > B, TRUE)`, `coalesce(A = B, TRUE)` |
| `dbt_utils.expression_is_true` | `coalesce(expression, TRUE)` |
| `unique`, `dbt_expectations.expect_column_values_to_be_unique` | a key (`sv.unique`) |
| `dbt_utils.unique_combination_of_columns`, `dbt_expectations.expect_compound_columns_to_be_unique` | a key over the columns |
| `relationships` | a foreign key (`sv.references`), as a precondition only |

NULLs pass each test, as they do in dbt. A test's `where` config and
dbt-expectations' `row_condition` limit the condition to the rows they keep.
dbt's `unique` lets NULLs repeat while a key counts them as one value, so a
`unique` test is a precondition only on a column a `not_null` test covers too.

When the proof needs a precondition no test states, such as a bound that
rules out an overflow, the model's tests stay unproved and the report lists
the test to add under `needs`, as YAML for the input's column (sverify's
`Report.needs`).

## Limits

- Generic data tests only. Singular tests and unit tests (`given`/`expect`)
  are listed as not checked.
- A model is refused where sverify cannot read its SQL (`WITH RECURSIVE`),
  with the construct named, and where it reads a table that is no `ref` or
  `source`.
- Sverify tracks a column's strings while they are few (up to 64), from
  constants, `IN` lists, `=` and `<>` filters, `CASE`, `COALESCE` and
  `UNION ALL`, which proves `accepted_values` there;
  what is inside a string (`LIKE`, regexes, lengths) is not tracked, so those
  tests are proved where the same test holds upstream and the column passes
  through ([the guide](../docs/guide.md#contracts)). Sverify reads no regex
  flags, so a regex test with `flags` is not checked.
- Python models, and models whose inputs have no column types, are refused.
- What each materialization gets: a table or view is checked; an incremental
  model as its full refresh (below); an ephemeral model is inlined, so its
  readers are read through it and it prints a note, with no test run on it; a
  snapshot is an input only. Python models are refused.
- An incremental model is checked as its full refresh, as `dbt compile`
  renders it; its `is_incremental()` block is taken to only filter that query.
  Its tests are skippable (`--selectors`) only under `merge` or `delete+insert`
  on a `unique_key` that a proved `unique` test names, and then only the
  row-level tests (`not_null`, `accepted_values`, `accepted_range`,
  `expression_is_true`) and `unique` over that key or more columns: other
  proved tests are listed as proved for the full refresh, and `dbt build`
  still runs them.

## Evidence

`python -m sverify_dbt.replay` builds the integration projects of
dbt-utils 1.4.1 and dbt-expectations 0.10.10, and the 175 distinct projects
of the pytest classes in dbt-tests-adapter 1.20.0, with dbt on DuckDB, checks
them with sverify-dbt and records every test beside dbt's own result, in
[`replay/`](replay/) (#859). No test sverify-dbt proves fails in dbt's run.

| Source | Proved | Not proved | Not checked | Refused | Inputs |
|---|---|---|---|---|---|
| dbt-utils 1.4.1 | 3 | 13 | 45 | 15 | 37 |
| dbt-expectations 0.10.10 | 0 | 33 | 9 | 115 | 0 |
| dbt-tests-adapter 1.20.0 | 8 | 11 | 85 | 11 | 13 |

These projects test macros more than they model data: most of their tests
compare two relations or match patterns with flags, which sverify-dbt leaves
to dbt by design, and most of dbt-expectations' models cast to float32,
which Lean's model does not cover
([#417](https://github.com/AlexanderNenninger/substrait-lean/issues/417)),
or use `random()`. Every refusal and test not checked names its issue or the
reason it is by design ([`replay/constructs.json`](replay/constructs.json)).
The adapter suite's classes whose fixtures need a running warehouse, and the
projects dbt cannot build, are listed under `unextracted` in its ledger.
CI's `dbt` job replays them and warns when an outcome changes.

## Development

```bash
# skip: builds or tests the repository, which needs elan and takes minutes
cd dbt
uv sync
uv run pytest
```

`uv sync` installs the sverify of this checkout (`../python`), with the
checker its build hook links or builds.

The tests compile the sample project and a few small ones with dbt's own
runner. CI runs them, then the check of `examples/shop`, and `dbt build`
without the proved tests (the `dbt` job of
[ci.yml](../.github/workflows/ci.yml)). [API-NOTES.md](API-NOTES.md) lists
what building on sverify's public API showed.
