# sverify-dbt

Sverify-dbt proves a dbt project's data tests and model contracts before
the models run. It reads the project after `dbt compile`, checks each
model's compiled SQL with [sverify](https://github.com/AlexanderNenninger/substrait-lean/blob/main/python/README.md) against the tests on
the models and sources it reads, and reports per model which tests hold on
every run, which may fail and why, and which source tests would let it prove
more. A test it proves can be left out of `dbt build`: it rests on
`contract_sound` and `Rel.keys_sound`, applied to the model's compiled SQL
under `semantics="duckdb"` ([proofs.md](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/proofs.md)).

It reads DuckDB projects (dbt-duckdb). The other adapters wait on sverify's
other engines ([#271](https://github.com/AlexanderNenninger/substrait-lean/issues/271)).
The design is in [#177](https://github.com/AlexanderNenninger/substrait-lean/issues/177).

## Installation

Sverify-dbt is published with sverify, at the same version, from
[substrait-lean](https://github.com/AlexanderNenninger/substrait-lean)'s
releases on
([#732](https://github.com/AlexanderNenninger/substrait-lean/issues/732)):

```bash
pip install sverify-dbt dbt-duckdb
```

## Usage

Compile the project, then check it:

```bash
dbt compile
sverify-dbt check .
```

On the sample project in [`examples/shop`](examples/shop):

```
stg_orders (models/staging/stg_orders.sql)
  proved before the model runs (dbt build may skip them):
    not_null(order_id)
    unique(order_id)
    not_null(customer_id)
    dbt_utils.accepted_range(amount)
  not proved (dbt build still runs them):
    accepted_values(status): sverify cannot rule out a row that fails it, from the tests upstream

customer_revenue_by_category (models/marts/customer_revenue_by_category.sql)
  not proved (dbt build still runs them):
    dbt_utils.accepted_range(books): sverify cannot rule out a row that fails it, from the tests upstream
  contract: columns and types match
    primary_key(customer_id): proved

org_depth (models/marts/org_depth.sql)
  refused: sverify cannot read WITH RECURSIVE yet

subscription_arr (models/marts/subscription_arr.sql)
  not proved (dbt build still runs them):
    dbt_utils.accepted_range(arr): proved only with the source tests listed under 'needs'
  needs these tests before anything is proved:
    on source('app', 'subscriptions'), column mrr: dbt_utils.accepted_range: {arguments: {max_value: 700000000000000000, inclusive: false}}
      (overflow in `mrr * 12` otherwise)
```

`--selectors` adds a selector, `sverify_proved`, to the project's
`selectors.yml` (keeping the others), and `dbt build` skips the tests it
selects:

```bash
sverify-dbt check . --selectors
dbt build --exclude selector:sverify_proved
```

`sverify-dbt suggest` prints the tests that would let sverify prove more,
as a dbt properties file to merge into the project's YAML: what each model
needs, and the tests on its inputs under which an unproved test would hold,
each with its reason as a comment (`--output FILE` writes it). Merge them
by hand, and tighten a bound where your data allows:
[`examples/shop/PROOF-STATUS.md`](examples/shop/PROOF-STATUS.md) shows one.

```bash
sverify-dbt suggest .
```

The other options of `check`:

| Option | What it does |
|---|---|
| `--select MODEL ...` | Report on these models (their upstream models are checked too) |
| `--json` | Print the result as JSON |
| `--counterexamples N` | Small inputs to try per unproved test (default 200; 0 skips the search) |
| `--fail-on` | Exit with status 1 on a contract mismatch or an unproved constraint (`contract`, the default), also on any unproved test or refused model (`unproved`), or `never` |
| `--target-path` | The target directory, if not `target` |

The same from Python:

```python
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
`Report.needed`).

## Limits

- Generic data tests only. Singular tests and unit tests (`given`/`expect`)
  are listed as not checked.
- A model is refused where sverify cannot read its SQL (`WITH RECURSIVE`),
  with the construct named, and where it reads a table that is no `ref` or
  `source`.
- Sverify tracks a column's strings while they are few (up to 64), from
  constants, `IN` lists, `=` and `<>` filters, `CASE`, `COALESCE` and
  `UNION ALL`, which proves `accepted_values` there
  ([#708](https://github.com/AlexanderNenninger/substrait-lean/issues/708));
  what is inside a string (`LIKE`, lengths) is not tracked
  ([the guide](../docs/guide.md#contracts)).
- Python models, and models whose inputs have no column types, are refused.
- An incremental model is checked as its full refresh, as `dbt compile`
  renders it.

## Development

```bash
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
