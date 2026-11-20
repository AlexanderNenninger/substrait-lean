# sverify

> Sverify is a working prototype. Its Lean proofs, its checker and its Python
> code still need a human audit before anyone relies on their results.
>
> [How this project is built](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/how-this-is-built.md)
> says who writes it and what you can check yourself.

Sverify proves a data pipeline's contracts in Lean before it runs, keeps the
result up to date from Delta and Iceberg changes, and runs the checked plan on
DuckDB, Polars and Spark.

It finds the bugs that tests on sample data miss:

* A duplicate that arrives late, or a payment that is reversed, in an
  incremental job
  ([the tour's first notebook](https://molab.marimo.io/github/AlexanderNenninger/substrait-lean/blob/published/notebooks/01_duplicate_payments.py)).
* Ties and NaN readings that change a window's result, and SQL that only
  runs alike on some engines
  ([second notebook](https://molab.marimo.io/github/AlexanderNenninger/substrait-lean/blob/published/notebooks/02_sensor_alerts.py)).
* A dbt test on a point-in-time join to a type-2 dimension, proved as a
  contract, and the promises a left join's NULL padding
  breaks
  ([third notebook](https://molab.marimo.io/github/AlexanderNenninger/substrait-lean/blob/published/notebooks/03_orders_mart.py),
  [what a left join keeps](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/proved-theorems.md#contracts)).
* Division by zero, integer overflow and bad casts
  ([the runtime-error theorems](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/proved-theorems.md#runtime-errors)).

[How sverify compares](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/comparison.md) with dbt tests, Great Expectations,
Soda and data contracts says what it does not do.

## In thirty lines

```python
import pyarrow as pa
import sverify as sv
from ibis import _
from sverify.io import Changes, StaticSource

orders = StaticSource(  # in memory; DeltaSource and IcebergSource work the same way
    pa.table({"id": [1, 2], "customer": ["ada", "bob"], "amount": [30, 5]}), name="orders"
)


# The upper bound on amount keeps `amount * 2` within 64 bits. Leave it out and
# the report names the bound to declare.
@sv.transform(
    requires={"orders": [_.amount >= 0, _.amount < 1_000_000_000, sv.unique("id")]},
    ensures=[_.doubled >= 22, _.doubled.notnull(), sv.unique("id")],
)
def big_orders(orders):
    return orders.filter(orders.amount > 10).select(orders.id, doubled=orders.amount * 2)


big = orders.pipe(big_orders)  # proved here, before any data runs
big.refresh()  # computed, on DuckDB by default
orders.apply(Changes(inserts=[(3, "cy", 50)], deletes=[(1, "ada", 30)]))
big.refresh(engine="polars", route="auto")  # updated from the changes alone, on Polars
assert big.to_arrow().to_pylist() == [{"id": 3, "doubled": 100}]
print(big_orders.report)
# proved
# The output guarantees:
#   doubled ≥ 22
#   doubled is never NULL
#   no two rows share id
# Each run checks on the data:
#   orders: amount ≥ 0
#   orders: amount < 1000000000
#   orders: no two rows share id
# ...
```

`print(big_orders.report.details())` goes on with the evidence for each engine; `sverify check` prints the same contract.

A postcondition that doesn't follow is refused before anything runs:

```python
@sv.transform(requires={"orders": [_.amount >= 0]}, ensures=[_.total > 5])
def plus_one(orders):
    return orders.select(orders.id, total=orders.amount + 1)


from sverify.errors import VerificationError

try:
    plus_one(orders)
except VerificationError as e:
    print(e)
# 1 of 1 postcondition not proved, 1 precondition needed (e.report has the details)
#   ...
#   not proved: (_.total > 5): it may be FALSE on some rows ...
#     would hold with `(_.amount >= 5)` in the requires of 'orders'
```

## Install

```bash
pip install sverify                # or: uv add sverify; verifies, runs nothing
pip install 'sverify[duckdb]'      # and runs plans on DuckDB, the default engine
pip install 'sverify[all]'         # with every engine in the 1.x promise and both table formats
```

The core verifies without an engine and writes DuckDB and Snowflake SQL; `sverify[spark]` adds Spark SQL (`report.to_sql("spark")` raises `unknown dialect` without it). Extras:
`polars`, `spark` (needs Java 17 or 21), `delta`, `iceberg`,
`flight`, `testing`, `odcs`, `openlineage`, or `all`.
The `polars` and `spark` extras install the engine packages `sverify-polars`
and `sverify-spark` with their runtimes; either package alone
(`pip install sverify-spark`) verifies under its engine's semantics and
writes its SQL without the runtime. Sverify finds every installed engine
through its plugin (`sverify.profiles.ProfilePlugin`, the entry-point group
`sverify.profiles`). Wheels bundle the checker as a small native binary for Linux (x86_64,
aarch64) and macOS (arm64), Python 3.12 and later. Elsewhere (Windows, an Intel Mac) the
sdist's build stops with a message; use WSL2 or a Linux container, or set
`SVERIFY_BUILD_FROM_SOURCE=1` to build from source, which needs
[elan](https://github.com/leanprover/elan) and starts a full `lake build` of every generated Lean module,
minutes of work that can load every core.
Contributors with a built checker set `SVERIFY_PREBUILT_CHECKER=<path to substrait-check>`, and an editable install links it instead.

## In CI

`sverify check` proves every transform and node in a pipeline file and
exits 0 when all are proved, 1 when one is not, and 3 when a construct is
outside sverify's model (the other codes are in
[the guide](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/tasks.md#the-command-line)). `--format sarif` writes a
report for GitHub's code scanning.

```bash
sverify check pipelines/orders.py
```

## Go on from here

[Getting started](https://alexandernenninger.github.io/substrait-lean/examples/examples.html) goes in ten steps from a first contract to
Substrait's own semantics, each feature in a few lines.

The [API reference](https://alexandernenninger.github.io/substrait-lean/)
documents every public function and class of the released version, with the
[examples](https://alexandernenninger.github.io/substrait-lean/examples/examples.html)
and the [ledgers](https://alexandernenninger.github.io/substrait-lean/ledgers/):
the upstream bugs and Substrait spec gaps sverify found, and each engine's
characterization, searchable by id, engine, function and option. For
coding agents, the site also publishes
[skills](https://alexandernenninger.github.io/substrait-lean/skills.html) for
writing contracts, pipelines and engine code with sverify
(`npx skills add https://alexandernenninger.github.io/substrait-lean/`); they
ship in the wheel too, under `sverify/skills/`.

## What sverify proves

In sverify you write a data transformation as usual, in
[Ibis](https://ibis-project.org) or SQL, and state what it assumes about its
inputs (`requires`) and what it guarantees about its output (`ensures`). A
checker written in [Lean](https://lean-lang.org) proves the guarantees for
every possible input, or says why it can't ([what is proved](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/proved-theorems.md)). Then:

* Contracts are proved before the job runs. `not_null`, `unique`, ranges and
  relations between columns hold on every input that meets the
  preconditions, and division by zero, overflow and bad casts are ruled out
  before the job runs. The preconditions you state, and those Sverify
  infers, are checked on each batch before the run, or proved from Delta
  and Iceberg metadata, and a batch that breaks one is refused before
  anything runs. The [runtime-error theorems](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/proved-theorems.md#runtime-errors) list what is ruled out.
* A route takes the proof to the engine. `route="auto"` runs the plan on
  DuckDB, Polars or Spark natively, through the reference's proved translation, or
  by a check that the engine's choices are within the proof's, and names
  the plan's class there: exact, equal under an observation the
  postcondition states (a float tolerance is one), or exact or observed
  after a proved shim. Where no route
  applies, the plan is refused with the reason
  ([routes and classes](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/guide.md#routes-classes-and-profiles)). DuckDB,
  Polars and Spark are characterized fact by fact, with the evidence for each
  ([the ledgers](https://alexandernenninger.github.io/substrait-lean/ledgers/)).
* Postconditions say what the result's consumer observes. By default,
  doubles within the plan's proved bound (`floats="plan"`, which the report
  prints); `sv.equivalent(floats=sv.within(abs=1e-6))` states a tolerance,
  which `verify` checks against that bound, and also rows as a sequence or
  a multiset, one zero. A sink states what a
  rerun must reproduce (`reproducible=`), and a refresh whose engine can't
  promise it is refused.
* Results are kept up to date from the changes, by delta plans proved
  equal to a full recompute ([`Rel.delta_correct`](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/proved-theorems.md#incremental-view-maintenance)), read from Delta's Change Data Feed or Iceberg's
  appends, and written to sinks exactly once, with the contract attached.

## Reference semantics and engines

Sverify checks every plan against a reference semantics, written in Lean,
whose four principles and choices are in
[reference-semantics.md](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/reference-semantics.md#principles).
The reference raises where engines disagree on an answer, so a proved plan
runs alike on each: an operation on finite doubles that overflows to `±∞`,
`power(-inf, 0.5)`, a `MEDIAN` between `-inf` and `+inf`, a constant
subexpression that raises. `AND` and `OR` evaluate both operands, as DuckDB
and Polars do. A plan proved under the reference creates no NaN and no
`±∞` its inputs did not hold. `semantics="duckdb"`, `"polars"` and
`"spark"` check a plan under what that engine does, and
`semantics="substrait"` under Substrait's extension YAMLs, open wherever
they say nothing
([the Substrait profile](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/core-semantics.md#the-substrait-profile)).

Sverify runs plans on DuckDB, Polars and Spark, and writes DuckDB, Spark
and Snowflake SQL. [Engines](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/stability.md#engines)
says which are in the 1.x promise, with their profiles and translations.

Polars refuses what only DuckDB runs so far, with a message that links
[the issue that tracks it](https://github.com/AlexanderNenninger/substrait-lean/issues/271): the functions
that [`SUPPORT` and `WINDOW_SUPPORT`](https://github.com/AlexanderNenninger/substrait-lean/blob/main/python/src/sverify/_support.py)
list without `polars` (`regexp_extract`, `regexp_replace`, `md5`, `sha256`, `first`, `last`,
`string_agg`, `median`, the quantiles, `mode`, `arg_min`, `arg_max`, the covariances,
`corr`, and variances over a window), the black boxes, and `MIN` and `MAX` of doubles.

## Status

Sverify is a working prototype of a pipeline tool: it proves contracts and runs the checked plan. Production shouldn't depend on it yet, as the API will change (sometimes drastically) between minor releases. A name that goes is deprecated for one release, with a `DeprecationWarning` that says what replaces it ([the changelog](https://github.com/AlexanderNenninger/substrait-lean/blob/main/CHANGELOG.md) lists each move), and the 1.0 release candidate removes the ones left ([#1288](https://github.com/AlexanderNenninger/substrait-lean/issues/1288)). It describes each engine as observed at pinned versions, without certifying or ranking it, and isn't affiliated with any engine's project or vendor.

## Nightly builds

Each night, when `main` has changed, the
[`nightly` pre-release](https://github.com/AlexanderNenninger/substrait-lean/releases/tag/nightly) gets its wheels, versioned
`<next minor>.dev<commits>+g<sha>`, so they sort after the latest release. They are not on PyPI:

```bash
uv add "sverify>=0.8.0.dev0" --find-links https://github.com/AlexanderNenninger/substrait-lean/releases/expanded_assets/nightly
pip install --pre sverify --find-links https://github.com/AlexanderNenninger/substrait-lean/releases/expanded_assets/nightly
```

uv keeps the version and drops the page, so add it to your `pyproject.toml`;
`uv lock --upgrade-package sverify` then moves to the latest nightly:

```toml
[tool.uv]
find-links = ["https://github.com/AlexanderNenninger/substrait-lean/releases/expanded_assets/nightly"]
```

Each build's wheels stay on the release for 30 days, so a wheel's own URL pins
one build for that long. `--find-links` sees every build on the page and picks
the newest. Copy a URL from the release page:

```bash
pip install "sverify @ https://github.com/AlexanderNenninger/substrait-lean/releases/download/nightly/sverify-<version>-py3-none-<platform>.whl"
```

## Testing with pytest

`sverify.testing` has assertions for your test suite, and sverify registers a
pytest plugin with two fixtures: `sv_source` makes an in-memory
source from rows, and a test that takes `sv_engine` runs once per installed
engine.

```python
from sverify.testing import assert_contract, assert_engines_agree, source


def test_big_orders():
    orders = source([], {"id": "int64", "customer": "string", "amount": "int64"}, name="orders")
    node = orders.pipe(big_orders)
    assert_contract(node)  # the contract is proved
    data = {"orders": [(1, "ada", 30), (2, "bob", 5)]}
    assert_contract(node, data=data, expected=[(1, 60)])  # and holds on these rows
    assert_engines_agree(node, data)  # every installed engine agrees


test_big_orders()
```

A failure lists the offending rows: those that break a precondition, or the
expected rows that are missing or unexpected.
`sverify.testing.cases(node)` is a Hypothesis strategy of inputs that meet
the preconditions, for property tests of the code around a node
(`pip install 'sverify[testing]'`).

## SQL models

A transform's body can be SQL over its inputs by name. Sverify proves,
composes and refreshes it like any other:

```python
@sv.transform(
    requires={"orders": ["amount >= 0", "amount IS NOT NULL"]},
    ensures=["total >= 0", sv.unique("customer")],
)
def per_customer(orders):
    return sv.sql(
        "SELECT customer, coalesce(sum(amount), 0) AS total FROM orders GROUP BY customer",
        orders=orders,
    )


totals = orders.pipe(per_customer)  # proved here, like an Ibis transform
totals.refresh()
assert sorted(totals.to_arrow().to_pylist(), key=str) == [
    {"customer": "bob", "total": 5},
    {"customer": "cy", "total": 50},
]
```

`sverify check` reads a Python file or a dbt project; a bare `.sql` file is not checked yet, so put the query in `sv.sql` in a `.py` file, or use [sverify-dbt](https://github.com/AlexanderNenninger/substrait-lean/blob/main/dbt/README.md).
Several inputs are several keywords (`sv.sql(query, orders=orders,
customers=customers)`). The SQL is DuckDB's, and sverify plans it itself,
through SQLGlot, with sverify's reference semantics (`semantics="reference"`,
the default) or DuckDB's (`semantics="duckdb"`), for a subset of
SQL so far ([what the SQL lift reads](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/reference-semantics.md)).

## Workflows

Three complete jobs from a catalogue of 139 real analytical queries, each
from source tables to a sink, with what goes wrong without the checker:

* [Duplicate card payments](https://molab.marimo.io/github/AlexanderNenninger/substrait-lean/blob/published/notebooks/01_duplicate_payments.py):
  a self-join over a Delta table, refreshed from its Change Data Feed, where
  a watermark job would miss a late duplicate and keep a reversed one.
* [Sensor alerts](https://molab.marimo.io/github/AlexanderNenninger/substrait-lean/blob/published/notebooks/02_sensor_alerts.py):
  `LAG` over an Iceberg table, where ties and a NaN reading change the alerts,
  and Snowflake and Spark need proved tie-freedom.
* [An orders mart](https://molab.marimo.io/github/AlexanderNenninger/substrait-lean/blob/published/notebooks/03_orders_mart.py):
  dbt tests as a proved contract on a point-in-time join to a type-2
  dimension, in Ibis and in SQL.

The [whole tour](https://github.com/AlexanderNenninger/substrait-lean/tree/main/notebooks)
adds three guides, to contracts, to pipelines and engines, and to running it in production; it runs locally with
`uvx marimo edit --sandbox notebooks` from a clone.

## The API in brief

```python
import ibis
from sverify.io import DeltaSink, DeltaSource  # IcebergSource, IcebergSink likewise

sv.verify(
    "select id, amount from orders where amount > 0",
    tables={"orders": ibis.table({"id": "int64", "amount": "int64"}, name="orders")},
    ensures=["amount > 0"],
)  # SQL, checked; returns the report
# the checked plan as SQL: "snowflake", "duckdb" or "spark", or sverify.engines.UnsupportedError
big.to_sql("snowflake")

# p = DeltaSource("s3://.../orders").pipe(paid).write(DeltaSink("s3://.../paid"))  # stored
# r = p.pipe(revenue, regions=regions).write(DeltaSink("s3://.../revenue"))
# r.refresh(engine="polars"); sv.group(r, other).refresh(); r.to_pandas()
```

* `@sv.transform(requires=..., ensures=..., on_unproved="error" | "check" | "warn")`
  proves a contract on each call; `.report` says what was proved and
  what is known about every output column. `sv.unique(...)` states keys.
* `source.pipe(paid).pipe(revenue, regions=regions)` builds nodes left to
  right, in the order the data flows (the call form `revenue(paid(source),
  regions=regions)` is the same node). A step is a transform, SQL
  (`sv.sql(query)`, which binds the chained node to the one table the
  keywords leave over) or a plain function. A downstream precondition is
  proved from the upstream contract (`CompositionError` names a broken
  link).
* Without `.write` in between, transforms fuse into one plan; `.write(sink)`
  stores a node, exactly once per state, and nodes downstream read it as a
  versioned source. `refresh(engine=...)` updates the whole lineage, and
  `sv.group(a, b)` several outputs against the same source versions.
* Filters, projections, inner, cross, semi and anti joins, `UNION ALL`,
  `DISTINCT`, and `COUNT`, exact `SUM` and `AVG`, `MIN` and `MAX` per group
  are maintained from the changes. Another aggregate recomputes only the
  groups a batch touches, and a window only the partitions it touches;
  anything else is recomputed and diffed
  ([what refresh maintains](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/tasks.md#nodes-composing-storing-refreshing)).
* `sverify.io` has Delta, Iceberg and in-memory sources and sinks, and
  base classes for your own: a `Source` implements `read(since)`
  (`from_query`, `from_frame` and `from_files` build one), a `Sink`
  implements `write(change)` (`sink_from` wraps a function).
* `sverify.testing` has `assert_contract`, `assert_engines_agree` and the
  Hypothesis strategy `cases` for pytest, with the plugin's `sv_engine` and
  `sv_source` fixtures.
* `report.run(con, engine, route="auto")` runs a proved plan on an
  engine by a route (`report.routes` records it, with its class), and
  `refresh(engine=..., route="auto")` does the same for each node.
  `sv.equivalent(...)` in `ensures` names the observation, and
  `reproducible=` on a sink what a rerun must reproduce.
* `sverify.engines` has the engines, SQL dialects and plans
  (`run_sharded` runs a plan per shard and combines the results, with a
  proof that the result is the same); `sverify.errors` the exceptions.

Refused for now: correlated scalar subqueries, unbound parameters
(`sv.verify(expr, params={p: 10})` checks an `ibis.param` with its value),
`sample`, `random()` and `now()`, among the operations
[the Ibis coverage table](https://github.com/AlexanderNenninger/substrait-lean#ibis-coverage)
marks ✗. The repository has
[a how-to page](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/tasks.md), [getting started](https://alexandernenninger.github.io/substrait-lean/examples/examples.html),
the Ibis coverage table in its README, and
[what is proved and what is trusted](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/how-it-works.md).

## Configuration

* `SVERIFY_CHECKER`: path to a `substrait-check` binary that replaces the
  bundled one, for example your own `lake build`. The guide lists every
  variable ([environment variables](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/tasks.md#environment-variables)).

## Development

```bash
git clone https://github.com/AlexanderNenninger/substrait-lean
cd substrait-lean/python
uv sync                          # builds substrait-check with lake (needs elan) and links it in
uv run poe qa                    # proofs, lint, typecheck, golden, Python tests, notebooks
```

The [repository](https://github.com/AlexanderNenninger/substrait-lean) has setup details.

## License

Sverify is licensed under the [Mozilla Public License 2.0](https://github.com/AlexanderNenninger/substrait-lean/blob/main/LICENSE) (MPL-2.0).
You can use it in any product, open or proprietary, and your own code stays
yours. If you distribute a modified version of sverify's own files, those
files stay under the MPL and you share their source. The license applies file
by file, so it never reaches the code around them.

`python/src/sverify/ibis_substrait/` is derived from
[ibis-substrait](https://github.com/ibis-project/ibis-substrait) and stays
under the [Apache License 2.0](https://github.com/AlexanderNenninger/substrait-lean/blob/main/python/src/sverify/ibis_substrait/LICENSE).
