---
name: sverify
description: >
  Write data transformations with proved contracts using the sverify Python
  package. Use when a user wants to state what an Ibis or SQL transformation
  assumes about its inputs and guarantees about its output (not NULL, unique
  keys, value ranges, no division by zero), check those guarantees before the
  pipeline runs, read a sverify Report, fix a postcondition sverify could
  not prove, or test transforms and their contracts with pytest.
---

# sverify: contracts proved before a pipeline runs

`sverify` hands a transformation's query plan to a checker written in Lean,
which proves the postconditions (`ensures`) for every input that meets the
preconditions (`requires`), or says why it can't. Use it in place of data
tests on derived data: the checks hold on all inputs, not only on the data
that happened to be there.

## Install

```bash
pip install sverify                       # core: DuckDB, contracts, views
pip install 'sverify[all]'                # Polars, Spark, Delta, Iceberg, Flight and the rest
pip install 'sverify[datafusion]'         # DataFusion, an optional engine outside `all`
```

DuckDB (the default), Polars (streaming) and Spark 4.x run plans, each with a
proved profile (`semantics="duckdb"`, `"polars"`, `"spark"`). The SQL
dialects (DuckDB, Spark, Snowflake) need no extra. DataFusion is outside the
1.x promise
([docs/stability.md](https://github.com/AlexanderNenninger/substrait-lean/blob/main/docs/stability.md#engines)).

Wheels bundle the checker, so no Lean toolchain is needed.

## Write a contracted transformation

The function body is ordinary Ibis. Called on a source, it proves the
contract and returns a `Node`; `refresh()` computes it, on DuckDB unless you
pass `refresh(engine=...)`. `report` says what was proved.
`@sv.transform(check_engine=...)` says where checks on data run.

```python
import ibis
import pyarrow as pa
from ibis import _

import sverify as sv
from sverify.io import StaticSource

orders = StaticSource(  # in memory; DeltaSource and IcebergSource work the same way
    pa.table({"id": [1, 2], "customer": ["ada", "bob"], "amount": [30, 5]}), name="orders"
)


@sv.transform(
    requires={"orders": [_.amount >= 0, _.amount < 1_000_000_000, sv.unique("id")]},
    ensures=[_.doubled >= 22, _.doubled.notnull(), sv.unique("id")],
)
def big_orders(orders):
    return orders.filter(orders.amount > 10).select(orders.id, doubled=orders.amount * 2)


big = big_orders(orders)  # proved here, before any data runs
big.refresh()
assert big.to_arrow().to_pylist() == [{"id": 1, "doubled": 60}]
report = big_orders.report
assert report.proved
print(report.facts["doubled"])  # what Lean established about the column
```

* Conditions are Ibis expressions over the output (`_.doubled >= 22`) or SQL
  snippets (`"doubled >= 22"`). `sv.unique(...)` states a key;
  `sv.references("cust", to=customers.id)` a foreign key (only in
  `requires`); `sv.max_rows(n)` caps an input's rows. A transformation with
  one input also takes a plain list, `requires=[_.amount >= 0]`.
* `requires` is checked on the source's data when the node is refreshed
  (`sverify.errors.PreconditionError`), or proved from table metadata.
* Transforms compose: `revenue(paid(orders))` proves each link from the
  upstream contract (`sverify.errors.CompositionError` names a broken one).
* Called on Ibis tables instead of a source, a transform returns an Ibis
  expression: handy for checking a contract without data.

## Read the report, and fix what isn't proved

An unproved postcondition raises `sverify.errors.VerificationError`.
`sv.verify` returns the report without raising, with a counterexample when
the search finds one:

```python
orders_t = ibis.table({"id": "int64", "customer": "string", "amount": "int64"}, name="orders")
report = sv.verify(
    orders_t.select(orders_t.id, total=orders_t.amount + 1),
    requires={"orders": [_.amount >= 0]},
    ensures=[_.total > 5],
)
failed = report.unproved[0]
print(failed.label, failed.value)  # (_.total > 5) TRUE or FALSE
print(failed.counterexample)  # an input row with amount = 0 gives total = 1
```

Read the counterexample, then either strengthen `requires` (if the input
really can't look like that), change the transformation, or weaken the
postcondition. Here a filter makes it hold:

```python
fixed = orders_t.filter(orders_t.amount > 4).select(orders_t.id, total=orders_t.amount + 1)
bounded = {"orders": [_.amount >= 0, _.amount < 1_000_000_000]}
assert sv.verify(fixed, requires=bounded, ensures=[_.total > 5]).proved
```

`report.issues` lists runtime errors that may happen (division by zero,
overflow at the declared width, bad casts); an error makes `proved` False.
Sverify infers the bounds that rule most of them out (`amount * 2` needs
`_.amount < 2**62`) and, by default (`on_inferred="error"`), reports each
under `needs:` (`report.needs`, ready for `requires=` as
`report.suggested_requires`) until `requires` states it or the
transformation no longer needs it (filter those rows first, or a CASE);
`on_inferred="warn"` or `"ignore"` assumes it and checks it on the data, and
`on_inferred="off"` infers and assumes nothing. For the rest, the `hint:` lines of
`str(report)` name the bound to add, and an unproved comparison with a constant comes with
the precondition that proves it (`report.suggestions`). An integer `SUM` that
may overflow is listed in `report.assumed` and checked at run time (an error
with `on_inferred="off"`); a row cap (`sv.max_rows(n)`) proves it fits. Guard a divisor with
`NULLIF`/`ifelse`, or bound it in `requires`.

Sums and means of doubles round: with a row cap, `sv.approx(_.cpu_avg <= 100)`
states a postcondition up to the proved rounding error.

## Choose what happens when a proof fails

`@sv.transform(..., on_unproved=...)`:

* `"error"` (default): raise `VerificationError`.
* `"check"`: check the unproved postconditions on the output data instead,
  at refresh (raises `PostconditionError`).
* `"warn"`: warn and continue; a node's refreshes run it unverified, each
  with an `UnverifiedRunWarning`.

A run or refresh of a plan that is not proved raises `UnverifiedRunError`, a
`VerificationError` (and a `RouteError`), unless you pass `unverified=True`.

## Test transforms with pytest

Installing sverify registers a pytest plugin. In a test suite, assert the
contract, run the node on a few rows, and compare the engines; with
`expected=`, a failure lists the missing and unexpected rows, and test data
that breaks a precondition is reported with its rows.

```python
from sverify.testing import assert_contract, assert_engines_agree, cases, source


def test_big_orders():  # with the plugin: def test_big_orders(sv_source, sv_engine)
    orders = source([], {"id": "int64", "customer": "string", "amount": "int64"}, name="orders")
    node = orders.pipe(big_orders)
    assert_contract(node)  # every contract in the node's lineage is proved
    data = {"orders": [(1, "ada", 30), (2, "bob", 5)]}
    out = assert_contract(node, data=data, expected=[{"id": 1, "doubled": 60}])
    assert out.num_rows == 1
    assert_engines_agree(node, data)  # every installed engine gives the same rows


test_big_orders()
```

* `data` names every table the node reads: its sources, and the stored nodes
  (`.write`) it reads. Rows are tuples in column order, dicts, or Arrow
  tables; `expected` is compared as a bag.
* Fixtures: `sv_source(rows, schema, name=...)` is `source`; a test taking
  `sv_engine` runs once per installed engine (pass it as `engine=`);
  `pytest --sv-engines=duckdb,polars` picks them, `-p no:sverify` turns the
  plugin off.
* `cases(node, max_rows=5)` is a Hypothesis strategy of input tables that
  meet the preconditions (`pip install 'sverify[testing]'`), for property
  tests of the code around a node:

```python
from hypothesis import given, settings

ORDERS = {"id": "int64", "customer": "string", "amount": "int64"}
node = source([], ORDERS, name="orders").pipe(big_orders)


@settings(max_examples=10, deadline=None)
@given(cases(node))
def test_doubles_are_big(data):
    out = assert_contract(node, data=data)
    assert all(d > 20 for d in out["doubled"].to_pylist())


test_doubles_are_big()
```

## Gotchas

* **Windows need a key for facts about order.** `LAG`, `LEAD` and
  `ROW_NUMBER` depend on how ties break unless `requires` has a key on the
  partition and order columns (`sv.unique("device_id", "ts")`). Without it
  `verify` proves only what holds for every order of the ties (D24),
  `report.deterministic` is False and `str(report)` names the window;
  a rerun that must give the same rows refuses the plan.
* **SQL strings are DuckDB's SQL**, read by sverify's lift, which covers a
  subset so far (SELECT, WHERE, joins, subqueries and CTEs, GROUP BY with
  grouping sets, windows, set operations, ORDER BY, LIMIT, CASE, CAST and
  common functions): write the rest in Ibis. In DuckDB's SQL, `/` divides as
  doubles; integer division is `//`. Checks use sverify's reference semantics
  unless you pass `semantics="duckdb"` (to `sv.sql`, `sv.verify` or
  `@sv.transform`), which models DuckDB's NaN and `±inf`.
* **Counts across rows are not tracked**, so `COUNT(*) >= 1` per group and
  relations beyond "column plus constant" (`a < 2 * b`) aren't proved.
* **Incremental maintenance** covers filters, projections, inner, cross,
  semi and anti joins, `UNION ALL`, `DISTINCT`, `COUNT`, exact `SUM`/`AVG`
  and `MIN`/`MAX` per group; other aggregates recompute the groups a batch
  touches, windows on one `PARTITION BY` the touched partitions, and bounded
  `RANGE` frames the touched frames; other nodes (left joins, `LIMIT`) are
  recomputed and diffed on each refresh, and `node.status()` says which (see
  the `sverify-pipelines` skill).
* **Sharded `SUM`/`AVG` of doubles is refused** (`sverify.engines.run_sharded`), since
  the rounding would depend on the split; `reproducible=sv.equivalent(floats="plan")`
  splits them anyway, within a proved tolerance that `tolerance=True` reports per row.

## More

* [references/contracts.md](references/contracts.md): what Lean tracks,
  SQL transformations, composing contracts.
* The `sverify-pipelines` skill: Delta and Iceberg sources, sinks, refresh.
* The `sverify-engines` skill: running a plan on DuckDB, Polars or Spark,
  writing it as DuckDB, Spark or Snowflake SQL, and ASOF joins.
