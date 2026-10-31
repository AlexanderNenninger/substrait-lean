---
name: sverify
description: >
  Write data transformations with proved contracts using the sverify Python
  package. Use when a user wants to state what an Ibis or SQL transformation
  assumes about its inputs and guarantees about its output (not NULL, unique
  keys, value ranges, no division by zero), check those guarantees before the
  pipeline runs, read a sverify Report, or fix a postcondition sverify could
  not prove.
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
pip install 'sverify[datafusion]'         # also SQL strings, and DataFusion as an engine
pip install 'sverify[all]'                # every engine and table format
```

Wheels bundle the checker, so no Lean toolchain is needed.

## Write a contracted transformation

The function body is ordinary Ibis. Called on a source, it proves the
contract and returns a `Node`; `refresh()` computes it, on DuckDB unless you
pass `engine=`. `last_report` says what was proved.

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
    requires={"orders": [_.amount >= 0, sv.unique("id")]},
    ensures=[_.doubled >= 22, _.doubled.notnull(), sv.unique("id")],
)
def big_orders(orders):
    return orders.filter(orders.amount > 10).select(orders.id, doubled=orders.amount * 2)


big = big_orders(orders)  # proved here, before any data runs
big.refresh()
assert big.to_arrow().to_pylist() == [{"id": 1, "doubled": 60}]
report = big_orders.last_report
assert report.proved
print(report.facts["doubled"])  # what Lean established about the column
```

* Conditions are Ibis expressions over the output (`_.doubled >= 22`) or SQL
  snippets (`"doubled >= 22"`). `sv.unique(...)` states a key;
  `sv.references(col, table, key_col)` a foreign key (only in `requires`).
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
assert sv.verify(fixed, requires={"orders": [_.amount >= 0]}, ensures=[_.total > 5]).proved
```

`report.issues` lists runtime errors that may happen (division by zero,
overflow, bad casts): an error makes `proved` False; a warning (64-bit
wrap-around) doesn't. Guard a divisor with `NULLIF`/`ifelse`, or bound it in
`requires`.

## Choose what happens when a proof fails

`@sv.transform(..., on_unproved=...)`:

* `"error"` (default): raise `VerificationError`.
* `"runtime"`: check the unproved postconditions on the output data instead,
  at refresh (raises `PostconditionError`).
* `"warn"`: warn and continue.

## Gotchas

* **No DECIMAL columns.** Tables with DECIMAL columns are refused; keep money
  as integer cents (doubles don't compare exactly).
* **Windows need a key.** `LAG`, `LEAD` and `ROW_NUMBER` depend on how ties
  break unless `requires` has a key on the partition and order columns
  (`sv.unique("device_id", "ts")`); without it every postcondition is
  undetermined and `report.deterministic` is False.
* **SQL strings need a SQL producer:** the `datafusion` extra, or an Isthmus
  binary (`SVERIFY_ISTHMUS`). Ibis expressions need neither.
* **Counts across rows are not tracked**, so `COUNT(*) >= 1` per group and
  relations beyond "column plus constant" (`a < 2 * b`) aren't proved.
* **Incremental maintenance** covers filters, projections, inner and cross
  joins and `UNION ALL`; other nodes (left joins, aggregates, windows,
  `DISTINCT`, `LIMIT`) are recomputed and diffed on each refresh (see the
  `sverify-pipelines` skill).
* **Sharded `SUM`/`AVG` of doubles is refused** (`sverify.engines.run_sharded`), since
  the rounding would depend on the split.

## More

* [references/contracts.md](references/contracts.md): what Lean tracks,
  SQL transformations, composing contracts.
* The `sverify-pipelines` skill: Delta and Iceberg sources, sinks, refresh.
* The `sverify-engines` skill: running a plan on DuckDB, Polars, DataFusion,
  Snowflake or Spark, and ASOF joins.
