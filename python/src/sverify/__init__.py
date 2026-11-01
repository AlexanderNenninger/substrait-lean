"""Contracts and incremental views, proved in Lean, on DuckDB, Polars,
DataFusion and Spark.

    import sverify as sv
    from sverify.io import DeltaSink, DeltaSource

    @sv.transform(requires={"orders": [...]}, ensures=[...])
    def paid(orders): ...

    orders = DeltaSource("s3://lake/orders")
    p = orders.pipe(paid).write(DeltaSink("s3://lake/paid"))
    r = p.pipe(revenue).write(DeltaSink("s3://lake/revenue"))
    r.refresh(engine="polars")
    r.to_pandas()

* `transform` gives a function from Ibis tables to an Ibis table a contract:
  what it assumes of its inputs (`requires`) and what it promises of its
  output (`ensures`), which Lean proves. Conditions are Ibis expressions, SQL
  snippets, `unique` keys and `references` (foreign keys).
* A source (`sverify.io`) or a node piped into a transform,
  `orders.pipe(paid)`, builds a `Node` (as does the call form `paid(orders)`).
  Transforms compose left to right, fused into one plan until `.write`
  stores a result; `refresh` keeps the nodes up to date from the changes to
  their sources, and `group` refreshes several together. A batch of
  `Changes` feeds an in-memory source (`sverify.io.StaticSource`).
* `sql(query)` is SQL as a step of `.pipe`, reading the chained node and
  the keyword inputs by their table names; `sql(query, orders=orders)`
  writes a transform's body in SQL over its input tables.
* `verify` proves a contract of an Ibis expression without a transform, and
  returns a `Report`.
* `connect` gives a connection of named in-memory tables, for Ibis
  expressions bound to data; `asof_join` matches each row with the latest
  earlier row of another table, with operators Lean verifies.

Engines, SQL dialects and plans are in `sverify.engines`, the exceptions in
`sverify.errors`.
"""

import sverify.sql  # noqa: F401 - before `sql` below, which a first import of it would replace
from sverify.asof import asof_join
from sverify.contracts import Report, references, transform, unique, verify
from sverify.engine import connect
from sverify.incremental import Changes
from sverify.nodes import Node, group
from sverify.sql_model import sql

__all__ = [
    "Changes",
    "Node",
    "Report",
    "asof_join",
    "connect",
    "group",
    "references",
    "sql",
    "transform",
    "unique",
    "verify",
]
