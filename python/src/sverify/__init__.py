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
  snippets, `unique` keys, `references` (foreign keys), `max_rows` caps and `rows_per` bounds;
  `approx` relaxes a condition by a tolerance for rounding; `equivalent`
  names what the result's consumer observes (rows as a multiset, doubles
  `within` a tolerance, …).
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
  returns a `Report`; `paid.check(orders=schema)` returns the report of a
  transform's contract for input schemas, without raising or reading data.
* `connect` gives a connection of named in-memory tables, for Ibis
  expressions bound to data; `asof_join` matches each row with the latest
  earlier row of another table, with operators Lean verifies.

Engines, SQL dialects and plans are in `sverify.engines`, the exceptions in
`sverify.errors`. `__version__` is the installed version.
"""

from importlib.metadata import PackageNotFoundError as _PackageNotFoundError
from importlib.metadata import version as _version

import sverify.sql  # noqa: F401 - before `sql` below, which a first import of it would replace
from sverify.asof import asof_join
from sverify.contracts import (
    ContractedTransform,
    Report,
    approx,
    arrives_within,
    key,
    max_rows,
    references,
    rows_per,
    transform,
    unique,
    verify,
)
from sverify.engine import connect
from sverify.incremental import Changes
from sverify.nodes import Node, group
from sverify.observation import equivalent, within
from sverify.sql_model import sql
from sverify.substrait_export import from_substrait

__all__ = [
    "Changes",
    "ContractedTransform",
    "Node",
    "Report",
    "approx",
    "arrives_within",
    "asof_join",
    "connect",
    "equivalent",
    "from_substrait",
    "group",
    "key",
    "max_rows",
    "references",
    "rows_per",
    "sql",
    "transform",
    "unique",
    "verify",
    "within",
]

try:
    __version__: str = _version("sverify")
except _PackageNotFoundError:  # a source tree without an install
    __version__ = "0+unknown"


def __dir__() -> list[str]:
    """The public names, `__all__` and `__version__`: the submodules
    (`sverify.io`, `sverify.errors`, ...) stay importable but out of tab
    completion."""
    return sorted([*__all__, "__version__"])
