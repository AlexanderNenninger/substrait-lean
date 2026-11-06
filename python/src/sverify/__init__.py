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
  `sverify.io.Changes` feeds an in-memory source (`sverify.io.StaticSource`).
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

import importlib as _importlib
import sys as _sys
import types as _types
from typing import TYPE_CHECKING as _TYPE_CHECKING
from typing import Any as _Any

from sverify import _meta

if _TYPE_CHECKING:
    from sverify.asof import asof_join
    from sverify.conditions import key
    from sverify.contracts import (
        ContractedTransform,
        Report,
        approx,
        arrives_within,
        max_rows,
        references,
        rows_per,
        transform,
        unique,
        verify,
    )
    from sverify.engine import connect
    from sverify.nodes import Node, group
    from sverify.observation import equivalent, within
    from sverify.sql_model import sql

# The public names, imported on first use (PEP 562): `import sverify` stays
# cheap, and so do the command's `--help`, `--version` and `explain`, until
# a name that needs Ibis is read.
_LAZY = {
    "asof_join": "sverify.asof",
    "ContractedTransform": "sverify.contracts",
    "Report": "sverify.contracts",
    "approx": "sverify.contracts",
    "arrives_within": "sverify.contracts",
    "key": "sverify.conditions",
    "max_rows": "sverify.contracts",
    "references": "sverify.contracts",
    "rows_per": "sverify.contracts",
    "transform": "sverify.contracts",
    "unique": "sverify.contracts",
    "verify": "sverify.contracts",
    "connect": "sverify.engine",
    "Node": "sverify.nodes",
    "group": "sverify.nodes",
    "equivalent": "sverify.observation",
    "within": "sverify.observation",
    "sql": "sverify.sql_model",
}


#: Moved before 1.0 (the API review's A1); the old names warn for a release.
_DEPRECATED = {
    "Changes": ("sverify.incremental", "sverify.Changes is deprecated; import it from sverify.io"),
    "from_substrait": (
        "sverify.substrait_export",
        "sverify.from_substrait is deprecated; call sverify.Report.from_substrait",
    ),
}


def __getattr__(name: str) -> _Any:
    """A public name, imported on first use; a deprecated one, with a
    warning; else a submodule (`sverify.contracts`), as an eager import
    used to load them."""
    if name in _DEPRECATED:
        import warnings

        module, message = _DEPRECATED[name]
        warnings.warn(message, DeprecationWarning, stacklevel=2)
        return getattr(_importlib.import_module(module), name)
    if name in _LAZY:
        value = getattr(_importlib.import_module(_LAZY[name]), name)
        globals()[name] = value
        return value
    if name.startswith("__"):
        raise AttributeError(f"module {__name__!r} has no attribute {name!r}")
    try:
        return _importlib.import_module(f"{__name__}.{name}")
    except ModuleNotFoundError as e:
        if e.name != f"{__name__}.{name}":
            raise
        raise AttributeError(f"module {__name__!r} has no attribute {name!r}") from None


class _Module(_types.ModuleType):
    """`sverify` itself: `sverify.sql` stays the function `sql`, though the
    package `sverify.sql` (the SQL writers) shares its name and its import
    would set the attribute to the package."""

    def __setattr__(self, name: str, value: _Any) -> None:
        if name == "sql" and isinstance(value, _types.ModuleType):
            return
        super().__setattr__(name, value)


_sys.modules[__name__].__class__ = _Module

__all__ = [
    "ContractedTransform",
    "Node",
    "Report",
    "approx",
    "arrives_within",
    "asof_join",
    "connect",
    "equivalent",
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

__version__: str = _meta.VERSION


def __dir__() -> list[str]:
    """The public names, `__all__` and `__version__`: the submodules
    (`sverify.io`, `sverify.errors`, ...) stay importable but out of tab
    completion."""
    return sorted([*__all__, "__version__"])
