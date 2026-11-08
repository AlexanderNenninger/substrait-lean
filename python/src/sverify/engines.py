"""Engines, SQL and plans: the lower-level tools under `sverify`'s transforms.

    import sverify as sv
    from sverify.engines import run

    node.refresh(engine="polars")     # or "duckdb", "spark"
    node.to_sql("snowflake")          # or "duckdb", "spark"; report.to_sql too
    con = sv.connect()
    con.create("orders", schema, rows)
    run(con, node.internal_plan, "polars")

Running plans:

* `run` runs a plan in sverify's internal form on DuckDB or Polars
  (`ENGINES`), or on Spark (`"spark"`, or a Spark session
  configured with `SPARK_CONF`; `pip install 'sverify[spark]'`), over a
  `Connection`'s tables (`sv.connect()` makes one; `con.create`, `con.put`
  and `con.rows` put rows in and read them back). `run_sharded` runs a plan
  shard by shard and combines the results.
* `sv.Report.run` runs the plan a `sv.verify` report checked.

SQL:

* `Node.to_sql` and `Report.to_sql` write the plan a proof checked as SQL
  whose meaning is the proof's, in a `Dialect`: `DUCKDB`, `SNOWFLAKE` or
  `SPARK`. What a dialect cannot write is refused (`UnsupportedError`, the same
  class as `sverify.errors.UnsupportedError`). `Dialect`'s SQL-writing methods
  and subclassing it are outside the 1.x promise.

Plans, the low-level layer, outside the 1.x promise (they take sverify's
internal plan, and may change in a minor release):

* `to_sql` writes any plan in sverify's internal form as SQL.
* `substrait_json` compiles DuckDB's SQL with sverify's lift; `written_plan`
  is a plan as the checker parsed and wrote it back, the form `run` and
  `to_sql` take; `run_substrait_json` runs a Substrait plan on DataFusion (an optional engine);
  `delta_plans` are the weighted delta plans the checker derives for
  incremental maintenance.

Deprecated: `create_table` (`con.create`), `table_rows` (`con.rows`),
`run_spark` (`run(con, plan, "spark")`).
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Any

from sverify._unsupported import UnsupportedError
from sverify.engine import (
    ENGINES,
    Connection,
    create_table,
    run_substrait_json,
    substrait_json,
    table_rows,
    written_plan,
)
from sverify.engine import run_plan as run
from sverify.incremental import delta_plans
from sverify.partition import run_sharded
from sverify.sql import Dialect, to_sql
from sverify.sql.duckdb import DUCKDB
from sverify.sql.snowflake import SNOWFLAKE
from sverify.sql.spark import SPARK, SPARK_CONF

if TYPE_CHECKING:
    from collections.abc import Mapping

    import pyarrow as pa


def run_spark(
    plan: str | dict,
    tables: Mapping[str, pa.Table],
    spark: Any = None,
    *,
    deterministic: bool = False,
) -> pa.Table:
    """Deprecated: `run(con, plan, "spark")`, or `run(con, plan, spark)` for
    a session of your own, over a connection's tables.

    A window that needs a row order is written for Spark when the contract
    states the order key (`sv.unique(...)` on the order columns): the
    report is then `deterministic`, and `Node.to_sql("spark")` and
    `Report.to_sql("spark")` write the window without a tiebreak.
    """
    import warnings

    warnings.warn(
        "sverify.engines.run_spark is deprecated; write run(con, plan, 'spark') or "
        "run(con, plan, spark_session). For a window without a row order, state the "
        "order key as sv.unique(...) in the contract and use node.to_sql('spark') or "
        "report.to_sql('spark')",
        DeprecationWarning,
        stacklevel=2,
    )
    from sverify.spark_engine import run as _run

    return _run(plan, tables, spark, deterministic=deterministic)


def __getattr__(name: str) -> Any:
    if name == "Unsupported":
        from sverify.errors import deprecated_name

        return deprecated_name(__name__, name)
    raise AttributeError(f"module {__name__!r} has no attribute {name!r}")


__all__ = [
    "DUCKDB",
    "ENGINES",
    "SNOWFLAKE",
    "SPARK",
    "SPARK_CONF",
    "Connection",
    "Dialect",
    "UnsupportedError",
    "create_table",
    "delta_plans",
    "run",
    "run_sharded",
    "run_spark",
    "run_substrait_json",
    "substrait_json",
    "table_rows",
    "to_sql",
    "written_plan",
]
