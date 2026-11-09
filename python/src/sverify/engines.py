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
  whose meaning is the proof's, in a dialect named as its engine:
  `"duckdb"`, `"snowflake"` or `"spark"`. What a dialect cannot write is
  refused (`UnsupportedError`, the same class as
  `sverify.errors.UnsupportedError`). `Dialect`'s SQL-writing methods
  and subclassing it are outside the 1.x promise.

Plans, the low-level layer, outside the 1.x promise (they take sverify's
internal plan, and may change in a minor release):

* `to_sql` writes any plan in sverify's internal form as SQL.
* `substrait_json` compiles DuckDB's SQL with sverify's lift; `written_plan`
  is a plan as the checker parsed and wrote it back, the form `run` and
  `to_sql` take; `run_substrait_json` runs a Substrait plan on DataFusion (an optional engine);
  `delta_plans` are the weighted delta plans the checker derives for
  incremental maintenance.

Deprecated: `create_table` (`con.create`), `table_rows` (`con.rows`).
"""

from __future__ import annotations

from typing import Any

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
from sverify.sql.spark import SPARK_CONF


def __getattr__(name: str) -> Any:
    if name == "Unsupported":
        from sverify.errors import deprecated_name

        return deprecated_name(__name__, name)
    raise AttributeError(f"module {__name__!r} has no attribute {name!r}")


__all__ = [
    "ENGINES",
    "SPARK_CONF",
    "Connection",
    "Dialect",
    "UnsupportedError",
    "create_table",
    "delta_plans",
    "run",
    "run_sharded",
    "run_substrait_json",
    "substrait_json",
    "table_rows",
    "to_sql",
    "written_plan",
]
