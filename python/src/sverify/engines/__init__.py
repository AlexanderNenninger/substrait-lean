"""Engines and SQL: the lower-level tools under `sverify`'s transforms.

    import sverify as sv
    from sverify.engines import run

    node.refresh(engine="polars")     # or "duckdb", "spark"
    node.to_sql("snowflake")          # or "duckdb", "spark"; report.to_sql too
    con = sv.connect()
    con.create("orders", schema, rows)
    run(con, node.internal_plan, "polars")

Running plans:

* `run` runs a plan in sverify's internal form on DuckDB or Polars
  (`ENGINES`), or on Spark (`"spark"`, or a Spark session configured with
  `sverify_spark.dialect.SPARK_CONF`; `pip install 'sverify[spark]'`), over a
  `Connection`'s tables (`sv.connect()` makes one; `con.create`, `con.put`
  and `con.rows` put rows in and read them back). `run_sharded` runs a plan
  shard by shard and combines the results (with `tolerance=True`, a
  `Sharded`: the result and its doubles' distance from Lean's values).
  `run` and `run_sharded` take the plan as a value a node or report holds
  (`node.internal_plan`); its content is outside the 1.x promise.
  `con.get` gives a table as it is held: an Arrow table, or a `Native`
  table an engine reads where it is, whose members are outside the 1.x
  promise while the native scans move into the engine packages.
* `sv.Report.run` runs the plan a `sv.verify` report checked.

SQL:

* `Node.to_sql` and `Report.to_sql` write the plan a proof checked as SQL
  whose meaning is the proof's, in a dialect named as its engine:
  `"duckdb"`, `"snowflake"` or `"spark"`, or a `Dialect` (an engine
  package's, `sverify_spark.dialect.SPARK`). What a dialect cannot write is
  refused (`UnsupportedError`, the same class as
  `sverify.errors.UnsupportedError`). `Dialect`'s SQL-writing methods
  and subclassing it are outside the 1.x promise.

The plan layer (`to_sql` of any plan, `substrait_json`, `written_plan`,
`delta_plans`) is `sverify.engines.plan`, outside the 1.x promise.
"""

from __future__ import annotations

from sverify._scan import Native
from sverify._unsupported import UnsupportedError
from sverify.engine import ENGINES, Connection
from sverify.engine import run_plan as run
from sverify.partition import Sharded, run_sharded
from sverify.sql import Dialect

__all__ = [
    "ENGINES",
    "Connection",
    "Dialect",
    "Native",
    "Sharded",
    "UnsupportedError",
    "run",
    "run_sharded",
]
