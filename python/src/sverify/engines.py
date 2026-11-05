"""Engines, SQL and plans: the lower-level tools under `sverify`'s transforms.

    import json

    import sverify as sv
    from sverify.engines import SNOWFLAKE, create_table, run, to_sql

    plan = node.internal_plan         # the plan Lean checked
    con = sv.connect()
    create_table(con, "orders", schema, rows)
    run(con, plan, "polars")          # or "duckdb", "spark"
    to_sql(plan, SNOWFLAKE)

Running plans:

* `run` runs a plan in Lean's written form on DuckDB or Polars
  (`ENGINES`), or on Spark, over a `Connection`'s tables (`sv.connect()`
  makes one); `run_substrait_json` runs any Substrait plan on DataFusion (experimental);
  `run_sharded` runs a plan shard by shard and combines the results;
  `run_spark` runs a plan on a Spark session configured with `SPARK_CONF`
  (`pip install 'sverify[spark]'`).
* `sv.Report.run` runs the plan a `sv.verify` report checked.
* `create_table` and `table_rows` put rows into a connection and read them back.

Plans:

* A node's `internal_plan` is the plan Lean checked, in Lean's written form.
* `substrait_json` compiles DuckDB's SQL with sverify's lift; `written_plan`
  is a plan as Lean parsed and wrote it back, the form `run` and `to_sql` take; `delta_plans` are
  the weighted delta plans Lean derives for incremental maintenance.

SQL:

* `to_sql` writes a plan as SQL whose meaning is Lean's, in a `Dialect`:
  `DUCKDB`, `SNOWFLAKE` or `SPARK`. What it cannot write it refuses
  (`UnsupportedError`, the same class as `sverify.errors.UnsupportedError`,
  which every refusal of sverify raises).
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
    from sverify.spark_engine import run as run_spark


def __getattr__(name: str) -> Any:
    # Spark is an extra: its engine is imported when first used.
    if name == "run_spark":
        from sverify.spark_engine import run

        return run
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
