"""Engines, SQL and plans: the lower-level tools under `sverify`'s transforms.

    import json

    import sverify as sv
    from sverify.engines import SNOWFLAKE, create_table, run, to_sql

    plan = node.plan                  # the plan Lean checked
    con = sv.connect()
    create_table(con, "orders", schema, rows)
    run(con, plan, "polars")          # or "duckdb", "datafusion", "spark"
    to_sql(json.loads(plan), SNOWFLAKE)

Running plans:

* `run` runs a plan in Lean's written form on DuckDB, Polars or DataFusion
  (`ENGINES`), or on Spark, over a `Connection`'s tables (`sv.connect()`
  makes one); `run_substrait_json` runs any Substrait plan on DataFusion;
  `run_sharded` runs a plan shard by shard and combines the results;
  `run_spark` runs a plan on a Spark session configured with `SPARK_CONF`
  (`pip install 'sverify[spark]'`).
* `create_table` and `table_rows` put rows into a connection and read them back.

Plans:

* A node's `plan` is the plan Lean checked, in Lean's written form.
* `substrait_json` compiles SQL with DataFusion's producer, `isthmus_json`
  with Isthmus (`SQL_PRODUCERS`); `written_plan` is a plan as Lean parsed
  and wrote it back, the form `run` and `to_sql` take; `delta_plans` are
  the weighted delta plans Lean derives for incremental maintenance.

SQL:

* `to_sql` writes a plan as SQL whose meaning is Lean's, in a `Dialect`:
  `DUCKDB`, `SNOWFLAKE` or `SPARK`. What it cannot write it refuses
  (`Unsupported`).
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Any

from sverify.engine import (
    ENGINES,
    SQL_PRODUCERS,
    Connection,
    create_table,
    isthmus_json,
    run_substrait_json,
    substrait_json,
    table_rows,
    written_plan,
)
from sverify.engine import run_plan as run
from sverify.incremental import delta_plans
from sverify.partition import run_sharded
from sverify.sql import Dialect, Unsupported, to_sql
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
    raise AttributeError(f"module {__name__!r} has no attribute {name!r}")


__all__ = [
    "DUCKDB",
    "ENGINES",
    "SNOWFLAKE",
    "SPARK",
    "SPARK_CONF",
    "SQL_PRODUCERS",
    "Connection",
    "Dialect",
    "Unsupported",
    "create_table",
    "delta_plans",
    "isthmus_json",
    "run",
    "run_sharded",
    "run_spark",
    "run_substrait_json",
    "substrait_json",
    "table_rows",
    "to_sql",
    "written_plan",
]
