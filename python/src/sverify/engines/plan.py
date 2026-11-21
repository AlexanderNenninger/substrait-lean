"""Plans, the low-level layer under `sverify.engines`. Outside the 1.x
promise: these take and give sverify's internal plan, whose form may change
in a minor release (`docs/stability.md`).

    from sverify.engines.plan import substrait_json, to_sql, written_plan

    plan = written_plan(substrait_json(con, "SELECT id FROM orders"))
    print(to_sql(plan, "duckdb"))

* `to_sql` writes any plan in sverify's internal form as SQL.
* `substrait_json` compiles DuckDB's SQL with sverify's lift.
* `written_plan` is a plan as the checker parsed and wrote it back, the
  form `sverify.engines.run` and `to_sql` take.
* `delta_plans` are the weighted delta plans the checker derives for
  incremental maintenance.
"""

from __future__ import annotations

from sverify.engine import substrait_json, written_plan
from sverify.incremental import delta_plans
from sverify.sql import to_sql

__all__ = ["delta_plans", "substrait_json", "to_sql", "written_plan"]
