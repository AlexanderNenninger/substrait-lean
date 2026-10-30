"""DuckDB as an engine, through SQL generated from the plan.

`run` writes the plan as SQL with `sverify.sql.to_sql` (whose semantics are
Lean's `Rel.eval`, see `sverify.sql.core`) and runs it on a fresh in-process
DuckDB database holding the given tables. DuckDB's Substrait extension is not
used.
"""

from __future__ import annotations

import json
from collections.abc import Mapping

import duckdb
import pyarrow as pa

from sverify.sql import to_sql
from sverify.sql.duckdb import DUCKDB


def run(plan: str | dict, tables: Mapping[str, pa.Table]) -> pa.Table:
    """Run a Substrait JSON plan on DuckDB over `tables`."""
    db = duckdb.connect()
    for name, table in tables.items():
        # A real table (not a view on the Arrow data): `rowid` numbers its rows
        # in insertion order, which `to_sql` uses as the scan order.
        db.register("__sverify_input", table)
        db.execute(f"CREATE TABLE {DUCKDB.quote(name)} AS SELECT * FROM __sverify_input")
        db.unregister("__sverify_input")
    sql = to_sql(json.loads(plan) if isinstance(plan, str) else plan, DUCKDB)
    return db.sql(sql).to_arrow_table()
