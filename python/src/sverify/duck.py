"""DuckDB as Substrait producer and consumer.

Needs the `substrait` community extension, which is published for DuckDB
1.2.x but not for 1.3 and later, hence the `duckdb==1.2.2` pin.
"""

import duckdb


def connect(database: str = ":memory:") -> duckdb.DuckDBPyConnection:
    con = duckdb.connect(database)
    con.sql("INSTALL substrait FROM community")
    con.sql("LOAD substrait")
    return con


def scalar(result: duckdb.DuckDBPyConnection | duckdb.DuckDBPyRelation):
    """The single value of a one-row, one-column result."""
    row = result.fetchone()
    if row is None:
        raise ValueError("query returned no rows")
    return row[0]


def substrait_json(con: duckdb.DuckDBPyConnection, sql: str) -> str:
    """Compile SQL to a Substrait JSON plan.

    The optimizer is disabled while producing the plan: it uses table
    statistics, so with it on DuckDB drops a `WHERE` clause on an empty table.
    Incremental maintenance needs plans that are valid for any data.
    """
    con.sql("PRAGMA disable_optimizer")
    try:
        return scalar(con.execute("CALL get_substrait_json(?)", [sql]))
    finally:
        con.sql("PRAGMA enable_optimizer")


def run_substrait_json(con: duckdb.DuckDBPyConnection, plan: str) -> duckdb.DuckDBPyRelation:
    return con.sql("SELECT * FROM from_substrait_json($plan)", params={"plan": plan})
