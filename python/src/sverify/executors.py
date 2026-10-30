"""Engines that run verified plans: where incremental views and runtime
contract checks execute.

Plans always come from DataFusion's Substrait producer (and from Lean, for
delta plans); an `Executor` holds tables and runs those plans:

* `DataFusionExecutor` runs them with DataFusion's own Substrait consumer, on
  the tables of an Ibis DataFusion backend.
* `DuckDBExecutor` writes them as SQL with `sverify.sql.to_sql` (whose
  semantics are Lean's `Rel.eval`, see `sverify.sql.core`) and runs that on an
  in-process DuckDB database. Tables are copied in from the DataFusion backend
  the plans were compiled on.

`executor(con, "duckdb")` picks one per call; `IncrementalView` and
`transform` take the same `engine` argument.
"""

from __future__ import annotations

import json
from typing import Literal, Protocol

import duckdb
import pyarrow as pa

from sverify.engine import Backend, put_table, run_substrait_json
from sverify.sql import to_sql
from sverify.sql.duckdb import DUCKDB

EngineName = Literal["datafusion", "duckdb"]


class Executor(Protocol):
    name: str

    def put(self, name: str, table: pa.Table) -> None:
        """Create or replace a table."""
        ...

    def get(self, name: str) -> pa.Table:
        """A table's rows, in insertion order."""
        ...

    def drop(self, name: str) -> None: ...

    def run(self, plan_json: str) -> pa.Table:
        """Run a Substrait JSON plan."""
        ...


class DataFusionExecutor:
    name = "datafusion"

    def __init__(self, con: Backend):
        self.con = con

    def put(self, name: str, table: pa.Table) -> None:
        put_table(self.con, name, table)

    def get(self, name: str) -> pa.Table:
        return self.con.con.table(name).to_arrow_table()

    def drop(self, name: str) -> None:
        self.con.con.deregister_table(name)

    def run(self, plan_json: str) -> pa.Table:
        return run_substrait_json(self.con, plan_json)


class DuckDBExecutor:
    name = "duckdb"

    def __init__(self, db: duckdb.DuckDBPyConnection | None = None):
        self.db = db if db is not None else duckdb.connect()

    def put(self, name: str, table: pa.Table) -> None:
        # A real table (not a view on the Arrow data): `rowid` numbers its rows
        # in insertion order, which `to_sql` uses as the scan order.
        self.db.register("__sverify_put", table)
        try:
            self.db.execute(
                f"CREATE OR REPLACE TABLE {DUCKDB.quote(name)} AS SELECT * FROM __sverify_put"
            )
        finally:
            self.db.unregister("__sverify_put")

    def get(self, name: str) -> pa.Table:
        return self.db.sql(f"SELECT * FROM {DUCKDB.quote(name)} ORDER BY rowid").to_arrow_table()

    def drop(self, name: str) -> None:
        self.db.execute(f"DROP TABLE IF EXISTS {DUCKDB.quote(name)}")

    def sql(self, plan_json: str) -> str:
        return to_sql(json.loads(plan_json), DUCKDB)

    def run(self, plan_json: str) -> pa.Table:
        return self.db.sql(self.sql(plan_json)).to_arrow_table()


def executor(con: Backend, engine: EngineName | Executor = "datafusion") -> Executor:
    """The executor for plans compiled on `con`: `con` itself for DataFusion,
    or a fresh DuckDB database (tables are copied in by the caller)."""
    if engine == "datafusion":
        return DataFusionExecutor(con)
    if engine == "duckdb":
        return DuckDBExecutor()
    if isinstance(engine, str):
        raise ValueError(f"unknown engine {engine!r}; use 'datafusion' or 'duckdb'")
    return engine


def runs_on(ex: Executor, con: Backend) -> bool:
    """Does `ex` use the tables of `con` itself?"""
    return isinstance(ex, DataFusionExecutor) and ex.con is con


def copy_tables(con: Backend, ex: Executor, names: list[str]) -> None:
    """Copy tables of the DataFusion backend `con` into `ex`, unless it runs on `con`."""
    if runs_on(ex, con):
        return
    for t in names:
        ex.put(t, con.con.table(t).to_arrow_table())
