"""Incrementally maintained views on DuckDB, with delta plans from Lean.

The verified part is the delta plan: `substrait-check --delta` compiles the
view's Substrait plan with `Rel.delta`, splits it into union-free terms
(`Rel.terms`) and applies the weight-column encoding (`Rel.weighted`). Lean
proves the concatenated results equal the change to the view
(`Rel.incremental_sound`, `Rel.zeval_terms`, `Rel.weighted_eval`). This module is the trusted
glue around it: it stores the view as rows with a multiplicity column, builds
the change tables, runs the delta plan on DuckDB and merges the result.
"""

from __future__ import annotations

import contextlib
import json
import os
import subprocess
from collections.abc import Mapping, Sequence
from dataclasses import dataclass, field
from pathlib import Path

import duckdb
import pyarrow as pa

from sverify.duck import run_substrait_json, scalar, substrait_json

Row = tuple
WEIGHT = "__weight"
COUNT = "__count"


def q(name: str) -> str:
    """Quote a SQL identifier."""
    return '"' + name.replace('"', '""') + '"'


def checker_path() -> Path:
    if env := os.environ.get("SVERIFY_CHECK"):
        return Path(env)
    return Path(__file__).resolve().parents[3] / ".lake" / "build" / "bin" / "substrait-check"


class NotIncremental(Exception):
    """The plan is outside the fragment with verified delta rules."""


def delta_plans(plan_json: str) -> list[str]:
    """Ask Lean for the weighted delta plans of a Substrait JSON plan.

    The change to the view is the concatenation of their outputs. Each plan is
    union-free because DuckDB 1.2's Substrait consumer runs `UNION ALL` as
    `UNION DISTINCT`; the concatenation happens in SQL instead.
    """
    proc = subprocess.run(
        [str(checker_path()), "--delta", "/dev/stdin"],
        input=plan_json,
        capture_output=True,
        text=True,
    )
    if proc.returncode == 3:
        raise NotIncremental(proc.stderr.strip())
    if proc.returncode != 0:
        raise ValueError(f"substrait-check --delta failed: {proc.stderr.strip()}")
    return proc.stdout.splitlines()


def read_tables(plan: dict) -> list[str]:
    """Named tables a Substrait plan reads."""
    found: list[str] = []

    def walk(node: object) -> None:
        if isinstance(node, dict):
            if "namedTable" in node:
                name = ".".join(node["namedTable"]["names"])
                if name not in found:
                    found.append(name)
            for v in node.values():
                walk(v)
        elif isinstance(node, list):
            for v in node:
                walk(v)

    walk(plan)
    return found


@dataclass
class Changes:
    """Rows to insert into and delete from one table (bag semantics: each
    deleted row removes one occurrence)."""

    inserts: Sequence[Row] = field(default_factory=list)
    deletes: Sequence[Row] = field(default_factory=list)


class IncrementalView:
    """A query result kept up to date from table changes instead of recomputed.

    The view is stored in table `name` with the query's columns plus `__count`,
    the multiplicity of each distinct row.
    """

    def __init__(self, con: duckdb.DuckDBPyConnection, sql: str, name: str):
        self.con, self.sql, self.name = con, sql, name
        plan = json.loads(substrait_json(con, sql))
        self.columns: list[str] = plan["relations"][0]["root"]["names"]
        self.tables = read_tables(plan)
        self.deltas = delta_plans(json.dumps(plan))
        cols = ", ".join(q(c) for c in self.columns)
        con.sql(
            f"CREATE OR REPLACE TABLE {q(name)} AS "
            f"SELECT {cols}, count(*)::BIGINT AS {COUNT} FROM ({sql}) GROUP BY ALL"
        )

    @classmethod
    def from_ibis(cls, con: duckdb.DuckDBPyConnection, expr, name: str) -> IncrementalView:
        import ibis

        return cls(con, ibis.to_sql(expr, dialect="duckdb"), name)

    def rows(self) -> list[Row]:
        """The view's contents as a sorted bag of rows."""
        cols = ", ".join(q(c) for c in self.columns)
        expanded = self.con.sql(f"SELECT {cols} FROM {q(self.name)}, range({COUNT})").fetchall()
        return sorted(expanded, key=repr)

    def apply(self, changes: Mapping[str, Changes]) -> None:
        unknown = set(changes) - set(self.tables)
        if unknown:
            raise ValueError(f"view does not read {sorted(unknown)}")
        con = self.con
        con.begin()
        try:
            for t in self.tables:
                self._load_delta_table(t, changes.get(t, Changes()))
            # The delta plan reads the *old* tables, so it runs before they change.
            parts = [run_substrait_json(con, d).arrow() for d in self.deltas]
            cols = ", ".join(q(c) for c in self.columns)
            con.register("__delta", pa.concat_tables(parts))
            con.sql(f"""
                CREATE OR REPLACE TEMP TABLE __consolidated AS
                SELECT {cols}, sum({WEIGHT})::BIGINT AS {WEIGHT}
                FROM __delta GROUP BY ALL HAVING sum({WEIGHT}) <> 0""")
            self._merge()
            for t, ch in changes.items():
                self._apply_to_table(t, ch)
            con.commit()
        except BaseException:
            con.rollback()
            raise
        finally:
            for t in self.tables:
                con.sql(f"DROP TABLE IF EXISTS {q(t + '$delta')}")
            con.sql("DROP TABLE IF EXISTS __consolidated")
            with contextlib.suppress(duckdb.Error):
                con.unregister("__delta")

    def _load_delta_table(self, t: str, ch: Changes) -> None:
        dt = q(t + "$delta")
        self.con.sql(
            f"CREATE OR REPLACE TABLE {dt} AS SELECT *, 0::BIGINT AS {WEIGHT} FROM {q(t)} LIMIT 0"
        )
        rows = [(*r, 1) for r in ch.inserts] + [(*r, -1) for r in ch.deletes]
        if rows:
            marks = ", ".join("?" * len(rows[0]))
            self.con.executemany(f"INSERT INTO {dt} VALUES ({marks})", rows)

    def _merge(self) -> None:
        con, view = self.con, q(self.name)
        cols = ", ".join(q(c) for c in self.columns)
        dcols = ", ".join(f"d.{q(c)}" for c in self.columns)
        con.sql(f"""
            CREATE OR REPLACE TEMP TABLE __merged AS
            SELECT {cols}, sum({COUNT})::BIGINT AS {COUNT} FROM (
                SELECT {cols}, {COUNT} FROM {view}
                UNION ALL
                SELECT {dcols}, d.{WEIGHT} FROM __consolidated d)
            GROUP BY ALL""")
        bad = scalar(con.sql(f"SELECT count(*) FROM __merged WHERE {COUNT} < 0"))
        if bad:
            raise ValueError("changes delete rows that are not in the tables")
        con.sql(f"DELETE FROM {view}")
        con.sql(f"INSERT INTO {view} SELECT * FROM __merged WHERE {COUNT} > 0")
        con.sql("DROP TABLE __merged")

    def _apply_to_table(self, t: str, ch: Changes) -> None:
        con, tq = self.con, q(t)
        names = [r[0] for r in con.sql(f"DESCRIBE {tq}").fetchall()]
        for r in ch.deletes:
            cond = " AND ".join(f"{q(c)} IS NOT DISTINCT FROM ?" for c in names)
            hit = con.execute(f"SELECT rowid FROM {tq} WHERE {cond} LIMIT 1", list(r)).fetchone()
            if hit is None:
                raise ValueError(f"cannot delete {r!r} from {t}: no such row")
            con.execute(f"DELETE FROM {tq} WHERE rowid = ?", [hit[0]])
        if ch.inserts:
            marks = ", ".join("?" * len(names))
            con.executemany(f"INSERT INTO {tq} VALUES ({marks})", [tuple(r) for r in ch.inserts])

    def recompute(self) -> list[Row]:
        """The view computed from scratch, for checking."""
        return sorted(self.con.sql(self.sql).fetchall(), key=repr)
