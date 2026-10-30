"""Incrementally maintained views on DataFusion, with delta plans from Lean.

The verified part is the delta plan: `substrait-check --delta` compiles the
view's Substrait plan with `Rel.delta`, splits it into union-free terms
(`Rel.terms`) and applies the weight-column encoding (`Rel.weighted`). Lean
proves the concatenated results are the change to the view
(`Rel.incremental_sound`, `Rel.zeval_terms`, `Rel.weighted_eval`). This module
is the trusted glue around it: it keeps the view as rows with multiplicities,
builds the change tables, runs the delta plans on an engine (DataFusion, or
DuckDB through generated SQL; see `sverify.executors`) and merges the result.
A batch is computed completely before anything is replaced, so a failing batch
changes nothing.
"""

from __future__ import annotations

import json
import math
import os
import subprocess
from collections import Counter
from collections.abc import Mapping, Sequence
from dataclasses import dataclass, field
from pathlib import Path

import ibis.expr.types as ir
import pyarrow as pa

from sverify.engine import Backend, put_table, substrait_json, to_arrow, to_sql
from sverify.executors import EngineName, Executor, copy_tables, executor, runs_on

Row = tuple
WEIGHT = "__weight"


def checker_path() -> Path:
    """`$SVERIFY_CHECK` if set, else the `substrait-check` the wheel ships with
    (a symlink to the lake build in an editable install)."""
    if env := os.environ.get("SVERIFY_CHECK"):
        return Path(env)
    bundled = Path(__file__).parent / "_bin" / "substrait-check"
    if not bundled.exists():
        raise FileNotFoundError(f"{bundled} is missing; reinstall sverify or set SVERIFY_CHECK")
    return bundled


class NotIncremental(Exception):
    """The plan is outside the fragment with verified delta rules."""


def delta_plans(plan_json: str) -> list[str]:
    """Ask Lean for the weighted delta plans of a Substrait JSON plan; the
    change to the view is the concatenation of their outputs."""
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


def _value_key(x: object) -> object:
    # Python's float equality differs from DataFusion's total order: there
    # NaN equals itself, and -0.0 and 0.0 (or -NaN and NaN) are different.
    if isinstance(x, float) and (math.isnan(x) or x == 0):
        return ("NaN" if math.isnan(x) else "zero", math.copysign(1.0, x))
    return x


def row_key(row: Row) -> tuple:
    """Rows compare as DataFusion compares them (see `_value_key`)."""
    return tuple(_value_key(x) for x in row)


def arrow_rows(table: pa.Table) -> list[Row]:
    return [tuple(r.values()) for r in table.to_pylist()]


@dataclass
class Changes:
    """Rows to insert into and delete from one table (bag semantics: each
    deleted row removes one occurrence)."""

    inserts: Sequence[Row] = field(default_factory=list)
    deletes: Sequence[Row] = field(default_factory=list)


class IncrementalView:
    """A query result kept up to date from table changes instead of recomputed.

    `query` is an Ibis expression or SQL over tables of `con`, an Ibis
    DataFusion backend. The view is also registered as table `name`.

    `engine` runs the plans: `"datafusion"` (on `con`'s tables), `"duckdb"` (a
    DuckDB database holding copies of the tables the view reads) or an
    `Executor`. Base tables change in `con` and in the engine alike.
    """

    def __init__(
        self,
        con: Backend,
        query: ir.Table | str,
        name: str,
        engine: EngineName | Executor = "datafusion",
    ):
        self.con, self.name = con, name
        self.sql = query if isinstance(query, str) else to_sql(query)
        self.plan = substrait_json(con, self.sql)
        plan = json.loads(self.plan)
        self.columns: list[str] = plan["relations"][0]["root"]["names"]
        self.tables = read_tables(plan)
        self.deltas = delta_plans(self.plan)
        self.engine = executor(con, engine)
        copy_tables(con, self.engine, self.tables)
        result = self.engine.run(self.plan)
        self.schema = result.schema
        self.counts: Counter[tuple] = Counter()
        self.examples: dict[tuple, Row] = {}
        self._add(arrow_rows(result), 1)
        self._publish()

    def _add(self, rows: Sequence[Row], weight: int) -> None:
        for r in rows:
            k = row_key(r)
            self.counts[k] += weight
            self.examples.setdefault(k, r)

    def _publish(self) -> None:
        rows = [self.examples[k] for k, n in self.counts.items() for _ in range(n)]
        self._put(self.name, to_arrow(rows, self.schema))

    def _put(self, t: str, table: pa.Table) -> None:
        """Replace a table in the engine, and in `con` if that is another one."""
        self.engine.put(t, table)
        if not runs_on(self.engine, self.con):
            put_table(self.con, t, table)

    def rows(self) -> list[Row]:
        """The view's contents as a bag of rows, in a canonical order."""
        out = [self.examples[k] for k, n in self.counts.items() for _ in range(n)]
        return sorted(out, key=lambda r: repr(row_key(r)))

    def recompute(self) -> list[Row]:
        """The view computed from scratch, for checking."""
        rows = arrow_rows(self.engine.run(self.plan))
        return sorted(rows, key=lambda r: repr(row_key(r)))

    def apply(self, changes: Mapping[str, Changes]) -> None:
        unknown = set(changes) - set(self.tables)
        if unknown:
            raise ValueError(f"view does not read {sorted(unknown)}")
        # New base tables first: this also checks that every delete exists.
        new_tables = {t: self._apply_to_table(t, ch) for t, ch in changes.items()}
        try:
            for t in self.tables:
                self._load_delta_table(t, changes.get(t, Changes()))
            # The delta plans read the *old* tables, so they run before those change.
            delta = Counter[tuple]()
            examples: dict[tuple, Row] = {}
            for plan in self.deltas:
                for r in arrow_rows(self.engine.run(plan)):
                    k = row_key(r[:-1])
                    delta[k] += r[-1]
                    examples.setdefault(k, r[:-1])
        finally:
            for t in self.tables:
                self.engine.drop(t + "$delta")
        merged = self.counts.copy()
        merged.update(delta)
        if any(n < 0 for n in merged.values()):
            raise ValueError("changes delete rows that are not in the tables")
        # Commit: nothing above changed any state.
        for t, table in new_tables.items():
            self._put(t, table)
        self.counts = Counter({k: n for k, n in merged.items() if n > 0})
        for k, r in examples.items():
            self.examples.setdefault(k, r)
        self._publish()

    def _load_delta_table(self, t: str, ch: Changes) -> None:
        base = self.engine.get(t).schema
        schema = pa.schema([*base, pa.field(WEIGHT, pa.int64())])
        rows = [(*r, 1) for r in ch.inserts] + [(*r, -1) for r in ch.deletes]
        self.engine.put(t + "$delta", to_arrow(rows, schema))

    def _apply_to_table(self, t: str, ch: Changes) -> pa.Table:
        current = self.engine.get(t)
        rows = arrow_rows(current)
        for r in ch.deletes:
            k = row_key(tuple(r))
            hit = next((i for i, x in enumerate(rows) if row_key(x) == k), None)
            if hit is None:
                raise ValueError(f"cannot delete {r!r} from {t}: no such row")
            rows.pop(hit)
        rows += [tuple(r) for r in ch.inserts]
        return to_arrow(rows, current.schema)
