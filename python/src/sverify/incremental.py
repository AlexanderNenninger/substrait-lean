"""Incrementally maintained views on DataFusion or Polars, with delta plans from Lean.

The verified part is the delta plan: `substrait-check --delta` compiles the
view's Substrait plan with `Rel.delta`, splits it into union-free terms
(`Rel.terms`) and applies the weight-column encoding (`Rel.weighted`). Lean
proves the concatenated results are the change to the view
(`Rel.incremental_sound`, `Rel.zeval_terms`, `Rel.weighted_eval`). This module
is the trusted glue around it: it keeps the view as rows with multiplicities,
builds the change tables, runs the delta plans on DataFusion or Polars and merges the
result. A batch is computed completely before anything is replaced, so a
failing batch changes nothing.
"""

from __future__ import annotations

import json
import math
import subprocess
from collections import Counter
from collections.abc import Mapping, Sequence
from dataclasses import dataclass, field

import ibis.expr.types as ir
import pyarrow as pa

from sverify.engine import (
    Backend,
    Engine,
    checker_path,
    put_table,
    read_tables,
    run_plan,
    substrait_json,
    to_arrow,
    to_sql,
    written_plan,
)

Row = tuple
WEIGHT = "__weight"


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
    `engine` runs the plans: the view's plan as Lean read it
    (`written_plan`) and the delta plans, all over the tables of `con`.
    """

    def __init__(
        self, con: Backend, query: ir.Table | str, name: str, engine: Engine = "datafusion"
    ):
        self.con, self.name, self.engine = con, name, engine
        self.sql = query if isinstance(query, str) else to_sql(query)
        plan = json.loads(substrait_json(con, self.sql))
        self.columns: list[str] = plan["relations"][0]["root"]["names"]
        self.tables = read_tables(plan)
        self.deltas = delta_plans(json.dumps(plan))
        self.plan = written_plan(json.dumps(plan))
        result = run_plan(con, self.plan, engine)
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
        put_table(self.con, self.name, to_arrow(rows, self.schema))

    def rows(self) -> list[Row]:
        """The view's contents as a bag of rows, in a canonical order."""
        out = [self.examples[k] for k, n in self.counts.items() for _ in range(n)]
        return sorted(out, key=lambda r: repr(row_key(r)))

    def recompute(self) -> list[Row]:
        """The view computed from scratch, for checking."""
        rows = arrow_rows(run_plan(self.con, self.plan, self.engine))
        return sorted(rows, key=lambda r: repr(row_key(r)))

    def apply(self, changes: Mapping[str, Changes]) -> None:
        unknown = set(changes) - set(self.tables)
        if unknown:
            raise ValueError(f"view does not read {sorted(unknown)}")
        con = self.con
        # New base tables first: this also checks that every delete exists.
        new_tables = {t: self._apply_to_table(t, ch) for t, ch in changes.items()}
        try:
            for t in self.tables:
                self._load_delta_table(t, changes.get(t, Changes()))
            # The delta plans read the *old* tables, so they run before those change.
            delta = Counter[tuple]()
            examples: dict[tuple, Row] = {}
            for plan in self.deltas:
                for r in arrow_rows(run_plan(con, plan, self.engine)):
                    k = row_key(r[:-1])
                    delta[k] += r[-1]
                    examples.setdefault(k, r[:-1])
        finally:
            for t in self.tables:
                con.con.deregister_table(t + "$delta")
        merged = self.counts.copy()
        merged.update(delta)
        if any(n < 0 for n in merged.values()):
            raise ValueError("changes delete rows that are not in the tables")
        # Commit: nothing above changed any state.
        for t, table in new_tables.items():
            put_table(con, t, table)
        self.counts = Counter({k: n for k, n in merged.items() if n > 0})
        for k, r in examples.items():
            self.examples.setdefault(k, r)
        self._publish()

    def _load_delta_table(self, t: str, ch: Changes) -> None:
        base = self.con.con.table(t).schema()
        schema = pa.schema([*base, pa.field(WEIGHT, pa.int64())])
        rows = [(*r, 1) for r in ch.inserts] + [(*r, -1) for r in ch.deletes]
        put_table(self.con, t + "$delta", to_arrow(rows, schema))

    def _apply_to_table(self, t: str, ch: Changes) -> pa.Table:
        current = self.con.con.table(t).to_arrow_table()
        rows = arrow_rows(current)
        for r in ch.deletes:
            k = row_key(tuple(r))
            hit = next((i for i, x in enumerate(rows) if row_key(x) == k), None)
            if hit is None:
                raise ValueError(f"cannot delete {r!r} from {t}: no such row")
            rows.pop(hit)
        rows += [tuple(r) for r in ch.inserts]
        return to_arrow(rows, current.schema)
