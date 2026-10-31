"""Counterexamples for unproved postconditions.

When Lean cannot prove a postcondition, `verify` searches for small input
tables that meet the preconditions and make the postcondition fail: a row
where it is FALSE or NULL, or for `unique`, two output rows with the same
key. Each candidate is evaluated by `Rel.eval` (`substrait-check` on the plans
with the tables inlined, `sverify.testing`), so a counterexample is real.
Finding none says nothing: the search is bounded.

Candidates are drawn from a small domain per column type: a few simple
values, NULL for nullable columns, and the constants of the plans with their
neighbours (the boundaries a filter or a condition compares against). Tables
grow from one row to three. A counterexample is then shrunk: rows are
dropped, and values replaced by simpler ones, while it stays one.
"""

from __future__ import annotations

import datetime as dt
import json
import math
import random
from collections.abc import Callable, Iterator, Mapping, Sequence
from dataclasses import dataclass
from typing import Any

import ibis.expr.datatypes as dt_types

EPOCH = dt.datetime(1970, 1, 1)


@dataclass(frozen=True)
class Counterexample:
    """Input tables that meet the preconditions, and the transformation's
    output on them (`Rel.eval`), which violates the postcondition."""

    tables: dict[str, list[tuple]]
    output: list[tuple]
    columns: dict[str, list[str]]
    """Column names of each input table, and of the output under `""`."""

    def __str__(self) -> str:
        def named(name: str) -> str:
            return f"{name}({', '.join(self.columns[name])})"

        inputs = ", ".join(f"{named(n)} = {rows!r}" for n, rows in self.tables.items())
        out = f"({', '.join(self.columns[''])})"
        return f"{inputs} gives {out} = {self.output!r}"


Domain = list[object]


def _plan_literals(plans: Sequence[dict]) -> dict[str, set[object]]:
    """The constants of the plans, by kind."""
    found: dict[str, set[object]] = {"int": set(), "float": set(), "str": set(), "ts": set()}

    def walk(node: object) -> None:
        if isinstance(node, dict):
            lit = node.get("literal")
            if isinstance(lit, dict):
                for key in ("i8", "i16", "i32", "i64"):
                    if key in lit and abs(int(lit[key])) < 2**53:
                        found["int"].add(int(lit[key]))
                if isinstance(lit.get("fp64"), int | float):
                    found["float"].add(float(lit["fp64"]))
                if isinstance(lit.get("string"), str):
                    found["str"].add(lit["string"])
                ts = lit.get("precisionTimestamp") or {}
                if "value" in ts and ts.get("precision", 6) == 6:
                    found["ts"].add(int(ts["value"]))
            for v in node.values():
                walk(v)
        elif isinstance(node, list):
            for v in node:
                walk(v)

    for p in plans:
        walk(p)
    return found


def domain(dtype: dt_types.DataType, literals: Mapping[str, set[object]]) -> Domain | None:
    """Values to try for a column, simplest first; None if the type is not
    supported."""
    values: Domain
    if dtype.is_integer():
        near = sorted({v + d for v in literals["int"] for d in (-1, 0, 1)}, key=abs)  # type: ignore[operator]
        values = [0, 1, -1, *near, 2]
    elif dtype.is_floating():
        near = sorted(
            {v + d for v in literals["float"] for d in (-0.5, 0.0, 0.5)},  # type: ignore[operator]
            key=abs,
        )
        values = [0.0, 1.5, -1.0, *near, math.nan, math.inf, -math.inf]
    elif dtype.is_string():
        values = ["", "a", *sorted(literals["str"]), "b"]  # type: ignore[type-var]
    elif dtype.is_boolean():
        values = [False, True]
    elif dtype.is_timestamp() and dtype.timezone is None:  # type: ignore[attr-defined]
        micros = sorted({v + d for v in literals["ts"] for d in (-1, 0, 1)})  # type: ignore[operator]
        near_ts = [EPOCH + dt.timedelta(microseconds=m) for m in micros]
        values = [EPOCH, dt.datetime(2024, 1, 1), *near_ts]
    elif dtype.is_date():
        values = [EPOCH.date(), dt.date(2024, 1, 1)]
    else:
        return None
    unique: Domain = []
    for v in values:
        if not any(v is u or (type(v) is type(u) and v == u) for u in unique):
            unique.append(v)
    if dtype.nullable:
        unique.insert(1, None)
    return unique


class _Search:
    def __init__(
        self,
        schemas: Mapping[str, Any],
        requires: Sequence[tuple[str, dict]],
        keys: Mapping[str, Sequence[Sequence[int]]],
        transform: dict,
        violated: Callable[[dict[str, list[tuple]]], bool],
        domains: dict[str, list[Domain]],
        references: Mapping[str, Sequence[Sequence[Any]]],
    ):
        self.schemas = schemas
        self.references = references
        self.requires = requires
        self.keys = keys
        self.transform = transform
        self.violated = violated
        self.domains = domains

    def admissible(self, tables: dict[str, list[tuple]]) -> bool:
        """The tables meet every precondition."""
        for name, positions in self.keys.items():
            for cols in positions:
                seen = [tuple(r[i] for i in cols) for r in tables.get(name, [])]
                if len(set(seen)) < len(seen):
                    return False
        for name, fks in self.references.items():
            for col, other_table, other in fks:
                present = {repr(r[other]) for r in tables.get(other_table, [])}
                if any(
                    r[col] is not None and repr(r[col]) not in present for r in tables.get(name, [])
                ):
                    return False
        return all(all(v is True for (v,) in evaluate(plan, tables)) for _, plan in self.requires)

    def counterexample(self, tables: dict[str, list[tuple]]) -> bool:
        try:
            return self.admissible(tables) and self.violated(tables)
        except Exception:  # noqa: BLE001 - a value Lean or the reader can't handle: skip it
            return False

    def smaller(self, tables: dict[str, list[tuple]]) -> Iterator[dict[str, list[tuple]]]:
        """Tables with one row fewer, then with one value simpler (earlier in
        its domain)."""
        for name, rows in tables.items():
            for i in range(len(rows)):
                yield {**tables, name: rows[:i] + rows[i + 1 :]}
        for name, rows in tables.items():
            for i, row in enumerate(rows):
                for j, v in enumerate(row):
                    for simpler in self.domains[name][j]:
                        if simpler is v or (type(simpler) is type(v) and simpler == v):
                            break
                        new = row[:j] + (simpler,) + row[j + 1 :]
                        yield {**tables, name: rows[:i] + [new] + rows[i + 1 :]}

    def shrink(self, tables: dict[str, list[tuple]]) -> dict[str, list[tuple]]:
        while True:
            for smaller in self.smaller(tables):
                if self.counterexample(smaller):
                    tables = smaller
                    break
            else:
                return tables


def evaluate(plan: dict, tables: Mapping[str, list[tuple]]) -> list[tuple]:
    """`Rel.eval` of a plan over the given rows."""
    # Imported here: `sverify.testing` imports `sverify.contracts`, which imports this.
    from sverify.testing import inline_tables, lean_values

    return lean_values(json.dumps(inline_tables(json.loads(json.dumps(plan)), tables)))


def search(
    schemas: Mapping[str, Any],
    requires: Sequence[tuple[str, dict]],
    keys: Mapping[str, Sequence[Sequence[int]]],
    transform: dict,
    ensures: dict | Sequence[int],
    budget: int = 200,
    seed: int = 0,
    references: Mapping[str, Sequence[Sequence[Any]]] | None = None,
) -> Counterexample | None:
    """Small input tables meeting `requires` (condition plans per table),
    `keys` (unique column positions per table) and `references` (foreign keys
    per table: column position, referenced table, its column position) on
    which `ensures` fails.

    `ensures` is a condition plan over the transformation's output (it fails
    on a value that is not TRUE) or the column positions of a key of the
    output (it fails on a repeated key). At most `budget` candidates are tried."""
    plans = [transform, *(p for _, p in requires)]
    if isinstance(ensures, dict):
        plans.append(ensures)
    literals = _plan_literals(plans)
    domains: dict[str, list[Domain]] = {}
    for name, schema in schemas.items():
        cols = [domain(t, literals) for _, t in schema.items()]
        if any(d is None for d in cols):
            return None
        domains[name] = cols  # type: ignore[assignment]

    if isinstance(ensures, dict):
        plan = ensures

        def violated(tables: dict[str, list[tuple]]) -> bool:
            return any(v is not True for (v,) in evaluate(plan, tables))

    else:
        key = list(ensures)

        def violated(tables: dict[str, list[tuple]]) -> bool:
            seen = [tuple(r[i] for i in key) for r in evaluate(transform, tables)]
            return len(set(map(repr, seen))) < len(seen)

    s = _Search(schemas, requires, keys, transform, violated, domains, references or {})
    rng = random.Random(seed)
    for n in (1, 2, 3):
        for _ in range(budget // 3):
            tables = {
                name: [tuple(rng.choice(d) for d in doms) for _ in range(n)]
                for name, doms in domains.items()
            }
            if s.counterexample(tables):
                tables = s.shrink(tables)
                columns = {name: list(schema.names) for name, schema in schemas.items()}
                columns[""] = list(transform["relations"][0]["root"]["names"])
                return Counterexample(tables, evaluate(transform, tables), columns)
    return None
