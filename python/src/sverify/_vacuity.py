"""Preconditions that no row can meet (#1485).

Internal: not part of sverify's public API.

`requires` such as `amount > 5` and `amount < 3` is accepted, and every
postcondition then holds on the empty set of rows. `contradictions` finds the
simple cases: comparisons of one column with a number, per table, whose
bounds on a column leave no value. It reads Ibis conditions and SQL
strings, and ignores any other condition.
"""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from fractions import Fraction
from typing import Any

import ibis
import ibis.expr.operations as ops
from ibis.common.deferred import Deferred

Atom = tuple[str, str, Fraction]  # (column, comparison, number)

_SQL = {">": ">", ">=": ">=", "<": "<", "<=": "<=", "=": "="}
_FLIP = {">": "<", ">=": "<=", "<": ">", "<=": ">=", "=": "="}
_IBIS = {
    ops.Greater: ">",
    ops.GreaterEqual: ">=",
    ops.Less: "<",
    ops.LessEqual: "<=",
    ops.Equals: "=",
}


def _number(v: Any) -> Fraction | None:
    if isinstance(v, bool) or not isinstance(v, int | float):
        return None
    return Fraction(v)


def _ibis_atoms(op: Any, out: list[Atom]) -> None:
    if isinstance(op, ops.And):
        _ibis_atoms(op.left, out)
        _ibis_atoms(op.right, out)
        return
    cmp = _IBIS.get(type(op))
    if cmp is None:
        return
    left, right = op.left, op.right
    if isinstance(left, ops.Literal) and isinstance(right, ops.Field):
        left, right, cmp = right, left, _FLIP[cmp]
    if isinstance(left, ops.Field) and isinstance(right, ops.Literal):
        n = _number(right.value)
        if n is not None:
            out.append((left.name, cmp, n))


def _sql_atoms(text: str, out: list[Atom]) -> None:
    import sqlglot
    from sqlglot import exp

    try:
        tree = sqlglot.parse_one(text, read="duckdb")
    except sqlglot.errors.ParseError:
        return
    kinds: dict[type, str] = {exp.GT: ">", exp.GTE: ">=", exp.LT: "<", exp.LTE: "<=", exp.EQ: "="}
    for node in [tree] if not isinstance(tree, exp.And) else list(tree.flatten()):
        cmp = kinds.get(type(node))
        if cmp is None:
            continue
        left, right = node.this, node.expression
        if isinstance(left, exp.Literal) and isinstance(right, exp.Column):
            left, right, cmp = right, left, _FLIP[cmp]
        if isinstance(left, exp.Column) and isinstance(right, exp.Literal) and not right.is_string:
            out.append((left.name, cmp, Fraction(right.this)))


def atoms(cond: Any, columns: Mapping[str, Any]) -> list[Atom]:
    """The comparisons of a column with a number that `cond` states."""
    out: list[Atom] = []
    if isinstance(cond, str):
        _sql_atoms(cond, out)
        return out
    try:
        table = ibis.table(ibis.schema(dict(columns)), name="t")
        expr = cond.resolve(table) if isinstance(cond, Deferred) else cond(table)
        _ibis_atoms(expr.op(), out)
    except Exception:  # noqa: BLE001 - a condition we cannot read is not checked
        return []
    return out


def _empty(atoms_: Sequence[Atom], integer: bool) -> bool:
    lo: tuple[Fraction, bool] | None = None
    hi: tuple[Fraction, bool] | None = None
    for _, cmp, n in atoms_:
        if cmp in (">", ">="):
            lo = max(lo, (n, cmp == ">"), key=lambda b: (b[0], b[1])) if lo else (n, cmp == ">")
        if cmp in ("<", "<="):
            hi = min(hi, (n, cmp == "<"), key=lambda b: (b[0], not b[1])) if hi else (n, cmp == "<")
        if cmp == "=":
            lo = max(lo, (n, False), key=lambda b: (b[0], b[1])) if lo else (n, False)
            hi = min(hi, (n, False), key=lambda b: (b[0], not b[1])) if hi else (n, False)
    if lo is None or hi is None:
        return False
    (a, a_strict), (b, b_strict) = lo, hi
    if integer:
        a = a + 1 if a_strict and a.denominator == 1 else Fraction(-(-a // 1))
        b = b - 1 if b_strict and b.denominator == 1 else Fraction(b // 1)
        return a > b
    return a > b or (a == b and (a_strict or b_strict))


def contradictions(requires: Mapping[str, Sequence[Any]], schemas: Mapping[str, Any]) -> list[str]:
    """One sentence per column whose `requires` leave no value."""
    out = []
    for table, conds in requires.items():
        columns = dict(schemas.get(table, {}).items())
        by_col: dict[str, list[Atom]] = {}
        for cond in conds:
            for atom in atoms(cond, columns):
                by_col.setdefault(atom[0], []).append(atom)
        for col, found in by_col.items():
            dtype = columns.get(col)
            if _empty(found, bool(dtype is not None and dtype.is_integer())):
                shown = " and ".join(
                    f"{c} {op} {n if n.denominator != 1 else int(n)}" for c, op, n in found
                )
                out.append(
                    f"the requires of {table!r} contradict each other on `{col}` ({shown}): "
                    "no row meets them, so every ensures holds with nothing to check"
                )
    return out
