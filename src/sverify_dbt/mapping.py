"""dbt tests and constraints as sverify conditions.

A generic test passes when its query finds no failing rows. Its condition is
the one a row passes by: `not_null(c)` is `c IS NOT NULL`. dbt's tests let
NULLs pass (`accepted_values`, `accepted_range` and the dbt-expectations
ranges and sets select the rows where the comparison is FALSE), so each
condition says `c IS NULL OR …`.

`unique(c)` differs: dbt ignores NULLs, so two NULLs pass, and `sv.unique`
counts NULLs as one key. A proof of `sv.unique(c)` implies dbt's test, so in
`ensures` it maps as it is; in `requires` only where `c` is also not NULL.
"""

from __future__ import annotations

import re
from collections.abc import Callable
from dataclasses import dataclass
from typing import Any

import sqlglot as sg
import sverify as sv

from sverify_dbt.manifest import Test

Condition = Any
"""A condition `sv.verify` takes: a SQL string, `sv.unique(...)` or
`sv.references(...)`."""


@dataclass
class Mapped:
    """A test or constraint as conditions, or why it has none."""

    conditions: list[Condition]
    reason: str | None = None
    """Why there is no condition (`conditions` is empty)."""
    columns: tuple[str, ...] = ()
    """The columns the conditions read."""


def ident(name: str) -> str:
    """`name` as a DuckDB identifier, quoted only where it has to be."""
    if re.fullmatch(r"[a-z_][a-z0-9_]*", name) and name not in _RESERVED:
        return name
    return '"' + name.replace('"', '""') + '"'


_RESERVED = {
    "select",
    "from",
    "where",
    "group",
    "order",
    "by",
    "limit",
    "union",
    "all",
    "and",
    "or",
    "not",
    "null",
    "is",
    "in",
    "as",
    "on",
    "join",
    "case",
    "when",
    "then",
    "else",
    "end",
    "true",
    "false",
    "between",
    "like",
    "distinct",
    "having",
    "with",
    "default",
    "check",
    "primary",
    "unique",
    "references",
    "table",
    "column",
    "user",
    "to",
}


def literal(v: Any, quote: bool = True) -> str:
    """A value of `accepted_values` as SQL: quoted strings unless `quote`
    is false, as dbt writes them."""
    if isinstance(v, bool):
        return "TRUE" if v else "FALSE"
    if isinstance(v, int | float):
        return repr(v)
    s = str(v)
    return "'" + s.replace("'", "''") + "'" if quote else s


def _null_passes(col: str, cond: str) -> str:
    return f"{ident(col)} IS NULL OR ({cond})"


def _filtered(cond: str, where: str | None) -> str:
    """`cond` on the rows `where` keeps, as dbt's `where` config and
    dbt-expectations' `row_condition` filter the rows a test sees."""
    return f"NOT coalesce(({where}), FALSE) OR ({cond})" if where else cond


def _range(col: str, lo: Any, hi: Any, strict_lo: bool, strict_hi: bool) -> str | None:
    parts = []
    if lo is not None:
        parts.append(f"{ident(col)} {'>' if strict_lo else '>='} {lo}")
    if hi is not None:
        parts.append(f"{ident(col)} {'<' if strict_hi else '<='} {hi}")
    return _null_passes(col, " AND ".join(parts)) if parts else None


def test_conditions(
    test: Test,
    *,
    side: str,
    table_of: Callable[[str], str | None],
    not_null: set[str] = frozenset(),  # type: ignore[assignment]
) -> Mapped:
    """The conditions a test states about the relation it is on.

    Args:
        test: The test.
        side: `"requires"` (the relation is an input) or `"ensures"` (the
            relation is the model being checked).
        table_of: The input table name of a relation, by unique id, or None
            when the model does not read it (for `relationships`).
        not_null: The columns known not NULL, for `unique` in `requires`.
    """
    k, kw, col = test.kind, test.kwargs, test.column
    if k is None:
        return Mapped([], "a singular test: sverify-dbt reads generic tests only")
    base = k.split(".")[-1]
    ns = k.split(".")[0] if "." in k else None
    row_filter = test.where
    if ns == "dbt_expectations" and kw.get("row_condition"):
        row_filter = (
            f"({row_filter}) AND ({kw['row_condition']})" if row_filter else kw["row_condition"]
        )
    cond: str | None = None
    if base in ("not_null", "expect_column_values_to_not_be_null") and col:
        cond = f"{ident(col)} IS NOT NULL"
    elif base == "expect_column_values_to_be_null" and col:
        cond = f"{ident(col)} IS NULL"
    elif base in ("unique", "expect_column_values_to_be_unique") and col:
        return _unique(test, (col,), side, not_null, row_filter, nulls_ignored=True)
    elif base in ("unique_combination_of_columns", "expect_compound_columns_to_be_unique"):
        cols = kw.get("combination_of_columns") or kw.get("column_list") or []
        if not cols:
            return Mapped([], "the test names no columns")
        ignore = str(kw.get("ignore_row_if", "all_values_are_missing"))
        nulls_ignored = ns == "dbt_expectations" and ignore != "never"
        return _unique(test, tuple(cols), side, not_null, row_filter, nulls_ignored)
    elif base in ("accepted_values", "expect_column_values_to_be_in_set") and col:
        values = kw.get("values", kw.get("value_set")) or []
        quote = kw.get("quote", kw.get("quote_values", True))
        items = ", ".join(literal(v, quote) for v in values)
        cond = _null_passes(col, f"{ident(col)} IN ({items})") if values else None
    elif base == "expect_column_values_to_not_be_in_set" and col:
        values = kw.get("value_set") or []
        quote = kw.get("quote_values", True)
        items = ", ".join(literal(v, quote) for v in values)
        cond = _null_passes(col, f"{ident(col)} NOT IN ({items})") if values else None
    elif base == "accepted_range" and ns == "dbt_utils" and col:
        strict = not kw.get("inclusive", True)
        cond = _range(col, kw.get("min_value"), kw.get("max_value"), strict, strict)
    elif base == "expect_column_values_to_be_between" and col:
        strict = bool(kw.get("strictly", False))
        cond = _range(col, kw.get("min_value"), kw.get("max_value"), strict, strict)
    elif base == "expression_is_true":
        expr = kw.get("expression")
        if not expr:
            return Mapped([], "the test has no expression")
        if col:
            expr = f"{ident(col)} {expr}"
        cond = f"coalesce(({expr}), TRUE)"
    elif base == "relationships" and col:
        return _references(test, col, side, table_of)
    else:
        return Mapped([], f"sverify-dbt has no mapping for {k}")
    if cond is None:
        return Mapped([], f"the {k} test has no bounds or values")
    return Mapped([_filtered(cond, row_filter)], columns=_cols(test))


def _cols(test: Test) -> tuple[str, ...]:
    cols = test.kwargs.get("combination_of_columns") or test.kwargs.get("column_list")
    if cols:
        return tuple(cols)
    return (test.column,) if test.column else ()


def _unique(
    test: Test,
    cols: tuple[str, ...],
    side: str,
    not_null: set[str],
    where: str | None,
    nulls_ignored: bool,
) -> Mapped:
    if where:
        return Mapped([], "a uniqueness test with a where filter has no sverify condition")
    if side == "requires" and nulls_ignored and not all(c in not_null for c in cols):
        nullable = ", ".join(c for c in cols if c not in not_null)
        return Mapped(
            [],
            f"dbt's {test.kind} lets NULLs repeat, and sv.unique counts them as one key: "
            f"assumed only with a not_null test on {nullable}",
            cols,
        )
    return Mapped([sv.unique(*cols)], columns=cols)


def _references(test: Test, col: str, side: str, table_of: Callable[[str], str | None]) -> Mapped:
    if side == "ensures":
        return Mapped([], "sverify proves no foreign keys of a model's result", (col,))
    others = [d for d in test.depends_on if d != test.on] or test.depends_on
    target = next((t for d in others if (t := table_of(d)) is not None), None)
    field = test.kwargs.get("field")
    if target is None or not field:
        return Mapped([], "the model does not read the referenced relation", (col,))
    return Mapped([sv.references(col, to=(target, field))], columns=(col,))


def constraint_conditions(constraint: dict[str, Any], column: str | None) -> Mapped:
    """A contract's constraint (`not_null`, `unique`, `primary_key`, `check`,
    `foreign_key`) as the conditions it guarantees about the model's rows."""
    kind = constraint.get("type")
    cols = tuple(constraint.get("columns") or ([column] if column else []))
    if kind == "not_null" and cols:
        return Mapped([f"{ident(c)} IS NOT NULL" for c in cols], columns=cols)
    if kind == "unique" and cols:
        return Mapped([sv.unique(*cols)], columns=cols)
    if kind == "primary_key" and cols:
        return Mapped([*(f"{ident(c)} IS NOT NULL" for c in cols), sv.unique(*cols)], columns=cols)
    if kind == "check" and constraint.get("expression"):
        return Mapped([f"coalesce(({constraint['expression']}), TRUE)"], columns=cols)
    if kind == "foreign_key":
        return Mapped([], "sverify proves no foreign keys of a model's result", cols)
    return Mapped([], f"sverify-dbt has no mapping for a {kind} constraint", cols)


def constraint_label(constraint: dict[str, Any], column: str | None) -> str:
    cols = constraint.get("columns") or ([column] if column else [])
    expr = constraint.get("expression")
    inner = ", ".join(cols) if cols else (expr or "")
    return f"{constraint.get('type')}({inner})"


@dataclass
class Bound:
    """A bound on one column, parsed from an inferred precondition."""

    column: str
    op: str
    value: str


def bound(sql: str) -> Bound | None:
    """`"qty" IS NULL OR "qty" < 9000000000000000000` as a bound on `qty`."""
    try:
        tree = sg.parse_one(sql, read="duckdb")
    except sg.errors.ParseError:
        return None
    if isinstance(tree, sg.exp.Or) and isinstance(tree.this, sg.exp.Is):
        tree = tree.expression
    tree = tree.unnest() if isinstance(tree, sg.exp.Paren) else tree
    ops: dict[type, str] = {sg.exp.LT: "<", sg.exp.LTE: "<=", sg.exp.GT: ">", sg.exp.GTE: ">="}
    op = ops.get(type(tree))
    if op is None:
        return None
    left, right = tree.this, tree.expression
    if isinstance(right, sg.exp.Column) and not isinstance(left, sg.exp.Column):
        left, right = right, left
        op = {"<": ">", "<=": ">=", ">": "<", ">=": "<="}[op]
    if not isinstance(left, sg.exp.Column):
        return None
    return Bound(left.name, op, right.sql("duckdb"))


def as_dbt_test(sql: str) -> tuple[str | None, str]:
    """A precondition as a dbt test to add: the column it goes on (None for
    a test on the table) and the test's YAML."""
    b = bound(sql)
    if b is None:
        expr = sql.replace("\n", " ")
        return None, f'dbt_utils.expression_is_true: {{arguments: {{expression: "{expr}"}}}}'
    key = "max_value" if b.op in ("<", "<=") else "min_value"
    inclusive = "" if b.op in ("<=", ">=") else ", inclusive: false"
    return b.column, f"dbt_utils.accepted_range: {{arguments: {{{key}: {b.value}{inclusive}}}}}"
