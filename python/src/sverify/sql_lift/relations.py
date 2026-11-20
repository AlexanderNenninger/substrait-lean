"""The lift's rules of relations: subqueries in expressions (scalar and
EXISTS), `VALUES` in FROM, `UNPIVOT` and `ASOF` joins."""

from __future__ import annotations

from datetime import date, datetime, timedelta
from typing import Any

import ibis
import ibis.expr.datatypes as dt
import sqlglot.expressions as sge
from sqlglot.transforms import eliminate_qualify

from sverify.plan_json import (
    Json,
    SqlUnsupported,
    Unsupported,
    anchor,
    emit_rel,
    field_ref,
    literal,
    values_rel,
)
from sverify.sql_lift._base import (
    DIALECT,
    JOIN_METHODS,
    PARSE_REWRITES,
    SOURCES,
    Bound,
    Column,
    E,
    Sub,
    _fn,
    _Lift,
    _normalized,
    _numbered,
    _shown,
    register,
)


def _scalar_subquery(lf: _Lift, node: sge.Subquery, sub: Sub, scope: list[Column]) -> E:
    # At most one row, which the checker must prove (an aggregate without
    # groups, LIMIT 1); no row is NULL.
    rel, cols = lf.nested(node.this, scope)
    if len(cols) != 1:
        raise Unsupported("a scalar subquery must return one column")
    return E({"subquery": {"scalar": {"input": rel}}}, cols[0].type.copy(nullable=True))


def _exists(lf: _Lift, node: sge.Exists, sub: Sub, scope: list[Column]) -> E:
    rel, _ = lf.nested(node.this, scope)
    exists_ = {"predicateOp": "PREDICATE_OP_EXISTS", "tuples": rel}
    return E({"subquery": {"setPredicate": exists_}}, dt.boolean)


register(
    {
        sge.Subquery: _scalar_subquery,
        sge.Exists: _exists,
    }
)


# --------------------------------------------------------------------------
# Relations (#803, #804, #805)


def _values(lf: _Lift, node: sge.Values) -> tuple[Json, list[Column]]:
    """`(VALUES (1, 'a'), (2, 'b')) v(k, s)` in FROM (#803): a virtual table of
    constants, each column at the common type of its rows as DuckDB types it
    (`(1), (2.5)` is a `DECIMAL(11, 1)`), named `col0`, `col1`, … unless the
    alias names them."""
    rows = [list(r.expressions) if isinstance(r, sge.Tuple) else [r] for r in node.expressions]
    if not rows or len({len(r) for r in rows}) != 1:
        raise Unsupported(f"{_shown(node)}: every row of VALUES needs the same number of values")
    cells = [[lf.expr(c, [], Bound()) for c in r] for r in rows]
    for c in (c for r in cells for c in r):
        if not c.constant:
            raise SqlUnsupported(f"{_shown(node)}: VALUES of computed values is not supported yet")
    width = len(rows[0])
    types = []
    for i in range(width):
        column = [r[i] for r in cells]
        t = (
            dt.int32
            if all(c.type.is_null() for c in column)
            else lf.common(column, "a column of VALUES")
        )
        types.append(t.copy(nullable=True))
    alias = node.args.get("alias")
    given = [c.name for c in alias.columns] if alias is not None else []
    if len(given) > width:
        raise Unsupported(
            f"{_shown(node)} names {len(given)} columns of {width}; name at most {width}"
        )
    names = [_normalized(n) for n in given] + [f"col{i}" for i in range(len(given), width)]
    out = [[literal(lf.to(c, t).value, t) for c, t in zip(r, types, strict=True)] for r in cells]
    schema = ibis.schema(dict(zip(names, types, strict=True)))
    table = alias.name if alias is not None and alias.name else None
    return values_rel(schema, out), [Column(table, n, t) for n, t in zip(names, types, strict=True)]


def _values_names(tree: sge.Expr) -> sge.Expr:
    """DuckDB names the columns of `VALUES` without an alias's column list
    `col0`, `col1`, …; SQLGlot needs the names to resolve them."""
    for v in tree.find_all(sge.Values):
        alias = v.args.get("alias")
        rows = v.expressions
        if not rows or (alias is not None and alias.columns):
            continue
        width = len(rows[0].expressions) if isinstance(rows[0], sge.Tuple) else 1
        alias = alias or sge.TableAlias(this=sge.to_identifier("valueslist"))
        alias.set("columns", [sge.to_identifier(f"col{i}") for i in range(width)])
        v.set("alias", alias)
    return tree


def _unpivot(tree: sge.Expr) -> sge.Expr:
    """`src UNPIVOT [INCLUDE NULLS] (v FOR k IN (a, b AS 'x'))` (#804) as the
    `UNION ALL` it means: one branch per column, `SELECT * EXCLUDE (a, b),
    'a' AS k, a AS v FROM src WHERE a IS NOT NULL`. The set operation casts
    the values to their common type, as DuckDB does."""

    def node(n: sge.Expr) -> sge.Expr:
        pivots = n.args.get("pivots") if isinstance(n, sge.Table | sge.Subquery) else None
        if not pivots:
            return n
        if len(pivots) != 1 or not pivots[0].args.get("unpivot"):
            return n  # PIVOT: refused as before
        p = pivots[0]
        values, fields = p.expressions, p.args.get("fields") or []
        if len(values) != 1 or len(fields) != 1 or not isinstance(fields[0], sge.In):
            raise SqlUnsupported("UNPIVOT of several value columns is not supported yet")
        if any(p.args.get(k) for k in ("group", "columns", "default_on_null")):
            raise SqlUnsupported(f"{_shown(p)} is not supported yet")
        value, name = values[0].name, fields[0].this.name
        cols: list[tuple[sge.Expression, str]] = []
        for c in fields[0].expressions:
            label = c.args.get("alias") if isinstance(c, sge.PivotAlias) else None
            col = c.this if isinstance(c, sge.PivotAlias) else c
            if not isinstance(col, sge.Column):
                raise Unsupported(f"UNPIVOT of {_shown(col)} is not supported; only columns")
            text = label.name if isinstance(label, sge.Expression) else col.name
            cols.append((col, text))
        src = n.copy()
        src.set("pivots", None)
        alias = p.args.get("alias") or src.args.get("alias")
        src.set("alias", None)
        if isinstance(src, sge.Subquery):
            src = src.this
        branches = []
        for col, text in cols:
            star = sge.Star(except_=[sge.column(c.name) for c, _ in cols])
            sel = sge.select(
                star,
                sge.alias_(sge.Literal.string(text), name),
                sge.alias_(sge.column(col.name), value),
            ).from_(
                sge.Subquery(this=src.copy(), alias=sge.TableAlias(this=sge.to_identifier("_u")))
                if not isinstance(src, sge.Table)
                else src.copy()
            )
            if not p.args.get("include_nulls"):
                sel = sel.where(
                    sge.Not(this=sge.Is(this=sge.column(col.name), expression=sge.Null()))
                )
            branches.append(sel)
        union: sge.Expression = branches[0]
        for b in branches[1:]:
            union = sge.Union(this=union, expression=b, distinct=False)
        return sge.Subquery(
            this=union, alias=alias or sge.TableAlias(this=sge.to_identifier("unpivot"))
        )

    return tree.transform(node, copy=False)


def _unnest_columns(tree: sge.Expr) -> sge.Expr:
    """`SELECT id, unnest(['a', 'b']) AS k, unnest([a, b]) AS v FROM t`
    (#804, dbt's and Ibis's unpivot): `UNNEST`s of lists written out, of one
    length `n`, side by side, as the `UNION ALL` of `n` copies of the SELECT,
    the `i`-th reading each list's `i`-th element. A NULL element stays a
    row, as in DuckDB."""

    def node(n: sge.Expr) -> sge.Expr:
        if not isinstance(n, sge.Select):
            return n
        explodes = [x for e in n.expressions for x in e.find_all(sge.Explode)]
        if not explodes or not all(isinstance(x.this, sge.Array) for x in explodes):
            return n
        if any(x.args.get("expressions") for x in explodes):
            return n
        sizes = {len(x.this.expressions) for x in explodes}
        computed = any(
            not isinstance(e, sge.Literal | sge.Null | sge.Neg)
            for x in explodes
            for e in x.this.expressions
        )
        if len(sizes) != 1 or (len(explodes) == 1 and not computed):
            return n  # one list of constants: `Rel.unnest`, as before
        if any(
            n.args.get(k)
            for k in (
                "group",
                "having",
                "order",
                "limit",
                "offset",
                "distinct",
                "qualify",
                "windows",
            )
        ):
            raise Unsupported(
                "UNNEST of lists written out, next to GROUP BY, ORDER BY, LIMIT or DISTINCT, "
                "is not supported yet; unpivot in a subquery"
            )
        (size,) = sizes
        if size == 0:
            raise SqlUnsupported("UNNEST of an empty list is not supported")
        branches = []
        for i in range(size):
            b = n.copy()
            for x in list(b.find_all(sge.Explode)):
                x.replace(x.this.expressions[i].copy())
            branches.append(b)
        out: sge.Expression = branches[0]
        for b in branches[1:]:
            out = sge.Union(this=out, expression=b, distinct=False)
        return out

    return tree.transform(node, copy=False)


def _asof(lf: _Lift, rel: Json, scope: list[Column], join: sge.Join) -> tuple[Json, list[Column]]:
    """`l ASOF [LEFT] JOIN r ON l.k = r.k AND l.t >= r.t` (#805): each left
    row with the one right row of the ON's equalities whose `r.t` is the
    greatest at or before `l.t` (`>=`, `>`; the least at or after for `<=`,
    `<`). Written as `sverify.asof_join` writes it: the left rows numbered
    (equal rows apart), the inner (left) join on the whole ON, ranked by
    `ROW_NUMBER` per left row, latest first, and the first kept. Right rows
    that tie on `r.t` leave the match to the engine: the plan is not
    deterministic, and a run that must be reproducible (`reproducible=`)
    refuses it as it does for `ROW_NUMBER`. That DuckDB's operator returns a
    row this shape allows is the fact `duckdb-asof-join`, which the writer's
    native ASOF JOIN rests on too (#1447)."""
    side, kind = (join.side or "").upper(), (join.kind or "").upper()
    if kind or side not in ("", "LEFT"):
        raise Unsupported(f"ASOF {side} {kind} JOIN is not supported; only ASOF [LEFT] JOIN")
    on = join.args.get("on")
    if on is None or join.args.get("using"):
        raise Unsupported("ASOF JOIN needs an ON condition (USING is not supported yet)")
    right, cols = lf.source(join.this)
    n, m = len(scope), len(cols)
    left_names = {(c.table, c.name) for c in scope}

    def is_right(e: sge.Expression) -> bool | None:
        refs = {(c.table, c.name) for c in e.find_all(sge.Column)}
        if not refs:
            return None
        if all((t, c) not in left_names for t, c in refs):
            return True
        if all((t, c) in left_names for t, c in refs):
            return False
        return None

    conjuncts = list(on.flatten()) if isinstance(on, sge.And) else [on]
    ineqs = [c for c in conjuncts if isinstance(c, sge.GTE | sge.GT | sge.LTE | sge.LT)]
    if len(ineqs) != 1:
        raise Unsupported("ASOF JOIN needs exactly one of >=, >, <= and < in its ON")
    ineq = ineqs[0]
    lhs, rhs = is_right(ineq.this), is_right(ineq.expression)
    if {lhs, rhs} != {True, False}:
        raise Unsupported(f"ASOF JOIN: {_shown(ineq)} must compare a left and a right expression")
    # Is the right side's time at or before the left's (keep the latest)?
    right_below = isinstance(ineq, sge.GTE | sge.GT) == (rhs is True)
    right_time = ineq.expression if rhs else ineq.this
    number = Column(None, "\x00asof_row", dt.int64)
    joined_scope = scope + [number] + cols
    cond = lf.condition(on, joined_scope)
    how = "JOIN_TYPE_LEFT" if side == "LEFT" else "JOIN_TYPE_INNER"
    out: Json = {
        "join": {"left": _numbered(rel, n), "right": right, "expression": cond, "type": how}
    }
    width = n + 1 + m
    # The right side's time as a column, which the ranking sorts by.
    t = lf.expr(right_time, joined_scope, Bound())
    out = {"project": {"input": out, "expressions": [t.json]}}
    rank = {
        "functionReference": anchor("row_number"),
        "partitions": [field_ref(i) for i in range(n + 1)],
        "sorts": [
            {
                "expr": field_ref(width),
                "direction": f"SORT_DIRECTION_{'DESC' if right_below else 'ASC'}_NULLS_LAST",
            }
        ],
        "arguments": [],
        "lowerBound": {"unbounded": {}},
        "upperBound": {"unbounded": {}},
        "boundsType": "BOUNDS_TYPE_ROWS",
    }
    out = {"project": {"input": out, "expressions": [{"windowFunction": rank}]}}
    first = _fn("equal", [field_ref(width + 1), literal(1, dt.int64)], dt.boolean)
    out = {"filter": {"input": out, "condition": first}}
    return emit_rel(out, [*range(n), *range(n + 1, width)]), scope + cols


#: The most rows a `range` or `generate_series` input is written as (#321).
_SERIES_ROWS = 10_000

_STEP_UNITS = {
    "WEEK": timedelta(weeks=1),
    "DAY": timedelta(days=1),
    "HOUR": timedelta(hours=1),
    "MINUTE": timedelta(minutes=1),
    "SECOND": timedelta(seconds=1),
}


def _constant(node: sge.Expr) -> int | datetime | None:
    """A constant bound of a series: an integer literal, or a string literal
    cast to DATE or TIMESTAMP (`DATE '2024-01-01'`); None for anything else."""
    while isinstance(node, sge.Paren):
        node = node.this
    if isinstance(node, sge.Neg):
        inner = _constant(node.this)
        return -inner if isinstance(inner, int) else None
    if isinstance(node, sge.Literal) and not node.is_string and node.name.isdigit():
        return int(node.name)
    if isinstance(node, sge.Cast) and isinstance(node.this, sge.Literal) and node.this.is_string:
        kind = node.to.this
        try:
            if kind == sge.DataType.Type.DATE:
                return datetime.combine(
                    date.fromisoformat(node.this.name.strip()), datetime.min.time()
                )
            if kind in (sge.DataType.Type.TIMESTAMP, sge.DataType.Type.TIMESTAMPNTZ):
                return datetime.fromisoformat(node.this.name.strip())
        except ValueError:
            return None
    return None


def _ascending(step: Any) -> bool:
    return bool(step > (timedelta(0) if isinstance(step, timedelta) else 0))


def _series(tree: sge.Expr) -> sge.Expr:
    """`range(a, b[, step])` and `generate_series(a, b[, step])` in FROM with
    constant bounds (#321) as the `VALUES` they list, one row per value: the
    usual date spine. `range` excludes `b`, `generate_series` includes it. Over
    dates DuckDB's values are timestamps. Bounds that depend on the data are
    refused: the relation's size would depend on it."""

    def node(n: sge.Expr) -> sge.Expr:
        if isinstance(n, sge.Table) and isinstance(n.this, sge.GenerateSeries):
            series = n.this
        elif (
            isinstance(n, sge.Unnest)
            and len(n.expressions) == 1
            and isinstance(n.expressions[0], sge.GenerateSeries)
            and not n.args.get("offset")
        ):
            series = n.expressions[0]  # FROM UNNEST(generate_series(…)) AS t(d)
        else:
            return n
        name = "range" if series.args.get("is_end_exclusive") else "generate_series"
        if n.args.get("sample"):
            raise SqlUnsupported(
                f"{name} with TABLESAMPLE is not supported",
                hint="sample the input before sverify reads it; write this step in Ibis",
                construct=f"function {name}",
            )
        start, end = _constant(series.args["start"]), _constant(series.args["end"])
        step_node = series.args.get("step")
        if start is None or end is None:
            raise SqlUnsupported(
                f"{name} with bounds that depend on the data is not supported",
                hint="write constant bounds: the relation's size cannot depend on the data",
                issue=321,
                construct=f"function {name}",
            )
        temporal = isinstance(start, datetime)
        if temporal != isinstance(end, datetime):
            raise SqlUnsupported(
                f"{name} of an integer and a date or timestamp is not supported",
                construct=f"function {name}",
            )
        step: Any
        if step_node is None:
            if temporal:
                # DuckDB: "No function matches" `range(DATE, DATE)`; it wants an INTERVAL.
                raise SqlUnsupported(
                    f"{name} of dates or timestamps needs an INTERVAL step in DuckDB",
                    hint="add the step, for example INTERVAL 1 DAY",
                    construct=f"function {name}",
                )
            step = 1
        elif isinstance(step_node, sge.Interval):
            unit = step_node.args.get("unit")
            count = step_node.this
            if not (temporal and unit is not None and unit.name.upper() in _STEP_UNITS) or not (
                isinstance(count, sge.Literal) and count.name.isdigit()
            ):
                raise SqlUnsupported(
                    f"{name} with the step {step_node.sql(DIALECT)} is not supported",
                    hint="use a step of whole weeks, days, hours, minutes or seconds",
                    issue=321,
                    construct=f"function {name}",
                )
            step = _STEP_UNITS[unit.name.upper()] * int(count.name)
        else:
            step = _constant(step_node)
            if not isinstance(step, int) or temporal:
                raise SqlUnsupported(
                    f"{name} with the step {step_node.sql(DIALECT)} is not supported",
                    construct=f"function {name}",
                )
        if not step:
            raise SqlUnsupported(
                f"{name} with a step of 0 raises in DuckDB", construct=f"function {name}"
            )
        values: list[Any] = []
        at: Any = start
        forward = _ascending(step)
        while (at < end if forward else at > end) or (
            not series.args.get("is_end_exclusive") and at == end
        ):
            values.append(at)
            at += step
            if len(values) > _SERIES_ROWS:
                raise SqlUnsupported(
                    f"{name} lists more than {_SERIES_ROWS} rows, which is not supported",
                    issue=321,
                    construct=f"function {name}",
                )
        if not values:
            raise SqlUnsupported(
                f"{name} lists no rows, which is not supported yet",
                issue=321,
                construct=f"function {name}",
            )
        if temporal:
            cells = [
                sge.Cast(
                    this=sge.Literal.string(v.isoformat(sep=" ")),
                    to=sge.DataType.build("TIMESTAMP"),
                )
                for v in values
            ]
        else:
            cells = [
                sge.Cast(this=sge.Literal.number(v), to=sge.DataType.build("BIGINT"))
                for v in values
            ]
        alias = n.args.get("alias") or sge.TableAlias(this=sge.to_identifier(name))
        if not alias.columns:
            alias.set("columns", [sge.to_identifier(name)])
        return sge.Values(expressions=[sge.Tuple(expressions=[c]) for c in cells], alias=alias)

    return tree.transform(node, copy=False)


SOURCES[sge.Values] = _values
JOIN_METHODS["ASOF"] = _asof


def _group_all(tree: sge.Expr) -> sge.Expr:
    """`GROUP BY ALL` (#1991): DuckDB groups by the select items that hold no
    aggregate; none left is one group for the whole input. A select item with
    a window function is refused: DuckDB's reading of it is not probed."""
    for sel in list(tree.find_all(sge.Select)):
        group = sel.args.get("group")
        if group is None or not group.args.get("all"):
            continue
        keys: list[sge.Expression] = []
        for item in sel.expressions:
            if item.find(sge.Window):
                raise SqlUnsupported(
                    "GROUP BY ALL with a window function in the SELECT", construct="GROUP BY ALL"
                )
            if not item.find(sge.AggFunc):
                keys.append(item.unalias().copy())
        sel.set("group", sge.Group(expressions=keys) if keys else None)
    return tree


_QUALIFY_COLUMN = "_sverify_qualify"


def _qualify(tree: sge.Expr) -> sge.Expr:
    """`QUALIFY` (#319) as the filter of a subquery over the window columns
    (SQLGlot's `eliminate_qualify`, the form its dialects without QUALIFY
    print). The columns it adds (`_w`, `_w_2`, …) are renamed so no table's
    column collides, and a star of the outer select leaves them out."""
    for sel in list(tree.find_all(sge.Select)):
        if sel.args.get("qualify") is not None:
            if any(
                i.name.startswith(("_w", _QUALIFY_COLUMN)) for i in sel.find_all(sge.Identifier)
            ):
                raise SqlUnsupported(
                    "QUALIFY in a query that names a column `_w…` or `_sverify_qualify…`",
                    construct="QUALIFY",
                )
            own = len(sel.expressions)
            new = eliminate_qualify(sel)  # a new outer SELECT around `sel`
            if new is not sel:
                inner = new.args["from_"].this.this
                added = [e.alias for e in inner.expressions[own:]]
                renamed = {a: _QUALIFY_COLUMN + a.removeprefix("_w") for a in added}
                for i in new.find_all(sge.Identifier):
                    if i.name in renamed:
                        i.set("this", renamed[i.name])
                for star in new.args["expressions"]:
                    if isinstance(star, sge.Star):
                        star.set("except_", [sge.column(n) for n in renamed.values()])
            if sel is tree:
                tree = new
            elif new is not sel:
                sel.replace(new)
    return tree


PARSE_REWRITES.extend([_series, _group_all, _qualify, _values_names, _unpivot, _unnest_columns])
