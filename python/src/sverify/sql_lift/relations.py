"""The lift's rules of relations: subqueries in expressions (scalar and
EXISTS), `VALUES` in FROM, `UNPIVOT` and `ASOF` joins."""

from __future__ import annotations

import ibis
import ibis.expr.datatypes as dt
import sqlglot.expressions as sge

from sverify.plan_json import (
    Json,
    Unsupported,
    anchor,
    emit_rel,
    field_ref,
    literal,
    values_rel,
)
from sverify.sql_lift._base import (
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
            raise Unsupported(f"{_shown(node)}: VALUES of computed values is not supported yet")
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
        raise Unsupported(f"{_shown(node)} names {len(given)} columns of {width}")
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
            raise Unsupported("UNPIVOT of several value columns is not supported yet")
        if any(p.args.get(k) for k in ("group", "columns", "default_on_null")):
            raise Unsupported(f"{_shown(p)} is not supported yet")
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
            raise Unsupported("UNNEST of an empty list is not supported")
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
    deterministic, and the deterministic profile refuses it as it does for
    `ROW_NUMBER`."""
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


SOURCES[sge.Values] = _values
JOIN_METHODS["ASOF"] = _asof
PARSE_REWRITES.extend([_values_names, _unpivot, _unnest_columns])
