"""Touched-group recompute: an aggregate without delta rules, maintained at
the cost of the groups a batch touches.

Internal: not part of sverify's public API.

A view that ends in an aggregate (under filters, projections and sorts of
its output rows that read only their own row, and keep the group keys) and
whose input has delta rules is maintained in three steps per batch:

1. the input's change, from the input's delta plans;
2. the group keys of the rows it inserts or deletes (`keys`);
3. the view over the new input rows with those keys, a semi-join on the
   keys with NULLs equal (`recompute`). These rows replace the view's rows
   of the same keys.

Groups are independent, so this is the full recomputation for any measure
(`TouchedGroups.touched_sound` and `TouchedGroups.touched_eval` in
`SubstraitLean/TouchedGroups.lean`). Filters and projections over the
aggregate act on each output row, and keep the group keys, so they keep the
split. This module is trusted glue: it recognises the shape on the Ibis
expression and builds the three plans, which Lean checks as it checks any
plan.
"""

from __future__ import annotations

from dataclasses import dataclass
from datetime import timedelta
from typing import Any

import ibis
import ibis.expr.operations as ops
import ibis.expr.types as ir

from sverify._retention import _aggregate, _bucket, _own_tree, _row_local, _under

SQL = "the view is SQL; touched groups need an Ibis expression"
NOT_AGGREGATE = "not an aggregate or a window under filters and projections of its rows"


@dataclass(frozen=True)
class Touched:
    """The plans that maintain a view by touched groups."""

    columns: list[str]
    """The view's columns that hold the group keys, in key order."""
    deltas: list[str]
    """The delta plans of the aggregate's input."""
    input_names: list[str]
    """The input's columns."""
    keys: str
    """The distinct group keys `k0, k1, …` of the rows of table `<view>$in`
    (the input's columns)."""
    recompute: str
    """The view over the input rows whose keys are rows of `<view>$keys`."""
    ranged: Ranged | None = None
    """With a time bucket among the keys: `recompute` that reads only the
    input rows in the touched buckets' time range."""


@dataclass(frozen=True)
class Ranged:
    """`Touched.recompute` over the input rows whose time column lies in the
    range of the one-row table `<view>$range` (`__lo`, `__hi`): the rows of the
    buckets from `lo` up to `hi`, a superset of the touched buckets' rows,
    since a bucket starting at `b` holds the times in `[b, b + width)`
    (`Retention.bucket_le`, `Retention.lt_bucket_add`). The semi-join on the
    keys still picks the exact rows; the range lets the engine skip the
    others while it scans."""

    key: int
    """Which key is the bucket."""
    width: timedelta
    plan: str


def plan(name: str, query: ir.Table | str) -> Touched | str:
    """How to maintain the view `name` of `query` by touched groups, or why
    it cannot be."""
    from sverify.engine import plan_json, written_plan
    from sverify.incremental import NotIncremental, delta_plans

    if isinstance(query, str):
        return SQL
    found = _split(query.op())
    if isinstance(found, str):
        return found
    node, by, names, what = found
    if missing := [g for g in by if g not in names]:
        return f"the view does not output the {what} key {missing[0]} unchanged"
    parent = node.parent.to_expr()  # type: ignore[attr-defined]
    try:
        deltas = delta_plans(plan_json(None, parent))  # type: ignore[arg-type]
    except NotIncremental as e:
        return f"the {what}'s input has no delta rules ({e})"
    groups = list(by.values())
    agg: Any = node
    rows = ibis.table(parent.schema(), name=f"{name}$in")
    keys = rows.select(
        **{f"k{i}": g.replace({agg.parent: rows.op()}).to_expr() for i, g in enumerate(groups)}
    ).distinct()
    touched = ibis.table(keys.schema(), name=f"{name}$keys")
    on = [g.to_expr().identical_to(touched[f"k{i}"]) for i, g in enumerate(groups)]  # type: ignore[union-attr]
    hole = ibis.table(parent.schema(), name=f"{name}$hole").op()

    def over(narrowed: ir.Table) -> str:
        # Through a placeholder: `narrowed` holds the input itself.
        q = query.op().replace({agg.parent: hole}).replace({hole: narrowed.op()})
        return written_plan(plan_json(None, q.to_expr()))  # type: ignore[arg-type,attr-defined]

    return Touched(
        columns=[names[g] for g in by],
        deltas=deltas,
        input_names=list(parent.columns),
        keys=written_plan(plan_json(None, keys)),  # type: ignore[arg-type]
        recompute=over(parent.semi_join(touched, on)),
        ranged=_ranged(name, agg, groups, touched, over),
    )


def _split(
    op: ops.Relation,
) -> tuple[ops.Relation, dict[str, ops.Value], dict[str, str], str] | str:
    """The relation a view ends in whose rows split by key: an aggregate
    (its GROUP BY), or a projection whose window functions all share one
    PARTITION BY. Returns it, its keys by the name of the column that holds
    each, the view's column for each of its columns, and what it is; or why
    the view has no such relation."""
    found = _aggregate(op)
    if found is not None:
        agg, names = found
        if not agg.groups:
            return "the aggregate has no GROUP BY"
        if not _row_local(list(agg.groups.values()), agg.parent):
            return "a grouping key reads other rows"
        return agg, dict(agg.groups), names, "group"
    found = _under(op, _windowed)
    if found is None:
        return NOT_AGGREGATE
    proj, names = found
    assert isinstance(proj, ops.Project)
    wins = [w for v in proj.values.values() for w in v.find(ops.WindowFunction, filter=_own_tree)]
    parts = {tuple(w.group_by) for w in wins}
    if len(parts) != 1 or not (part := next(iter(parts))):
        return "the window functions do not share one PARTITION BY"
    for v in proj.values.values():
        if v.find(ops.Subquery, filter=_own_tree) or any(
            f.rel != proj.parent for f in v.find(ops.Field, filter=_own_tree)
        ):
            return "a window reads another relation"
    if any(isinstance(w.func, ops.Analytic) and not w.order_by for w in wins):
        return "an analytic window function has no ORDER BY"
    by = {}
    for p in part:
        name = next((n for n, v in proj.values.items() if v == p), None)
        if name is None:
            return "the view does not output its PARTITION BY keys"
        by[name] = p
    return proj, by, names, "partition"


def _windowed(op: ops.Relation) -> bool:
    return isinstance(op, ops.Project) and any(
        v.find(ops.WindowFunction, filter=_own_tree) for v in op.values.values()
    )


def _ranged(name, agg, groups, touched, over) -> Ranged | None:
    """`Ranged` for the first key that is a fixed-width time bucket of an
    input column, if one is."""
    for i, g in enumerate(groups):
        b = _bucket(g)
        if isinstance(b, str) or b[0].rel != agg.parent:
            continue
        f, width, _origin = b
        parent = agg.parent.to_expr()
        dtype = touched[f"k{i}"].type()
        bounds = ibis.table({"__lo": dtype, "__hi": dtype}, name=f"{name}$range")
        joined = parent.cross_join(bounds)
        col = joined[f.name]
        inside = joined.filter(col >= joined["__lo"], col < joined["__hi"]).select(*parent.columns)
        on = [
            g.replace({agg.parent: inside.op()}).to_expr().identical_to(touched[f"k{j}"])  # type: ignore[union-attr]
            for j, g in enumerate(groups)
        ]
        return Ranged(i, width, over(inside.semi_join(touched, on)))
    return None
