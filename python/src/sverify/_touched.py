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
    keys: str | None
    """The distinct group keys `k0, k1, …` of the rows of table `<view>$in`
    (the input's columns); None for a window without PARTITION BY."""
    recompute: str | None
    """The view over the input rows whose keys are rows of `<view>$keys`;
    None for a window without PARTITION BY."""
    ranged: Ranged | None = None
    """With a time bucket among the keys: `recompute` that reads only the
    input rows in the touched buckets' time range."""
    framed: Framed | None = None
    """For windows with bounded RANGE frames over one time column: the rows
    near the change, recomputed. Tested, not proved."""


@dataclass(frozen=True)
class Framed:
    """Windows whose frames are bounded RANGE frames over the time column
    `ts` of the input, from `start` to `end` around each row (signed: a
    frame of 10 minutes preceding to the current row is `-10 min, 0`).

    A row inserted or deleted at time `t` lies in the frames of the output
    rows from `t - end` to `t - start`. So for a batch whose changed rows
    span `[t0, t1]`, `plan` recomputes the output rows of the touched
    partitions with time in `[t0 - end, t1 - start]` (`__olo`, `__ohi` of
    the one-row table `<view>$range`) from the input rows in that span
    widened by the frame (`__lo`, `__hi`), and these rows replace the
    state's rows of those partitions and times.

    That the other output rows keep their values rests on a window value
    depending only on the rows in its frame. Sverify tests it (equality with
    a full recompute on random streams); Lean does not prove it yet (#294),
    so the strategy is reported as tested, unlike the proved ones."""

    ts: str
    """The input's time column."""
    column: str
    """The view's column that is it unchanged."""
    start: timedelta
    end: timedelta
    plan: str


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
    hole = ibis.table(parent.schema(), name=f"{name}$hole").op()

    def view_over(narrowed: ir.Table) -> ir.Table:
        # Through a placeholder: `narrowed` holds the input itself.
        return query.op().replace({agg.parent: hole}).replace({hole: narrowed.op()}).to_expr()  # type: ignore[attr-defined]

    def over(narrowed: ir.Table) -> str:
        return written_plan(plan_json(None, view_over(narrowed)))  # type: ignore[arg-type]

    keys = recompute = ranged = touched = None
    if groups:
        rows = ibis.table(parent.schema(), name=f"{name}$in")
        k = rows.select(
            **{f"k{i}": g.replace({agg.parent: rows.op()}).to_expr() for i, g in enumerate(groups)}
        ).distinct()
        keys = written_plan(plan_json(None, k))  # type: ignore[arg-type]
        touched = ibis.table(k.schema(), name=f"{name}$keys")
        on = [g.to_expr().identical_to(touched[f"k{i}"]) for i, g in enumerate(groups)]  # type: ignore[union-attr]
        recompute = over(parent.semi_join(touched, on))
        ranged = _ranged(name, agg, groups, touched, over)
    framed = None
    if what == "partition" and (frame := _frame(agg)) is not None:
        f, start, end = frame
        col = next((names[n] for n, v in agg.values.items() if v == f and n in names), None)
        if col is not None:
            framed = _framed(name, agg, groups, touched, view_over, f, col, start, end)
    if recompute is None and framed is None:
        return "the windows have no PARTITION BY and no bounded RANGE frame over a time column"
    return Touched(
        columns=[names[g] for g in by],
        deltas=deltas,
        input_names=list(parent.columns),
        keys=keys,
        recompute=recompute,
        ranged=ranged,
        framed=framed,
    )


def _frame(proj: Any) -> tuple[ops.Field, timedelta, timedelta] | None:
    """The time column, start and end of the windows' frames, if each is a
    window aggregate over a bounded RANGE frame ordered by the same input
    timestamp column ascending."""
    from sverify.ibis_substrait.windows import _interval_offset
    from sverify.plan_json import Unsupported

    wins = [w for v in proj.values.values() for w in v.find(ops.WindowFunction, filter=_own_tree)]
    fields, starts, ends = set(), [], []
    for w in wins:
        if not isinstance(w.func, ops.Reduction) or w.how != "range" or len(w.order_by) != 1:
            return None
        key = w.order_by[0]
        if not key.ascending or not isinstance(key.expr, ops.Field):
            return None
        dtype: Any = key.expr.dtype
        if key.expr.rel != proj.parent or not dtype.is_timestamp():
            return None
        if w.start is None or w.end is None:
            return None
        try:
            s, e = (_interval_offset(b.value) for b in (w.start, w.end))
        except Unsupported:
            return None
        starts.append(timedelta(microseconds=-s if w.start.preceding else s))
        ends.append(timedelta(microseconds=-e if w.end.preceding else e))
        fields.add(key.expr)
    if len(fields) != 1:
        return None
    return fields.pop(), min(starts), max(ends)


def _framed(name, proj, groups, touched, view_over, f, col, start, end) -> Framed:
    """`Framed` for windows over the input's time column `f`."""
    from sverify.engine import plan_json, written_plan

    parent = proj.parent.to_expr()
    dtype = f.dtype
    bounds = ibis.table(
        {"__lo": dtype, "__hi": dtype, "__olo": dtype, "__ohi": dtype}, name=f"{name}$range"
    )
    j = parent.cross_join(bounds)
    inside = j.filter(j[f.name] >= j["__lo"], j[f.name] <= j["__hi"]).select(*parent.columns)
    if groups:
        on = [
            g.replace({proj.parent: inside.op()}).to_expr().identical_to(touched[f"k{i}"])
            for i, g in enumerate(groups)
        ]
        inside = inside.semi_join(touched, on)
    q = view_over(inside)
    jq = q.cross_join(bounds)
    out = jq.filter(jq[col] >= jq["__olo"], jq[col] <= jq["__ohi"]).select(*q.columns)
    return Framed(f.name, col, start, end, written_plan(plan_json(None, out)))  # type: ignore[arg-type]


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
    if len(parts) != 1:
        return "the window functions do not share one PARTITION BY"
    part = next(iter(parts))
    if not part and _frame(proj) is None:
        return "the windows have no PARTITION BY and no bounded RANGE frame over a time column"
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
