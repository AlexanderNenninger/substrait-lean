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

import ibis
import ibis.expr.types as ir

from sverify._retention import _aggregate, _bucket, _row_local

SQL = "the view is SQL; touched groups need an Ibis expression"
NOT_AGGREGATE = "not an aggregate under filters and projections of its rows"


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
    found = _aggregate(query.op())
    if found is None:
        return NOT_AGGREGATE
    agg, names = found
    if not agg.groups:
        return "the aggregate has no GROUP BY"
    if not _row_local(list(agg.groups.values()), agg.parent):
        return "a grouping key reads other rows"
    if missing := [g for g in agg.groups if g not in names]:
        return f"the view does not output the group key {missing[0]} unchanged"
    parent = agg.parent.to_expr()
    try:
        deltas = delta_plans(plan_json(None, parent))  # type: ignore[arg-type]
    except NotIncremental as e:
        return f"the aggregate's input has no delta rules ({e})"
    groups = list(agg.groups.values())
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
        columns=[names[g] for g in agg.groups],
        deltas=deltas,
        input_names=list(parent.columns),
        keys=written_plan(plan_json(None, keys)),  # type: ignore[arg-type]
        recompute=over(parent.semi_join(touched, on)),
        ranged=_ranged(name, agg, groups, touched, over),
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
