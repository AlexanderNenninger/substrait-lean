"""Retention: the final time buckets leave a view's state (#294).

Internal: not part of sverify's public API.

A source with `sv.arrives_within("ts", hours=2)` promises that every row a
batch inserts or deletes has `ts` at or after the watermark: the largest `ts`
seen before the batch, minus the lateness. The pipeline checks it on every
batch (`check_batch`) and rejects a batch with a late row.

A view that aggregates such a source by a time bucket of `ts` (`plan`
recognises it) then has final buckets: one that ends at or before the
watermark changes in no admissible batch. Lean proves it for the aggregate
(`Retention.final_unchanged`, `Retention.retention_sound` and
`Retention.final_stable` in `SubstraitLean/Retention.lean`), and that at most
`⌈lateness / width⌉ + 1` buckets are open (`Retention.open_buckets_le`).
Filters and projections under the aggregate keep each row's `ts`, and those
over it act on each output row, so they keep the result.

This module is trusted glue. It recognises the shape of the plan in the
Ibis expression; the pipeline then

* computes the view's change on the buckets after those it retired
  (`IncrementalView._diff`), which is the whole change, since the retired
  buckets are final;
* drops the rows of the final buckets from the state after every sink has
  written them (`Pipeline.retire`), so they stay in the sink.
"""

from __future__ import annotations

import math
from collections.abc import Callable, Mapping, Sequence
from dataclasses import dataclass
from datetime import UTC, datetime, timedelta
from typing import Any

import ibis.expr.operations as ops
import ibis.expr.types as ir
import pyarrow as pa
from ibis.common.graph import Node

from sverify._weighted import _call, negative, positive, rows_of
from sverify.contracts import ArrivesWithin, Condition, label, show_duration

# `date_trunc` to these units is a bucket from 1970-01-01 (`Retention.trunc_eq_bucket`).
_UNITS = {
    "SECOND": timedelta(seconds=1),
    "MINUTE": timedelta(minutes=1),
    "HOUR": timedelta(hours=1),
    "DAY": timedelta(days=1),
}

# Inside a view that retires buckets, these would read other rows than the row's own.
_NOT_ROW_LOCAL = (ops.WindowFunction, ops.Reduction, ops.Subquery)


@dataclass(frozen=True)
class Retention:
    """How a view retires its final buckets: its column `column` is the
    `width`-wide bucket, counted from `origin` after 1970-01-01, of column
    `ts` of source `table`, whose rows arrive at most `lateness` late."""

    table: str
    ts: str
    lateness: timedelta
    column: str
    width: timedelta
    origin: timedelta = timedelta(0)

    @property
    def bound(self) -> int:
        """At most this many buckets are open: `⌈lateness / width⌉ + 1`."""
        return math.ceil(self.lateness / self.width) + 1

    def watermark(self, latest: Any) -> Any:
        """The watermark when the largest `ts` seen is `latest` (None: no row
        yet, no watermark)."""
        return None if latest is None else latest - self.lateness

    def cutoff(self, latest: Any) -> Any:
        """The last bucket start that is final: a bucket starting at `b` is
        final when `b + width ≤ watermark`."""
        return None if latest is None else latest - self.lateness - self.width

    def start(self, t: Any) -> Any:
        """The start of the bucket of time `t`."""
        epoch = datetime(1970, 1, 1, tzinfo=None if t.tzinfo is None else UTC) + self.origin
        return epoch + (t - epoch) // self.width * self.width

    def final_before(self, latest: Any) -> Any:
        """Every time before this one is in a final bucket: the end of the
        last final bucket (None: no row yet)."""
        cutoff = self.cutoff(latest)
        return None if cutoff is None else self.start(cutoff) + self.width

    def __str__(self) -> str:
        origin = f" from +{show_duration(self.origin)}" if self.origin else ""
        return (
            f"{self.column}: {show_duration(self.width)} buckets{origin} of {self.table}.{self.ts}"
        )


def _own_tree(n: Node) -> bool:
    """Whether `find` walks into `n`: a value's own expression, never the
    relations its fields read (#394), whose reductions are other rows'."""
    return not isinstance(n, ops.Relation)


def _row_local(values: Sequence[ops.Value], parent: ops.Relation) -> bool:
    """Every value reads only the columns of its own row of `parent`."""
    for v in values:
        if v.find(_NOT_ROW_LOCAL, filter=_own_tree):
            return False
        if any(getattr(f, "rel", None) != parent for f in v.find(ops.Field, filter=_own_tree)):
            return False
    return True


def _base_column(rel: ops.Relation, name: str) -> tuple[str, str] | None:
    """The base table and column that column `name` of `rel` is, unchanged
    through filters and projections that read only their own row; None if
    `rel` is anything else."""
    match rel:
        case ops.DatabaseTable() | ops.UnboundTable():
            return rel.name, name
        case ops.Filter(parent=parent, predicates=preds) if _row_local(preds, parent):
            return _base_column(parent, name)
        case ops.Project(parent=parent, values=values) if _row_local(list(values.values()), parent):
            v = values.get(name)
            if isinstance(v, ops.Field):
                return _base_column(parent, v.name)
    return None


def _aggregate(op: ops.Relation) -> tuple[ops.Aggregate, dict[str, str]] | None:
    """The aggregate a view ends in, under filters, projections and sorts of
    its output rows, and for each column of the aggregate the view's column
    that is it unchanged."""
    found = _under(op, lambda o: isinstance(o, ops.Aggregate))
    return None if found is None else (found[0], found[1])  # type: ignore[return-value]


def _under(
    op: ops.Relation, top: Callable[[ops.Relation], bool]
) -> tuple[ops.Relation, dict[str, str]] | None:
    """The relation `top` picks that a view ends in, under filters,
    projections and sorts of its output rows, and for each of its columns
    the view's column that is it unchanged."""
    if top(op):
        return op, {n: n for n in op.schema.names}  # type: ignore[attr-defined]
    match op:
        case ops.Filter(parent=parent, predicates=preds) if _row_local(preds, parent):
            return _under(parent, top)
        case ops.Sort(parent=parent):
            return _under(parent, top)
        case ops.Project(parent=parent, values=values) if _row_local(list(values.values()), parent):
            inner = _under(parent, top)
            if inner is None:
                return None
            rel, names = inner
            out = {}
            for a, n in names.items():
                for name, v in values.items():
                    if isinstance(v, ops.Field) and v.name == n:
                        out[a] = name
                        break
            return rel, out
    return None


def _interval_us(op: ops.Value | None) -> int | None:
    """A constant interval of days or less, in microseconds (None: none)."""
    from sverify.ibis_substrait.temporal import _const_interval

    if op is None:
        return 0
    parts = _const_interval(op)
    if parts is None or parts[0]:
        return None
    return parts[1]


def _bucket(v: ops.Value) -> tuple[ops.Field, timedelta, timedelta] | str:
    """The column, width and origin of a bucket expression, or why it is not
    one with a fixed width."""
    match v:
        case ops.TimestampTruncate(arg=ops.Field() as f, unit=unit):
            width = _UNITS.get(unit.name)
            if width is None:
                return f"buckets of a {unit.name.lower()} have no fixed width"
            return f, width, timedelta(0)
        case ops.TimestampBucket(arg=ops.Field() as f, interval=interval, offset=offset):
            k, o = _interval_us(interval), _interval_us(offset)
            if k is None or o is None or k <= 0:
                return "bucket() needs a constant interval of days or less"
            return f, timedelta(microseconds=k), timedelta(microseconds=o)
    return "not a time bucket"


def plan(
    query: ir.Table | str, requires: Mapping[str, Sequence[Condition]]
) -> Retention | str | None:
    """How the view of `query` retires buckets, given the preconditions on the
    sources it reads; why it cannot, if a source it reads has a lateness
    bound; None otherwise."""
    lateness = {
        (t, c.col): c for t, cs in requires.items() for c in cs if isinstance(c, ArrivesWithin)
    }
    if not lateness:
        return None
    if isinstance(query, str):
        return "the view is SQL; retention needs an Ibis expression"
    found = _aggregate(query.op())
    if found is None:
        return "the view is not an aggregate (under filters and projections)"
    agg, names = found
    if not agg.groups:
        return "the aggregate has no GROUP BY"
    if not _row_local(list(agg.groups.values()), agg.parent):
        return "a grouping key reads other rows"
    reasons = []
    for name, v in agg.groups.items():
        b = _bucket(v)
        if isinstance(b, str):
            if b != "not a time bucket":
                reasons.append(f"{name}: {b}")
            continue
        f, width, origin = b
        base = _base_column(f.rel, f.name) if f.rel == agg.parent else None
        cond = lateness.get(base) if base is not None else None
        if base is None or cond is None:
            reasons.append(f"{name} is not a bucket of a column with arrives_within")
            continue
        table, col = base
        dtype: Any = f.dtype
        if not dtype.is_timestamp():
            reasons.append(f"{table}.{col} is not a timestamp")
            continue
        if dtype.timezone not in (None, "UTC", "Etc/UTC") and width >= timedelta(hours=1):
            reasons.append(f"{table}.{col} has time zone {dtype.timezone}")
            continue
        if name not in names:
            reasons.append(f"the view does not output {name} unchanged")
            continue
        if _base_column(agg.parent, f.name) is None:
            reasons.append("the aggregate reads more than one source row per row")
            continue
        return Retention(table, col, cond.lateness, names[name], width, origin)
    conds = ", ".join(label(c) for c in lateness.values())
    return "; ".join(reasons) or f"no GROUP BY key is a fixed-width time bucket of {conds}"


# -- the lateness precondition on batches --------------------------------------


def _scalar(value: Any, dtype: pa.DataType) -> pa.Scalar:
    return pa.scalar(value, type=dtype)


def latest_of(column: pa.ChunkedArray | pa.Array) -> Any:
    """The largest value of a column, None if it has no value."""
    if not len(column):
        return None
    return _call("max", column).as_py()


@dataclass(frozen=True)
class Late:
    """Rows of a batch that break `arrives_within`."""

    late: int
    """Inserted rows before the watermark."""
    open: int
    """Deleted rows before the watermark whose bucket a view still holds."""
    nulls: int
    watermark: Any


def _before(rows: pa.Table, col: str, t: Any) -> int:
    """How many rows have `col` before `t`."""
    c = rows.column(col)
    if not len(c):
        return 0
    return _call("sum", _call("less", c, _scalar(t, c.type))).as_py() or 0


def late_rows(change: pa.Table, col: str, watermark: Any, limit: int) -> pa.Table:
    """Up to `limit` rows a batch (a weighted table) inserts with `col` NULL
    (`watermark` None) or before `watermark`."""
    inserted = rows_of(positive(change))
    c = inserted.column(col)
    bad = _call("is_null", c) if watermark is None else _call("less", c, _scalar(watermark, c.type))
    return inserted.filter(bad).slice(0, limit)


def check_batch(
    change: pa.Table, cond: ArrivesWithin, latest: Any, final_before: Any = None
) -> tuple[Late | None, int, Any]:
    """Check a batch (a weighted table, inserts and deletes) against the
    watermark of `latest`. A row it inserts before the watermark is late. A
    row it deletes before the watermark is an expiry, the source's own
    retention, if its time is before `final_before` (None: the watermark):
    every view that retires buckets of the column holds it in a final
    bucket. Returns the rows that break the condition, if any; how many
    rows expired; and the largest `ts` seen after the batch."""
    inserted, deleted = rows_of(positive(change)), rows_of(negative(change))
    nulls = inserted.column(cond.col).null_count + deleted.column(cond.col).null_count
    watermark = None if latest is None else latest - cond.lateness
    late = open_ = expired = 0
    if watermark is not None:
        late = _before(inserted, cond.col, watermark)
        limit = watermark if final_before is None else min(final_before, watermark)
        expired = _before(deleted, cond.col, limit)
        open_ = _before(deleted, cond.col, watermark) - expired
    found = Late(late, open_, nulls, watermark) if late or open_ or nulls else None
    batch_latest = latest_of(inserted.column(cond.col))
    if latest is None or (batch_latest is not None and batch_latest > latest):
        latest = batch_latest
    return found, expired, latest


def show_time(v: Any) -> str:
    return v.isoformat(sep=" ") if isinstance(v, datetime) else str(v)


# -- the state ------------------------------------------------------------------


def after(table: pa.Table, column: str, cutoff: Any) -> pa.Table:
    """The rows of `table` whose bucket `column` starts after `cutoff`."""
    col = table.column(column)
    return table.filter(_call("greater", col, _scalar(cutoff, col.type)))


def through(table: pa.Table, column: str, cutoff: Any) -> pa.Table:
    """The rows of `table` whose bucket starts at or before `cutoff`."""
    col = table.column(column)
    return table.filter(_call("less_equal", col, _scalar(cutoff, col.type)))


def buckets(table: pa.Table, column: str) -> int:
    """How many distinct buckets `table` has."""
    return _call("count_distinct", table.column(column)).as_py() if table.num_rows else 0


@dataclass
class RetentionReport:
    """What retention did to one view in a refresh: `str()` gives one line."""

    view: str
    """The view's name."""
    column: str
    """Its bucket column."""
    open: int
    """Buckets in the state after the refresh."""
    retired: int
    """Buckets dropped from the state in this refresh (they stay in the sink)."""
    bound: int
    """At most this many buckets are open: `⌈lateness / width⌉ + 1`."""
    watermark: Any
    """The largest time seen minus the lateness; None before the first row."""
    rows: int = 0
    """Rows in the state after the refresh."""
    waiting: str | None = None
    """Why final buckets were kept this time (a sink has not written them)."""
    off: str | None = None
    """Why the view keeps every bucket, if it does."""

    def __str__(self) -> str:
        if self.off is not None:
            return f"retention {self.view}: off ({self.off})"
        wm = "none yet" if self.watermark is None else show_time(self.watermark)
        line = (
            f"retention {self.view}.{self.column}: {self.open} bucket(s) open "
            f"(bound {self.bound}), {self.retired} retired, {self.rows} state row(s); "
            f"watermark {wm}"
        )
        if self.waiting:
            line += f"; final buckets kept until {self.waiting}"
        return line
