"""Conditions on a whole table and their checks on data: `unique`, `key`,
`references`, `arrives_within`, `max_rows`, `rows_per`, `approx`, how a
condition reads (`label`, `resolve`), and what a check established
(`CheckedCondition`, `Discharged`, `PreconditionError`).

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release. The
layers are in `docs/layers.md`.
"""

from __future__ import annotations

import math
import re
import warnings
from collections import Counter
from collections.abc import Callable, Sequence
from dataclasses import dataclass, field
from datetime import timedelta
from typing import TYPE_CHECKING, Any, ClassVar

import ibis
import ibis.expr.operations as ops
import ibis.expr.types as ir
from ibis.common.deferred import Deferred

from sverify import observation as _observation
from sverify._duration import Duration, duration
from sverify._unsupported import SverifyError
from sverify.counterexample import Counterexample
from sverify.observation import Observation

if TYPE_CHECKING:
    import pyarrow as pa

    from sverify.report import Condition, UnprovedReason


def q(name: str) -> str:
    """Quote a SQL identifier."""
    return '"' + name.replace('"', '""') + '"'


_Rows = Callable[[str], list[dict]]
"""The rows of a table, by name."""


_KeyResult = Callable[[], tuple[bool, Counterexample | None]]
"""The checker's next key result, and its counterexample."""


class TableCondition:
    """A condition on a whole table or its batches, not on each row: `Unique`,
    `References`, `ArrivesWithin`, `MaxRows` and `RowsPer`. Each kind carries
    its label, how it is counted on data, its entry in the checker's contract
    and how a source's batch checks it."""

    entry: ClassVar[str | None] = None
    """The checker contract's entry for it in `requires` (None: none)."""
    on_state: ClassVar[bool] = False
    """A view checks it on its whole new state, not on the rows it inserts."""
    batched: ClassVar[bool] = False
    """A source's batch checks it by `check_batch` (or against the
    watermark), not as a row condition on the inserted rows."""

    @property
    def label(self) -> str:
        raise NotImplementedError

    def violations(self, table: ir.Table) -> int:
        """How many rows of the bound `table` break it."""
        raise NotImplementedError

    def violating(self, rows: list[dict], key: Callable[[Any], Any], other: _Rows) -> list[dict]:
        """The `rows` that break it, with values compared by `key`, and
        `other` the rows of another table."""
        raise NotImplementedError

    def plan_entry(self, t: str, names: Callable[[str], Sequence[str]]) -> Any:
        """Its value in the checker contract's `entry` for table `t`, by
        column positions; `names` gives a table's column names."""
        return None

    def per_key(self) -> tuple[tuple[str, ...], int] | None:
        """At most so many rows per combination of these columns, if it says so."""
        return None

    def capped_by(self, rows: int) -> bool:
        """A table of at most `rows` rows meets it."""
        return False

    def ensured(self, out: dict, key: _KeyResult) -> CheckedCondition:
        """What the checker's output `out` proved of it as a postcondition;
        `key` gives the next key result and its counterexample."""
        raise NotImplementedError

    def check_batch(self, t: str, inserts: pa.Table, new: pa.Table | Any) -> Discharged | None:
        """Check it on a batch of source `t` that inserts `inserts`, against
        the `new` table, raising `PreconditionError`; None if the batch is
        checked elsewhere."""
        return None


def _positions(cols: Sequence[str], names: Sequence[str]) -> list[int]:
    missing = [c for c in cols if c not in names]
    if missing:
        raise ValueError(f"unique() names unknown columns: {missing}")
    return [list(names).index(c) for c in cols]


def _count(count: ir.Scalar) -> int:
    """The value of an Ibis count, fetched through Arrow: Ibis 12 converts
    `execute()`'s scalar through pandas, which warns under pandas 3.1
    (#479)."""
    return int(count.to_pyarrow().as_py())


@dataclass(frozen=True)
class Unique(TableCondition):
    """No two rows agree on these columns (see `unique`).

    Attributes:
        cols: The key's column names, in the order given to `unique`.
    """

    cols: tuple[str, ...]

    entry: ClassVar[str | None] = "keys"
    on_state: ClassVar[bool] = True
    batched: ClassVar[bool] = True

    @property
    def label(self) -> str:
        return f"unique({', '.join(self.cols)})"

    def violations(self, table: ir.Table) -> int:
        total: Any = table.count()
        distinct: Any = table.select(*self.cols).distinct().count()
        return _count(total) - _count(distinct)

    def violating(self, rows: list[dict], key: Callable[[Any], Any], other: _Rows) -> list[dict]:
        keys = Counter(key(tuple(r[c] for c in self.cols)) for r in rows)
        return [r for r in rows if keys[key(tuple(r[c] for c in self.cols))] > 1]

    def plan_entry(self, t: str, names: Callable[[str], Sequence[str]]) -> Any:
        return _positions(self.cols, names(t))

    def per_key(self) -> tuple[tuple[str, ...], int] | None:
        return self.cols, 1

    def ensured(self, out: dict, key: _KeyResult) -> CheckedCondition:
        ok, cex = key()
        value = "a key" if ok else "not shown to be a key"
        return CheckedCondition(self.label, ok, value, cex)

    def check_batch(self, t: str, inserts: pa.Table, new: pa.Table | Any) -> Discharged | None:
        from sverify._weighted import duplicate_keys

        if inserts.num_rows and (clash := duplicate_keys(new, self.cols, inserts)):
            raise PreconditionError(
                f"{clash} inserted key(s) of {t} violate {self.label}",
                source=t,
                condition=self,
                rows=_duplicate_rows(inserts, new, self.cols),
            )
        return Discharged(t, self.label, ON_DATA)


def unique(*cols: str) -> Unique:
    """A key: at most one row per combination of `cols`.

    In `requires` it is an assumption about an input (checked on the data when
    the input is bound to a backend); in `ensures` it is proved by
    `Rel.keys_sound` from the input keys and the transformation.

    Args:
        *cols: The names of the key's columns.

    Returns:
        A `Unique` condition, for `requires` or `ensures`.
    """
    return Unique(tuple(cols))


@dataclass(frozen=True)
class Key:
    """A key whose columns are never NULL (see `key`): `unique(*cols)` and
    `"col" IS NOT NULL` for each column, which it stands for in `requires`
    and `ensures`.

    Attributes:
        cols: The key's column names, in the order given to `key`.
    """

    cols: tuple[str, ...]

    @property
    def conditions(self) -> list[Condition]:
        """The conditions it stands for: the `unique` key, then each
        column's NOT NULL, as SQL."""
        quoted = ['"' + c.replace('"', '""') + '"' for c in self.cols]
        return [Unique(self.cols), *(f"{q} IS NOT NULL" for q in quoted)]


def key(*cols: str) -> Key:
    """A primary key: at most one row per combination of `cols`, and no NULL
    in any of them. `sv.key("id")` is `sv.unique("id")` and `'"id" IS NOT
    NULL'`, which it stands for in the contract and the report.

    Args:
        *cols: The names of the key's columns.

    Returns:
        A `Key`, for `requires` or `ensures`.
    """
    if not cols:
        raise ValueError("key() needs at least one column")
    return Key(tuple(cols))


def expand_keys(conds: Sequence[Condition]) -> list[Condition]:
    """`conds` with each `key` replaced by the conditions it stands for."""
    out: list[Condition] = []
    for c in conds:
        out += c.conditions if isinstance(c, Key) else [c]
    return out


@dataclass(frozen=True)
class References(TableCondition):
    """A foreign key: every non-NULL value of `col` occurs in column `other`
    of table `table` (see `references`).

    Attributes:
        col: The referencing column, in the table the condition is on.
        table: The name of the referenced table.
        other: The referenced column of `table`.
    """

    col: str
    table: str
    other: str

    entry: ClassVar[str | None] = "references"

    @property
    def label(self) -> str:
        return f"references({self.col}, {self.table}.{self.other})"

    def violations(self, table: ir.Table) -> int:
        other = ibis.get_backend(table).table(self.table)
        present = table.filter(table[self.col].notnull())
        missing: Any = present.anti_join(other, [present[self.col] == other[self.other]]).count()
        return _count(missing)

    def violating(self, rows: list[dict], key: Callable[[Any], Any], other: _Rows) -> list[dict]:
        present = {key(r[self.other]) for r in other(self.table)}
        return [r for r in rows if r[self.col] is not None and key(r[self.col]) not in present]

    def plan_entry(self, t: str, names: Callable[[str], Sequence[str]]) -> Any:
        try:
            other = names(self.table)
        except KeyError:
            raise ValueError(f"references() names an unknown table: {self.table!r}") from None
        [col] = _positions([self.col], names(t))
        [ref] = _positions([self.other], other)
        return [col, self.table, ref]

    def ensured(self, out: dict, key: _KeyResult) -> CheckedCondition:
        return CheckedCondition(self.label, False, "foreign keys are not proved")


def references(col: str, *, to: ir.Column | tuple[str, str] | None = None) -> References:
    """A foreign key: every non-NULL value of `col` occurs in the column `to`
    of another table.

    Only for `requires`, where it is checked on the data like `unique` (the
    referenced table must be bound to the same backend). With a key on the
    referenced column it lets `Rel.optimize` turn a left join on it into an
    inner join (`Report.optimized`). Not supported by incremental views.

    Args:
        col: The referencing column of the input the condition is on.
        to: The referenced column, keyword-only: an Ibis column of a named
            table (`customers.id`), or a `(table, column)` pair of names as
            `verify` and the backend know them.

    Returns:
        A `References` condition, for `requires`.

    Raises:
        TypeError: `to` is missing, or is not a column of a named table.

    Examples:
        ```python
        sv.references("customer_id", to=customers.id)
        sv.references("customer_id", to=("customers", "id"))
        ```
    """
    if to is None:
        raise TypeError(
            f"references({col!r}) needs the referenced column: to=customers.id or "
            "to=('customers', 'id')"
        )
    elif isinstance(to, ir.Column):
        op = to.op()
        if not (isinstance(op, ops.Field) and isinstance(op.rel, ops.PhysicalTable)):
            raise TypeError(
                "references(to=...) takes a column of a named table, such as customers.id"
            )
        table, other = op.rel.name, op.name
    else:
        table, other = to
    return References(col, table, other)


@dataclass(frozen=True)
class ArrivesWithin(TableCondition):
    """Rows arrive at most `lateness` late on `col` (see `arrives_within`).

    Attributes:
        col: The time column, a timestamp.
        lateness: How far behind the latest `col` seen a changed row may be.
    """

    col: str
    lateness: timedelta

    batched: ClassVar[bool] = True

    @property
    def label(self) -> str:
        return f"arrives_within({self.col}, {show_duration(self.lateness)})"

    def violations(self, table: ir.Table) -> int:
        # On one snapshot, only the NULLs break it; batches are checked by
        # the pipeline against the watermark.
        nulls: Any = table.filter(table[self.col].isnull()).count()
        return _count(nulls)

    def violating(self, rows: list[dict], key: Callable[[Any], Any], other: _Rows) -> list[dict]:
        return [r for r in rows if r[self.col] is None]

    def ensured(self, out: dict, key: _KeyResult) -> CheckedCondition:
        return CheckedCondition(self.label, False, "lateness is checked on a source's batches")


def arrives_within(
    col: str,
    within: Duration | None = None,
    *,
    days: float | None = None,
    hours: float | None = None,
    minutes: float | None = None,
    seconds: float | None = None,
) -> ArrivesWithin:
    """A bound on lateness: every row a batch inserts or deletes has `col` at
    most this far behind the largest `col` seen before the batch.

    Only for `requires` on a source. The first refresh checks that `col` has
    no NULLs, and every later batch is checked against the watermark, the
    largest `col` seen minus the lateness: a row before it, or a NULL, breaks
    the precondition and the batch is rejected (`PreconditionError`), so
    nothing is applied. An incremental node that aggregates by a time bucket
    of `col` (`ts.truncate("h")`, `ts.bucket(...)`) then drops the buckets
    that end at or before the watermark from its state, since no admissible
    batch changes them (`Retention.final_unchanged` in
    `SubstraitLean/Retention.lean`), and keeps at most
    `⌈lateness / width⌉ + 1` buckets (`Retention.open_buckets_le`).

    Args:
        col: The time column of the input, a timestamp.
        within: The lateness, a `timedelta` or an ISO 8601 duration:
            `arrives_within("ts", "PT15M")`.
        days: Deprecated: write `within`.
        hours: Deprecated: write `within`.
        minutes: Deprecated: write `within`.
        seconds: Deprecated: write `within`.

    Returns:
        An `ArrivesWithin` condition, for `requires`.

    Raises:
        ValueError: The lateness is negative.
    """
    given = {"days": days, "hours": hours, "minutes": minutes, "seconds": seconds}
    units = {k: v for k, v in given.items() if v is not None}
    if units:
        if within is not None:
            raise TypeError("arrives_within takes within= or the units, not both")
        warnings.warn(
            "arrives_within(col, days=, hours=, minutes=, seconds=) is deprecated; write "
            'arrives_within(col, within), a timedelta or an ISO 8601 duration ("PT15M")',
            DeprecationWarning,
            stacklevel=2,
        )
        lateness = timedelta(**units)
    elif within is None:
        raise TypeError('arrives_within needs the lateness: arrives_within(col, "PT15M")')
    else:
        lateness = duration(within, "arrives_within's lateness")
    if lateness < timedelta(0):
        raise ValueError(f"arrives_within needs a lateness of 0 or more, not {lateness}")
    return ArrivesWithin(col, lateness)


@dataclass(frozen=True)
class MaxRows(TableCondition):
    """At most `n` rows (see `max_rows`).

    Attributes:
        n: The cap.
    """

    n: int

    entry: ClassVar[str | None] = "max_rows"
    on_state: ClassVar[bool] = True
    batched: ClassVar[bool] = True

    @property
    def label(self) -> str:
        return f"max_rows({self.n})"

    def violations(self, table: ir.Table) -> int:
        rows: Any = table.count()
        return max(0, _count(rows) - self.n)

    def violating(self, rows: list[dict], key: Callable[[Any], Any], other: _Rows) -> list[dict]:
        return rows[self.n :]

    def plan_entry(self, t: str, names: Callable[[str], Sequence[str]]) -> Any:
        return self.n

    def capped_by(self, rows: int) -> bool:
        return rows <= self.n

    def ensured(self, out: dict, key: _KeyResult) -> CheckedCondition:
        n = out.get("rows")
        value = "no bound on the rows" if n is None else f"at most {n:,} rows"
        return CheckedCondition(self.label, n is not None and n <= self.n, value)

    def check_batch(self, t: str, inserts: pa.Table, new: pa.Table | Any) -> Discharged | None:
        from sverify._weighted import row_count

        if (n := row_count(new)) > self.n:
            raise PreconditionError(
                f"{n - self.n} row(s) of {t} violate {self.label}", source=t, condition=self
            )
        return Discharged(t, self.label, ON_DATA)


def max_rows(n: int) -> MaxRows:
    """A cap on an input's row count: at most `n` rows.

    In `requires` it is checked on the data (`COUNT(*) <= n`) like `unique`,
    or proved from the record counts of a Delta or Iceberg table's files; an
    incremental view checks it on every batch. Lean carries the caps through
    the plan (`Rel.maxRows`, and a join on a `unique` key of its right side
    keeps the left side's rows, `Rel.capJoins`), and `Report.rows` bounds
    the output. In `ensures` it is proved from them.

    With a cap, an integer `SUM` of values in `[-m, m]` over at most `n`
    rows, with `n · m < 2⁶³`, is proved to fit 64 bits (#219), and needs no
    check on the data. Error bounds of floating-point aggregates grow with
    the number of rows, so `SUM` and `AVG` of doubles get their bounds only
    from inputs with a cap: a sum of at most `n` values in `[lo, hi]` lies
    within the proved tolerance of `[min(lo, n·lo), max(hi, n·hi)]`, and
    their mean within it of `[lo, hi]` (#85, `docs/float-bounds.md`). Caps of
    up to `2³²` rows give bounds.

    Args:
        n: The largest number of rows the input may have.

    Returns:
        A `MaxRows` condition, for `requires` or `ensures`.

    Raises:
        ValueError: `n` is negative.
    """
    if n < 0:
        raise ValueError(f"max_rows needs a cap of 0 or more, not {n}")
    return MaxRows(int(n))


@dataclass(frozen=True)
class RowsPer(TableCondition):
    """At most `n` rows per combination of `cols` (see `rows_per`).

    Attributes:
        cols: The key's column names, in the order given to `rows_per`.
        n: The bound.
    """

    cols: tuple[str, ...]
    n: int

    entry: ClassVar[str | None] = "rows_per"

    @property
    def label(self) -> str:
        return f"rows_per({''.join(c + ', ' for c in self.cols)}at_most={self.n})"

    def violations(self, table: ir.Table) -> int:
        if not self.cols:
            everything: Any = table.count()
            return max(0, _count(everything) - self.n)
        # Rows beyond the bound in each key's group.
        sizes = table.group_by(list(self.cols)).aggregate(rows=ibis._.count())
        big = sizes.filter(sizes.rows > self.n)
        over: Any = (big.rows - self.n).sum()
        # A sum over no groups is NULL.
        return int(over.to_pyarrow().as_py() or 0)

    def violating(self, rows: list[dict], key: Callable[[Any], Any], other: _Rows) -> list[dict]:
        # The rows beyond the first `n` of each key.
        seen: Counter[object] = Counter()
        over = []
        for r in rows:
            k = key(tuple(r[c] for c in self.cols))
            seen[k] += 1
            if seen[k] > self.n:
                over.append(r)
        return over

    def plan_entry(self, t: str, names: Callable[[str], Sequence[str]]) -> Any:
        return [_positions(self.cols, names(t)), self.n]

    def per_key(self) -> tuple[tuple[str, ...], int] | None:
        return self.cols, self.n

    def capped_by(self, rows: int) -> bool:
        return rows <= self.n

    def ensured(self, out: dict, key: _KeyResult) -> CheckedCondition:
        return CheckedCondition(self.label, False, "rows per key are checked on inputs only")


def rows_per(*cols: str | Sequence[str], at_most: int | None = None) -> RowsPer:
    """A bound on the rows per key: at most `at_most` rows agree on `cols`,
    `rows_per("customer", "day", at_most=3)`.

    In `requires` it is checked on the data like `unique` (a `GROUP BY` of
    `cols`, with NULLs in one group), or proved from a row-count fact of a
    Delta or Iceberg table with at most `at_most` rows. `unique(*cols)` is
    `rows_per(*cols, at_most=1)`.

    Lean carries the bounds through the plan (`Rel.perKey`): filters, sorts,
    `DISTINCT`, semi-joins, projections and unions keep them, and so does a
    join on a `unique` key of its right side, which gives each left row at
    most one partner. An aggregate grouping by all of `cols` then has groups
    of at most `at_most` rows (`Rel.groupRows_sound`). So an integer or
    decimal `SUM` of values in `[-m, m]` per group is proved to fit its type
    when `at_most · m` does (#219), where a cap on the whole table
    (`max_rows`) would have to bound every group at once. `Report.relations`
    lists the bounds per relation.

    Incremental views do not check it on batches yet, and refuse it.

    Args:
        cols: The names of the key's columns.
        at_most: The most rows that may agree on them.

    Returns:
        A `RowsPer` condition, for `requires`.

    Raises:
        ValueError: A column is not a name, or `at_most` is missing or
            negative.
    """
    if len(cols) in (1, 2) and not isinstance(cols[0], str):
        # 0.x: rows_per(["a", "b"], 3) or rows_per(["a", "b"], at_most=3).
        warnings.warn(
            "rows_per(cols, at_most) is deprecated; write rows_per(*cols, at_most=...)",
            DeprecationWarning,
            stacklevel=2,
        )
        if len(cols) == 2:
            if at_most is not None:
                raise TypeError("rows_per got at_most twice")
            at_most = int(cols[1])  # type: ignore[arg-type]
        cols = tuple(cols[0])
    if not all(isinstance(c, str) for c in cols):
        raise ValueError("rows_per takes the key's column names, rows_per('a', 'b', at_most=3)")
    if at_most is None:
        raise ValueError("rows_per needs at_most=, the most rows that may share the key")
    if at_most < 0:
        raise ValueError(f"rows_per needs a bound of 0 or more, not {at_most}")
    return RowsPer(tuple(cols), int(at_most))  # type: ignore[arg-type]


@dataclass(frozen=True)
class RelationRows:
    """What the checker bounds a relation of the transformation's plan by (see
    `Report.relations`)."""

    op: str
    """The operator, such as "filter", "join" or "read orders"."""
    depth: int
    """How deep in the plan it is: 0 for the result, 1 for its input, …"""
    rows: int | None
    """At most this many rows (`Rel.maxRows_sound`); None if unbounded."""
    group_rows: int | None = None
    """For an aggregate, at most this many rows per group, from `rows_per`,
    `unique` or `max_rows` (`Rel.groupRows_sound`)."""


@dataclass(frozen=True)
class Approx(_observation.Tolerant):
    """A condition relaxed by a tolerance (see `approx`).

    Attributes:
        cond: The condition, an Ibis expression or a function of the table.
        rel: The relative tolerance, or None.
        abs: The absolute tolerance, or None.
        ulps: The tolerance in units in the last place, or None.
    """

    cond: Any
    rel: float | None = 1e-6
    abs: float | None = None
    ulps: int | None = None

    def __call__(self, table: ir.Table) -> ir.BooleanValue:
        return _relax(resolve(self.cond, table), self.slack)

    def slack(self, k: float) -> float:
        """How far a comparison with `k` moves: the largest of `abs`,
        `rel · max(1, |k|)` and `ulps` units in the last place of `k`."""
        out = 0.0
        if self.abs is not None:
            out = max(out, self.abs)
        if self.rel is not None:
            out = max(out, self.rel * max(1.0, abs(k)))
        if self.ulps is not None:
            out = max(out, self.ulps * math.ulp(k))
        return out


def _relax(expr: ir.BooleanValue, tolerance: Callable[[float], float]) -> ir.BooleanValue:
    """`expr` with each comparison against a number `k` moved outward by
    `tolerance(k)`."""
    import ibis.expr.operations as ops

    def slack(k: Any) -> float:
        return tolerance(float(k))

    def number(node: Any) -> Any:
        if isinstance(node, ops.Literal) and node.dtype.is_numeric():
            return node.value
        return None

    def go(node: Any) -> ir.BooleanValue:
        if isinstance(node, ops.And):
            return go(node.left) & go(node.right)
        if isinstance(node, ops.Or):
            return go(node.left) | go(node.right)
        if isinstance(node, ops.Between):
            lo, hi = number(node.lower_bound), number(node.upper_bound)
            if lo is not None and hi is not None:
                return node.arg.to_expr().between(lo - slack(lo), hi + slack(hi))
        up = (ops.Less, ops.LessEqual)
        down = (ops.Greater, ops.GreaterEqual)
        if isinstance(node, (*up, *down, ops.Equals)):
            x, k, flipped = node.left, number(node.right), False
            if k is None:
                x, k, flipped = node.right, number(node.left), True
            if k is not None:
                e = x.to_expr()
                d = slack(k)
                if isinstance(node, ops.Equals):
                    return e.between(k - d, k + d)
                # `k <= x` bounds `x` from below, as `x >= k` does.
                bound_above = isinstance(node, up) != flipped
                strict = isinstance(node, (ops.Less, ops.Greater))
                if bound_above:
                    return e < k + d if strict else e <= k + d
                return e > k - d if strict else e >= k - d
        what = (
            "it compares two columns"
            if isinstance(node, ops.Comparison)
            and not isinstance(node.left, ops.Literal)
            and not isinstance(node.right, ops.Literal)
            else f"it is a {node.__class__.__name__}"
        )
        raise TypeError(
            f"{what}; sv.approx relaxes comparisons of a column with a number, "
            "combined with & and |, such as sv.approx(_.mean >= 0)"
        )

    return go(expr.op())


def approx(
    cond: Any,
    rel: float | None = None,
    *,
    abs: float | None = None,  # noqa: A002 - the keyword of `within` and pytest.approx
    ulps: int | None = None,
) -> Approx:
    """A postcondition that holds up to rounding: every comparison of a column
    with a number `k` in `cond` is relaxed by the tolerance, with the
    keywords of `within`: the largest of `abs`, `rel · max(1, |k|)` and
    `ulps` units in the last place of `k`. With none of them, `rel=1e-6`.

    `_.avg <= 100` may fail by the last bits after `AVG` of doubles rounds;
    `approx(_.avg <= 100)` is `_.avg <= 100.0001`, which the checker proves
    from the error bounds of #85 when the inputs have a row cap
    (`max_rows`), and which runs as that condition at run time. The default
    `rel = 1e-6` covers the error of a `SUM` or `AVG` over any cap up to
    `2³²` rows, about `n · 2⁻⁵³` relative to the values' bound. Comparisons
    combine with AND and OR; `BETWEEN` and `=` widen on both sides.

    Args:
        cond: An Ibis condition (`_.avg <= 100`) or a function of the table.
        rel: The relative tolerance, `1e-6` when no tolerance is given.
        abs: The absolute tolerance.
        ulps: The tolerance in units in the last place of `k`.

    Returns:
        A condition for `ensures` (or `requires`).

    Raises:
        TypeError: `cond` is a SQL snippet.
        ValueError: A tolerance is negative.
    """
    if isinstance(cond, str):
        raise TypeError("approx takes an Ibis condition, not SQL; write the slack in the SQL")
    if any(t is not None and t < 0 for t in (rel, abs, ulps)):
        raise ValueError("approx's tolerances are 0 or more")
    if isinstance(cond, Deferred):
        _check_approx(cond)
    if rel is None and abs is None and ulps is None:
        rel = 1e-6
    return Approx(cond, rel, abs, ulps)


def _check_approx(cond: Deferred) -> None:
    """Whether `approx` can relax `cond`, checked when it is called (#687):
    `cond` is resolved on a table of doubles with the columns it names."""
    from ibis.common.deferred import Attr, Just

    names: list[str] = []

    def walk(r: Any) -> None:
        if isinstance(r, Deferred):
            r = r._resolver
        if isinstance(r, Attr) and isinstance(r.name, Just) and isinstance(r.name.value, str):
            names.append(r.name.value)
        for slot in getattr(r, "__slots__", ()):
            v = getattr(r, slot, None)
            for x in v if isinstance(v, tuple | list) else (v,):
                if hasattr(x, "__slots__"):
                    walk(x)

    walk(cond)
    try:
        table = ibis.table({n: "float64" for n in dict.fromkeys(names)}, name="t")
        expr = cond.resolve(table)
    except Exception:  # noqa: BLE001 - checked again when verified
        return
    try:
        _relax(expr, Approx(None).slack)
    except TypeError as e:
        raise TypeError(f"sv.approx({label(cond)}): {e}") from None


# The `value` of a postcondition sverify checks on data only.
_DATA_ONLY = frozenset(
    {
        "foreign keys are not proved",
        "lateness is checked on a source's batches",
        "rows per key are checked on inputs only",
    }
)


@dataclass
class CheckedCondition:
    """One postcondition in a `Report`, and what became of its proof."""

    label: str
    """The condition as written, e.g. "(_.amount >= 0)" or "unique(id)"."""
    proved: bool
    """Whether the checker proved it."""
    value: str
    """What the checker established about the condition, e.g. "TRUE or NULL"."""
    counterexample: Counterexample | None = None
    """For an unproved condition: inputs meeting the preconditions on which
    it fails, if the search (`sverify.counterexample`) found one."""
    checked: bool = False
    """For an unproved condition with `on_unproved="check"`: it is checked
    on the output data instead, on a bound result when it is built, or on a
    node at every refresh before its sink commits."""
    suggested: dict[str, list[Condition]] = field(default_factory=dict)
    """For an unproved condition: preconditions on the inputs, per table,
    under which the checker proves it (`_.x * 2 <= 100` holds with `_.x <= 50`).
    Never assumed: adding them is the author's choice."""
    ignores: tuple[str, ...] = ()
    """The components of the observation (`sv.equivalent`) the condition
    depends on but the observation ignores (D12, #444): the proof under the
    reference does not carry to an engine whose result is only equal up to
    the observation. Empty for a condition the observation keeps."""

    reads: tuple[str, ...] | None = None
    """The output columns the condition reads; None where that is not
    known (every column)."""
    robust: bool = field(default=False, repr=False, compare=False)
    """Proved on every value an engine's doubles may take: each double column
    the condition reads widened by its bound (`Report.epsilon`) and, for a
    sum, an average or a variance, kept to its sign
    (`EngineRobust.robust`, #1045). Such a condition needs no `sv.approx`."""
    checker_ignores: tuple[str, ...] | None = field(default=None, repr=False, compare=False)
    """What the checker reports the condition ignores (#1071), the same
    components as `ignores`, decided in Lean: None where the checker does not
    report them (a table condition, or a plan shape `Expr.depends` does not
    read)."""
    robust_on: tuple[str, ...] = field(default=(), repr=False, compare=False)
    """The engines where `robust` is a theorem: their sums keep the sign
    (`FloatBounds.StdModel.TreeSum.sign`). On the others it rests on the
    engine's facts, and a route there is tested."""
    allowed: bool = field(default=False, repr=False, compare=False)
    """Proved on every result the reference allows, not only on the orders
    `proved` covers (`contract_sound_allowed`, or `contract_sound_allowed_closed`
    for a plan without open measures, `SubstraitLean/AllowedNear.lean`): the
    plan has no open measure the condition reads (since D25 a double `SUM` or
    `AVG` is not one; a statistical aggregate still is)."""
    depends: tuple[str, ...] | None = field(default=None, repr=False, compare=False)
    """The components of an observation the condition's value depends on,
    as the checker computes them from the columns it reads (`Expr.depends`,
    `SubstraitLean/Robust.lean`): an observation that coarsens none of them
    keeps the condition TRUE (`Expr.robust_of_depends`). None where the
    checker does not know them."""
    approx: bool = False
    """The condition is `sv.approx(...)`: it allows for rounding."""
    nullable: tuple[str, ...] | None = None
    """Of the columns it reads, those the report says may be NULL; None
    where that is not known."""
    condition: Any = field(default=None, repr=False, compare=False)
    """The condition as it was given in `ensures` (a SQL string, an Ibis
    expression, `unique(...)`, …), to pair the result with it; None for a
    report not built by `verify` or a transform."""
    detail: str | None = None
    """Why it is not proved, in the user's terms, where the report found
    more than the checker's value says (`_key_reasons`, `_null_reasons`,
    #688): `why` reads it first."""
    ties: bool = False
    """Unproved only because rows may tie: the checker proves it where every
    window orders its rows totally (`Report.tie_places` names where they
    may not). The counterexample search is skipped for it (#691)."""

    @property
    def reason(self) -> UnprovedReason | None:
        """Why it is not proved, as a code a tool can act on; None when it
        is proved and independent of the observation (`portable`). `why`
        says the same in words.

        * `"observation"`: proved, but it depends on what the observation
          (`sv.equivalent`) ignores.
        * `"not_a_key"`: a `unique` the preconditions do not make a key.
        * `"ties"`: rows may tie in an ORDER BY, so the result is not
          determined.
        * `"always_false"`: it is FALSE on every row.
        * `"may_be_false"`: it may be FALSE on some rows (and maybe NULL).
        * `"may_be_null"`: it may be NULL on some rows, and is never FALSE.
        * `"not_proved_kind"`: a condition sverify checks on data only
          (`references`, `rows_per`, `arrives_within`).
        * `"unknown"`: Lean knows nothing that decides it.
        """
        if self.proved:
            return "observation" if self.ignores else None
        if self.value == "not shown to be a key":
            return "not_a_key"
        if self.ties or self.value.startswith("undetermined"):
            return "ties"
        parts = set(self.value.replace(" or ", ", ").split(", "))
        if parts == {"FALSE"}:
            return "always_false"
        if "FALSE" in parts:
            return "may_be_false"
        if "NULL" in parts:
            return "may_be_null"
        if self.value in _DATA_ONLY:
            return "not_proved_kind"
        return "unknown"

    @property
    def portable(self) -> bool:
        """Proved, and independent of what the observation ignores."""
        return self.proved and not self.ignores

    @property
    def why(self) -> str:
        """Why it is not proved, in words: what the checker found the condition may
        be on a row that meets the preconditions, and, where it may be NULL,
        how to rule that out."""
        if self.detail is not None:
            return self.detail
        if self.value == "not shown to be a key":
            return "the preconditions do not make it a key"
        if self.ties:
            return "it holds where no rows tie in a window's ORDER BY, and rows may tie there"
        parts = set(self.value.replace(" or ", ", ").split(", "))
        if "TRUE" not in parts and parts == {"FALSE"}:
            return "it is FALSE on every row"
        bad = [v for v in ("FALSE", "NULL") if v in parts]
        if not bad:
            return f"the checker only knows it is {self.value}"
        why = f"it may be {' or '.join(bad)} on some rows"
        if bad != ["NULL"]:
            # NULL is one way among others to fail: making a column NOT NULL
            # does not prove it.
            pass
        elif self.nullable is None:
            why += ", where a column it reads is NULL"
        elif self.nullable:
            why += f", where {', '.join(self.nullable)} is NULL"
        return why

    @property
    def message(self) -> str:
        """The condition's status in words, as `str(report)` prints it after
        "ensures <label>: ": "proved", or "NOT proved: " and `why`; then what
        the observation ignores that it depends on, and whether it is
        checked on the output data."""
        mark = "proved" if self.proved else f"NOT proved: {self.why}"
        if self.ignores:
            mark += f"; {_observation.why(self.ignores)}"
        if self.checked:
            mark += f"; {DATA_CHECK}"
        return mark


#: How a report marks a postcondition `on_unproved="check"` checks on data.
DATA_CHECK = "checked on the output data"


class PreconditionError(SverifyError):
    """Input data violates a precondition.

    Import it from `sverify.errors`. Raised when a contracted transformation
    is called on inputs bound to a backend, or a node is refreshed (on the
    full source tables the first time, then on each batch of changes), and a
    precondition does not hold on the rows. The message says how many rows
    violate which condition, for example
    "2 row(s) of orders violate (_.amount >= 0)".

    Attributes:
        source: The input or source table the condition is on (None when
            the error is about several, an assumed `SUM` among them).
        condition: The condition as stated in `requires` (an Ibis deferred,
            a SQL string, a `unique` key, ...) or as inferred, an `Inferred`
            whose text is its SQL; None as for `source`.
        rows: Up to `ROWS_SHOWN` (10) of the rows that break it, as an Arrow
            table with the input's columns; None where the condition is on
            the table as a whole (`max_rows`, `rows_per`) or the rows could
            not be fetched.
    """

    code = "precondition_failed"

    def __init__(
        self,
        message: str,
        *,
        source: str | None = None,
        condition: Condition | None = None,
        rows: pa.Table | None = None,
    ):
        super().__init__(message)
        self.source = source
        self.condition = condition
        self.rows = rows


class Inferred(str):
    """A bound inferred to rule out an overflow (#244): a SQL condition on one
    column of an input table, labelled as the Ibis code that states it
    (`(_.amount < 2**62)`). NULL passes, since only a value can overflow. It
    is checked, proved and reported like a precondition the user wrote."""

    text: str
    column: str | None = None
    """The input column it bounds (set by `_render_needs`)."""

    def __new__(cls, sql: str, text: str) -> Inferred:
        out = super().__new__(cls, sql)
        out.text = text
        return out

    def parts(self) -> tuple[str | None, str | None]:
        """The comparison and the SQL value of `col <op> <value>`, after an
        `IS NULL OR` that lets NULL pass: `("<", "9000000000000000000")`,
        `("IS NOT NULL", None)`; `(None, None)` where it is not of that form."""
        if self.column is None:
            return None, None
        col = '"' + self.column.replace('"', '""') + '"'
        rest = self.removeprefix(f"{col} IS NULL OR ")
        if rest == f"{col} IS NOT NULL":
            return "IS NOT NULL", None
        m = re.fullmatch(re.escape(col) + r" (>=|<=|<>|<|>) (.+)", rest)
        return (m[1], m[2]) if m else (None, None)


def label(cond: Condition) -> str:
    if isinstance(cond, Inferred):
        return cond.text
    if isinstance(cond, TableCondition):
        return cond.label
    if isinstance(cond, Approx):
        tol = (("rel", cond.rel), ("abs", cond.abs), ("ulps", cond.ulps))
        given = ", ".join(f"{k}={v:g}" for k, v in tol if v is not None)
        return f"approx({label(cond.cond)}, {given})"
    if isinstance(cond, Observation):
        return cond.label
    if isinstance(cond, str):
        return cond
    if isinstance(cond, Deferred):
        from sverify._user_text import deferred_text

        return deferred_text(cond)
    return getattr(cond, "__name__", repr(cond))


def show_duration(d: timedelta) -> str:
    """`d` in its largest whole unit: "2h", "90m", "1d", "1.5s"."""
    us = d // timedelta(microseconds=1)
    for unit, n in (("d", 86_400_000_000), ("h", 3_600_000_000), ("m", 60_000_000)):
        if us and us % n == 0:
            return f"{us // n}{unit}"
    return f"{us / 1_000_000:g}s"


def resolve(cond: Condition, table: ir.Table) -> ir.BooleanValue:
    if isinstance(cond, Deferred):
        return cond.resolve(table)
    if callable(cond):
        return cond(table)
    return cond  # type: ignore[return-value]


ROWS_SHOWN = 10
"""How many violating rows a `PreconditionError` carries (`.rows`)."""


def _duplicate_rows(
    inserts: pa.Table, new: pa.Table | Any, cols: Sequence[str], limit: int = ROWS_SHOWN
) -> pa.Table | None:
    """Up to `limit` inserted rows whose key `cols` occurs more than once in
    the `new` table (None if they cannot be fetched)."""
    try:
        from sverify._weighted import duplicate_key_rows

        return duplicate_key_rows(new, cols, inserts, limit)
    except Exception:
        return None


ON_DATA = "checked on data"


@dataclass(frozen=True)
class Discharged:
    """How a precondition on a table was established: proved from its
    `SCHEMA`, proved from facts of one metadata source, or `ON_DATA`."""

    table: str
    condition: str
    source: str
    inferred: bool = False
    """The condition is a bound inferred to rule out overflow (#244)."""

    def __str__(self) -> str:
        how = f"inferred, {self.source}" if self.inferred else self.source
        return f"{self.table}: {self.condition} ({how})"
