"""Pre- and postconditions for transformations, with postconditions proved in Lean.

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release.

    from ibis import _
    import sverify as sv

    @sv.transform(
        requires={"orders": [_.amount >= 0, _.id.notnull()]},
        ensures=[_.doubled >= 0, _.doubled.notnull(), "id IS NOT NULL"],
    )
    def doubled(orders):
        return orders.filter(orders.amount > 10).select(orders.id, doubled=orders.amount * 2)

Calling `doubled(orders)` builds the Ibis expression as usual. Before it is
returned, `substrait-check --contract` tries to *prove* every postcondition
from the preconditions, the column types and the transformation itself
(`contract_sound` in `SubstraitLean/Contracts.lean`). An unproved
postcondition raises `VerificationError` that says what the checker could establish,
unless `on_unproved` asks for a runtime check or a warning instead.

Preconditions are assumptions about data that comes from outside, so when the
inputs are bound to a backend they are checked on the data at call time.

Contracted transformations compose. When the result of one feeds another, the
downstream precondition is *proved* from the upstream contract instead of
checked on the data, and the downstream postconditions are proved assuming
only what the upstream one guarantees (`Triple.compose` in
`SubstraitLean/Compose.lean`):

    @sv.transform(
        requires={"orders": [_.amount >= 0, _.amount < 1_000_000_000, sv.unique("id")]},
        ensures=[_.amount >= 0, _.amount < 1_000_000_000, _.amount.notnull(), sv.unique("id")],
    )
    def paid(orders):
        return orders.filter(orders.amount.notnull())

    @sv.transform(
        requires={"t": [_.amount >= 0, _.amount < 1_000_000_000, _.amount.notnull()]},
        ensures=[_.doubled >= 0, _.doubled.notnull()],
    )
    def doubled(t):
        return t.select(t.id, t.customer, doubled=t.amount * 2)

    doubled(paid(orders))     # `doubled` is proved from `paid`'s guarantees

A link that does not hold raises `CompositionError` naming both sides:
"doubled needs (_.amount >= 0) (it may be FALSE on some rows) on 't'; not_null only
guarantees _.amount.notnull()". Plain Ibis steps in between carry no
guarantees of their own. A composed result can be maintained incrementally
(`sverify.incremental`): its preconditions on the base tables are then
checked on each batch of changes, and its guarantees hold in every state.

Conditions are Ibis expressions (`_.amount >= 0`, or a function of the table)
or SQL snippets (`"amount >= 0"`). SQL snippets are DuckDB's SQL, compiled to
Substrait by sverify's lift (`sverify.sql_lift`).

Runtime checks run through Ibis, on the connection the tables are bound to
(`sverify.connect()`), by default; naming an engine (`engine="duckdb"`,
`"polars"` or `"datafusion"`, see `sverify.engines.run`) runs each
condition's plan, as Lean wrote it, there instead, so such conditions must be
inside the Lean model. `unique` checks always run through Ibis.
"""

from __future__ import annotations

import difflib
import functools
import inspect
import json
import math
import os
import re
import warnings
import weakref
from collections import Counter
from collections.abc import Callable, Collection, Container, Mapping, Sequence
from dataclasses import dataclass, field, replace
from datetime import date, datetime, timedelta
from decimal import Decimal
from fractions import Fraction
from typing import TYPE_CHECKING, Any, ClassVar, Literal, overload

import ibis
import ibis.expr.operations as ops
import ibis.expr.types as ir
from ibis.common.deferred import Deferred
from ibis.common.graph import Node

from sverify import _deprecated, _stages
from sverify import observation as _observation
from sverify._duration import Duration, duration
from sverify._hooks import COLLECTING, Collected
from sverify._quarantine import Policy, check_policy
from sverify._unsupported import SverifyError
from sverify.counterexample import Counterexample
from sverify.counterexample import search as search_counterexample
from sverify.engine import (
    Connection,
    Engine,
    checker_failed,
    connect,
    connection_of,
    plan_json,
    run_checker,
    run_plan,
    written_plan,
)
from sverify.observation import Observation
from sverify.routes import RouteError

type Policies = dict[str, dict[str, set[Policy | None]]]
"""By table and condition label, the `on_violation` of each transform that
states the condition (None: unset)."""

if TYPE_CHECKING:
    import pyarrow as pa

    from sverify.routes import Route, RouteKind


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
class Approx:
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


Semantics = Literal["reference", "duckdb", "polars", "substrait"]
"""The profile a check is under: sverify's reference semantics (the
default), DuckDB's (#411), whose SQL also means what DuckDB computes,
Polars's, for Ibis transformations, or Substrait's own, as its extension
YAMLs state it (#444)."""

#: The profiles the checker is asked for by name (`"profile"` in a
#: `--contract` request): those beyond the reference and DuckDB's lift.
_PROFILE_REQUESTS = frozenset({"polars", "substrait"})


def _transfer_failure(f: Mapping[str, Any]) -> str:
    """Why the reference's proof does not carry over to Substrait at one option."""
    where = f"{f['group']}'s {f['option']}" if f.get("group") else f["option"]
    return (
        f'not proved under semantics="substrait": {where} allows '
        f"{', '.join(f['substrait'])}, the reference only {', '.join(f['reference']) or 'nothing'}"
    )


def _expr_semantics(transform: Transform) -> Semantics:
    """The semantics an unstated `verify(semantics=...)` takes: an expression
    whose SQL (`sverify.sql`) is all lifted with DuckDB's semantics has
    them (#575: so its report assumes no ±∞ precondition and `Report.run`
    writes no check of one); anything else, the reference."""
    if isinstance(transform, str):
        return "reference"
    from sverify.ibis_substrait.relations import SQLModel

    found = transform.op().find(SQLModel)
    sems = {op.semantics or "reference" for op in found}
    return "duckdb" if sems == {"duckdb"} else "reference"


def _checked_semantics(semantics: str) -> Semantics:
    if semantics not in ("reference", "duckdb", "polars", "substrait"):
        raise ValueError(
            f"semantics must be 'reference', 'duckdb', 'polars' or 'substrait', not {semantics!r}"
        )
    return semantics  # type: ignore[return-value]


Condition = (
    Deferred
    | ir.BooleanValue
    | str
    | Unique
    | Key
    | References
    | ArrivesWithin
    | MaxRows
    | RowsPer
    | Observation
    | Callable[[ir.Table], ir.BooleanValue]
)
Transform = ir.Table | str

UnprovedReason = Literal[
    "observation",
    "not_a_key",
    "ties",
    "always_false",
    "may_be_false",
    "may_be_null",
    "not_proved_kind",
    "unknown",
]
"""`CheckedCondition.reason`: why a postcondition is not proved."""

# The `value` of a postcondition sverify checks on data only.
_DATA_ONLY = frozenset(
    {
        "foreign keys are not proved",
        "lateness is checked on a source's batches",
        "rows per key are checked on inputs only",
    }
)


@dataclass(frozen=True)
class TiePlace:
    """A place where the plan leaves the order of ties open (D24): a window,
    an ordered aggregate (`first`, `group_concat`, …) or a `LIMIT` whose
    order is not total on the input's keys."""

    relation: int
    """The relation's index in the plan, in pre-order (`Report.relations`)."""
    op: str
    """The relation's operator: `window`, `aggregate` or `fetch`."""
    what: str
    """What is open there, with columns as `$i` of the relation's input."""

    def __str__(self) -> str:
        return f"the {self.op} at relation {self.relation}: {self.what}"


def tie_places(out: Mapping[str, Any]) -> list[TiePlace]:
    """The `tie_places` of `substrait-check`'s report."""
    return [TiePlace(t["relation"], t["op"], t["what"]) for t in out.get("tie_places", [])]


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


#: What a report suggests for an overflow it cannot rule out (#202).
OVERFLOW_HINT = (
    "an integer result may not fit its type (64 bits for BIGINT, or a timestamp's "
    "range), which raises. Bound the columns involved in `requires`, as a fact about "
    "your data: for example `_.amount < 1_000_000_000`, or, for an ASOF join with a "
    "tolerance, a lower bound on its time column such as `_.ts >= datetime(2000, 1, 1)`"
)

#: How a report's hint for a truncated timestamp or date starts.
TRUNC_HINT = "bound the truncated column"


def _truncates(expr: str) -> bool:
    """Whether an issue's expression (`Expr.render`) truncates a timestamp or
    a date, or bins a timestamp."""
    return any(f in expr for f in ("DATE_TRUNC_", "DAY_TRUNC_", "BUCKET_"))


#: How a report explains a `SUM` that may overflow: an error like any other,
#: which the job also checks while it runs.
RUNTIME_CHECK = (
    "the job also checks it while it runs and raises if it happens; a bound on "
    "the column and on the rows of a group rules it out"
)

#: How a report explains a `SUM` it assumes fits (`Report.assumed`).
SUM_ASSUMED = (
    "fits {} in every group (checked at run time: the job raises if it does not; "
    'on_inferred="off" makes it an error)'
)

#: A decimal `SUM`'s argument in Lean's notation: `DECIMAL_p_s(…)`.
_DECIMAL_ARG = re.compile(r"DECIMAL_(\d+)_(\d+)\(")


#: How a report explains an operation it assumes stays finite (#575).
FINITE_ASSUMED = (
    "stays finite on finite inputs (checked at run time: the data is checked "
    'before the run, which is refused if it overflows to ±inf; on_inferred="off" '
    "makes it an error)"
)

#: The kind of an operation on finite doubles that may give `±∞` (#575).
INFINITE = "overflow to infinity"

#: What a report suggests for an operation that may overflow to `±∞` (#575).
INFINITE_HINT = (
    "no bound on a column proves a double operation finite; unless "
    'on_inferred="off", it is assumed and checked on the data while the job runs'
)


#: What a report says of a constant that raises (#609, D21).
CONSTANT_HINT = (
    "this operation reads no column and raises: DuckDB evaluates it when it "
    "plans the query, so the plan raises on any data, an empty table included, "
    "and no precondition rules it out. Fix or remove the constant"
)


def _sum(issue: Issue) -> bool:
    """Whether `issue` is a `SUM` that may leave its type."""
    return issue.kind == "SUM overflow"


def _assumable(issue: Issue) -> bool:
    """Whether `issue` is assumed not to happen, and checked on the data while
    the job runs (`Issue.assumed` in `SubstraitLean/Safety.lean`): a `SUM`
    that may leave its type, or an operation on finite doubles that may give
    `±∞` (#575)."""
    return _sum(issue) or issue.kind == INFINITE


def _assumption(issue: Issue) -> str:
    """How a report names an assumed issue."""
    if _sum(issue):
        return f"SUM of {issue.what} {_sum_assumed(issue)}"
    return f"{issue.shown or issue.expr} {FINITE_ASSUMED}"


def _cause(issue: Issue) -> str:
    """What makes an issue happen, where its kind does not say: a domain
    error of a double SUM or addition is NaN from +inf plus -inf."""
    if issue.kind != "domain error" or issue.shown is None:
        return ""
    m = re.fullmatch(r"(?:sum|avg|mean)\((\w+)\)(?: or \w+\(\1\))*", issue.shown)
    if m:
        return (
            f" (NaN where {m[1]} holds both +inf and -inf: bound it in requires, "
            f"e.g. `_.{m[1]}.between(-1e300, 1e300)`)"
        )
    if re.search(r" [-+] ", issue.shown):
        return " (NaN from +inf minus +inf: bound the columns in requires)"
    return ""


def _sum_assumed(issue: Issue) -> str:
    """`SUM_ASSUMED` for `issue`: 64 bits for an integer `SUM`, the result's
    `DECIMAL(min(38, p + 10), s)` for a decimal one (`Measure.sumOk`, #316)."""
    if m := _DECIMAL_ARG.match(issue.expr):
        p, s = int(m[1]), int(m[2])
        return SUM_ASSUMED.format(f"DECIMAL({min(38, p + 10)}, {s})")
    return SUM_ASSUMED.format("64 bits")


@dataclass(frozen=True)
class Issue:
    """Something that may go wrong when the transformation runs
    (`Rel.mayIssues_sound` in `SubstraitLean/Safety.lean`)."""

    kind: str
    """"division by zero", "overflow" (an integer result that does not fit its
    declared width, `MIN / -1`, …), "cast out of range", "negative exponent",
    "domain error", "SUM overflow" (a `SUM` leaving its type: 64 bits for
    integers, the result's precision for decimals), or "overflow to infinity"
    (an operation on finite doubles, or their `SUM` or `AVG`, giving `±∞`,
    #575)."""
    expr: str
    """The operation, in Lean's notation (`$i` is the operation's i-th input
    column)."""
    error: bool
    """True if a proof must rule it out. Every issue is one; a "SUM overflow"
    or an "overflow to infinity" is also checked while the job runs, where
    the transformation's SQL raises too."""
    hint: str | None = None
    """For an overflow: the bound that would rule it out, as code to add to
    a contract, or why no bound on a column does (`infer_bounds`). None if
    there is nothing to suggest."""
    column: str | None = None
    """For a "SUM overflow": the column the SUM adds up, named as in its
    hint (the base table's column where it is passed on unchanged). None if
    `expr` is not a single column."""
    constant: bool = False
    """The operation reads no column and raises (#609, D21): DuckDB evaluates
    such a constant when it plans the query, so the plan raises on any data,
    and no precondition rules it out (`CONSTANT_HINT`)."""
    under_and_or: bool = False
    """The operation sits inside an operand of an `AND` or `OR`, which
    evaluates both operands (#604, D19): a guard in the other operand does
    not keep it from raising. The report suggests a `CASE` (`AND_OR_HINT`)."""
    _labels: tuple[str, ...] = field(default=(), repr=False, compare=False)
    """The preconditions that rule it out, as labels, where the inference
    found them (`infer_bounds` assumes them)."""
    shown: str | None = None
    """The operation in the user's terms: column names and the Ibis or SQL
    operator (`total // qty`, `sum(x)`); None where the plan does not say
    which columns `expr` reads."""
    needs: list[Needed] = field(default_factory=list, compare=False)
    """The preconditions that rule it out, one `Needed` each, where the
    inference found them: what `hint` says to state in `requires`, as data.
    Empty where it found none."""
    hint_needs: dict[str, list[Condition]] = field(default_factory=dict, repr=False, compare=False)
    """The preconditions per input table that `hint` proposes, as code; a
    hint is shown only where a proof with them rules the issue out
    (`_confirm_hints`, #688)."""
    unconfirmed: str | None = field(default=None, repr=False, compare=False)
    """The hint to show instead where a proof does not confirm `hint`."""

    @property
    def suggested(self) -> dict[str, tuple[str, ...]]:
        """Deprecated: `needs`. Its labels per input table."""
        warnings.warn(
            "Issue.suggested is deprecated; read Issue.needs",
            DeprecationWarning,
            stacklevel=2,
        )
        return _labels_by_table(self.needs)

    @property
    def what(self) -> str:
        """The column, or else the expression, a report names the issue by."""
        return self.column or self.shown or self.expr

    @property
    def message(self) -> str:
        """The issue in words, as `str(report)` prints it after "may fail: ":
        its kind, the operation, what causes it where the kind does not say,
        and, for one the job also checks while it runs, that it does."""
        return f"{self}{_cause(self)}" + (f" ({RUNTIME_CHECK})" if _assumable(self) else "")

    @property
    def assumption(self) -> str:
        """For an issue in `Report.assumed`: what the report assumes of it, as
        `str(report)` prints it after "assumes: "."""
        return _assumption(self)

    def __str__(self) -> str:
        return f"{self.kind}: {self.shown or self.expr}"


@dataclass
class Report:
    """What the checker proved about a transformation, returned by `verify` and kept
    in `ContractedTransform.report`.

    `str(report)` lists each postcondition with its status, the possible
    runtime errors and warnings, and what is known about each output column;
    in a notebook the report renders as tables.
    """

    requires: dict[str, list[str]]
    """The preconditions that were assumed, as labels, per input table."""
    ensures: list[CheckedCondition]
    """Each postcondition, in the order given: its label, whether it was
    proved, what the checker established about it, and a counterexample if one was
    found."""
    facts: dict[str, str] = field(default_factory=dict)
    """What the checker established about each output column."""
    not_null: list[str] = field(default_factory=list)
    """The output columns the checker proved never NULL, from what it
    established about them (`facts`), in the output's order. A stored node
    of a proved report writes them as NOT NULL columns."""
    deterministic: bool = True
    """False when rows may tie in the ORDER BY of a window or of an ordered
    aggregate (`first`, `last`, `group_concat`; without an `order_by` every
    row ties), or when a `LIMIT` takes rows that tie in its `ORDER BY`, or
    has none. The engine then picks an order, and a rerun may pick another
    (D10). The postconditions are proved for every order (D24); the
    deterministic profile (`run(reproducible=sv.equivalent())`, a sink's
    `reproducible=`) refuses such a plan and names `tie_places`."""
    _windows_total: bool = field(default=True, repr=False)
    """False only for the window and ordered-aggregate ties of
    `deterministic`."""
    _tie_places: list[TiePlace] = field(default_factory=list, repr=False)
    """Where the plan leaves the order of ties open (D24), one entry per
    window, ordered aggregate or `LIMIT`; empty when `deterministic`."""
    issues: list[Issue] = field(default_factory=list)
    """Runtime errors, SUM overflows among them, the checker could not rule out; when
    empty, the transformation provably runs without them."""
    _guard_free: bool = field(default=False, repr=False)
    """The only issues are assumed ones (`SUM`s that may overflow, double
    operations that may give `±∞`, which keep their checks): on data that meets
    the preconditions, the transformation's SQL (`sverify.engines.to_sql`)
    and Polars plan give the same result with `guards=False`, without
    per-row checks (`Rel.guardFree_sound`)."""
    _unchecked: dict | None = field(default=None, repr=False)
    """The expressions that run correctly without their checks, on data that
    meets the preconditions (`Rel.evalG_marks`), as a tree parallel to the
    plan; pass it to `sverify.engines.to_sql(..., unchecked=...)` with the
    same plan, and only the other expressions keep their checks. None when
    Lean found none (a left join with a filter on its right side, for one)."""
    _optimized: dict | None = field(default=None, repr=False)
    """The transformation as a Substrait JSON plan, rewritten with the facts
    and keys of the preconditions (`Rel.optimize` in
    `SubstraitLean/Semantic.lean`): for example a `DISTINCT` over a key is
    gone. On data that meets the preconditions it gives the same rows
    (`Rel.optimize_sound`); pass it to `sverify.engines.to_sql`, or as JSON
    to `sverify.engines.run`, instead of the transformation. None if Lean
    did not return one."""
    _rewrites: list[str] = field(default_factory=list, repr=False)
    """The rewrites in `optimized`, such as "DISTINCT on a key"."""
    _inferred: dict[str, list[Condition]] = field(default_factory=dict, repr=False)
    """The bounds inferred to rule out overflow (`infer_bounds`), per input
    table: also in `requires`, and assumed like the rest of it."""
    _implied: dict[str, str] = field(default_factory=dict, repr=False)
    """A SQL condition per input table that every row reaching the result
    passes, given `requires` (#81, `Rel.need_eval` in
    `SubstraitLean/Implied.lean`): the transformation gives the same result
    on the table's rows that pass it. `sverify.io` sources read only those,
    and skip the files whose statistics rule it out."""
    assumed: list[Issue] = field(default_factory=list)
    """The `SUM`s assumed to fit their type in every group (64 bits for
    integers, the result's precision for decimals), and the operations on
    finite doubles assumed to stay finite (#575): those the inputs' row caps
    (`max_rows`, #219) and the values' range do not prove to fit. The job
    checks each at run time, on the data, and raises where one fails. The
    proof holds under these assumptions (`Rel.noIssue_of_assumedHold`). With
    `on_inferred="off"` they are errors instead."""
    _params: list[str] = field(default_factory=list, repr=False)
    """The `ibis.param` values the transformation was verified with
    (`verify(..., params=...)`), as `param1 (int64) = 5`: every proof is for
    these values only."""
    _hints: list[str] = field(default_factory=list, repr=False)
    """What to add to the contract for the `issues` it names (#379): bounds
    on a truncated timestamp column, or on the column an integer `SUM` adds
    up, with the largest group the bound lets fit."""
    _bounds: dict[str, tuple[int | None, int | None]] = field(
        default_factory=dict, repr=False, compare=False
    )
    rows: int | None = None
    """At most this many output rows, from the inputs' row caps (`max_rows`
    in `requires`, `Rel.maxRows`); None if nothing bounds them."""
    _relations: list[RelationRows] = field(default_factory=list, repr=False, compare=False)
    """Each relation of the plan, from the result down in pre-order, with
    the bounds Lean proves on its rows and, for an aggregate, on the rows
    of a group (#219)."""
    semantics: Semantics = "reference"
    """The profile the report is under (`verify(semantics=...)`):
    `"reference"`, sverify's reference semantics; `"duckdb"`, what DuckDB
    computes (#411); `"polars"`; or `"substrait"`, Substrait's own (#444)."""
    """The integer bounds Lean found on each integer output column, lowest
    and highest (None: unbounded), for hints."""
    internal_plan: str | None = field(default=None, repr=False, compare=False)
    """The plan the report is about, as Substrait protobuf JSON: the
    transformation as `verify` compiled it and Lean checked it, with the
    `params` bound and the SQL lifted with `semantics`. `run` runs it (#461)."""
    observation: Observation = field(default_factory=lambda: _observation.PLAN_BOUND)
    """What the result's consumer observes (`sv.equivalent` in `ensures`,
    #444). When `ensures` names none: rows as a multiset, doubles within the
    plan's bound (`floats="plan"`, printed with the bound, `epsilon`) and
    other values exact, the same as `sv.equivalent(floats="plan")`. Under
    the plan's bound a run holds the double columns a postcondition reads
    to their exact value (`sverify.routes.observed`). `equivalence` is the same, by the
    concept's name."""
    _stated: bool = field(default=False, repr=False, compare=False)
    """Whether `ensures` names the observation (`sv.equivalent`)."""
    _floats_on: dict[str, list[str]] = field(default_factory=dict, repr=False, compare=False)
    """Where the observation asks for exact doubles or a tolerance: per
    engine the reference translates to, why that engine's doubles may not
    meet it (empty where they do), checked against the plan's bound
    (`epsilon`) at `verify`. Empty under `floats="plan"`, which every
    engine meets. Where no engine meets it, the plan is not proved
    (`floats_unmet`)."""
    _depends: list[dict] | None = field(default=None, repr=False, compare=False)
    """The options of the profile the proof depends on (`docs/core-semantics.md`,
    step 3c), as the checker reports them: `{"group", "option",
    "behaviours"}` rows. None when the checker does not report them; the
    option-wise transfer check then takes every option of every group the
    plan calls."""
    routes: dict[str, Route] = field(default_factory=dict, repr=False, compare=False)
    """The route each engine ran the plan by (`run(..., route=...)`, D13),
    by engine name."""
    _contract: dict | None = field(default=None, repr=False, compare=False)
    """The request the checker proved, for a check under another profile."""
    _transfer: list[dict] | None = field(default=None, repr=False, compare=False)
    """Under `semantics="substrait"`, the options where Substrait allows more
    than the reference, so that the reference's proof does not carry over:
    `{"group", "option", "preferences", "substrait", "reference"}` rows, each
    with the behaviours the profile allows. Empty when it carries over; None
    under every other profile."""
    output: dict[str, Any] = field(default_factory=dict, repr=False, compare=False)
    """The output's columns with their Ibis types."""
    _epsilon: dict[str, dict[str, Any]] | None = field(default=None, repr=False, compare=False)
    """How far each double output column may be from a result the reference
    allows on an engine whose summation order differs (`{"abs", "rel"}` per
    column, #568), as the checker computes it for this plan; None where it
    does not."""
    _rows_exact: dict[str, bool] | None = field(default=None, repr=False, compare=False)
    """Per engine, whether every filter, key and sort of the plan keeps the
    same rows and groups under the columns' `ε` (#568's threshold rule): a
    comparison on a double whose threshold lies within `ε` of its range may
    flip. None where the checker does not say."""
    _conditions: dict[str, list[Condition]] = field(default_factory=dict, repr=False, compare=False)
    _dialect: Literal["ibis", "sql"] = field(default="ibis", repr=False, compare=False)
    """The language of the transformation: the report names functions and
    writes code in it."""
    ties: dict[str, list[str]] = field(default_factory=dict, repr=False, compare=False)
    """For a result not determined up to row order (`deterministic`), the
    `sv.unique(...)` per input table that would determine it: the partition
    (or grouping) and order columns of its windows and ordered aggregates."""
    _on_inferred: OnInferred = field(default="ignore", repr=False, compare=False)
    """What the inferred preconditions (`inferred`) do to the proof
    (`verify(on_inferred=...)`): with `"error"`, a plan that needs one is
    not proved (`needed`)."""
    _inferred_from: dict[str, Issue] = field(default_factory=dict, repr=False, compare=False)
    """For each inferred precondition (by label), the runtime error it rules
    out: where it came from."""
    """The preconditions per input table, as conditions: `requires` and
    the bounds inferred (`inferred`). `check_inputs` checks them on data."""
    _postconditions: list[Condition] = field(default_factory=list, repr=False, compare=False)
    """The postconditions, as conditions, in the order of `ensures`
    (`to_substrait` ships them)."""
    inputs: dict[str, ibis.Schema] = field(default_factory=dict, repr=False, compare=False)
    """The schema of each input table the plan reads, by table name: the
    columns `requires` may name, per table, as `output` holds those
    `ensures` may name."""

    def to_json(self, indent: int | None = None) -> str:
        """The report as a versioned JSON document, for CI jobs and tools
        (#736), in the format of `sverify/schemas/report.schema.json`:
        `format` (1), the verdict, each postcondition with its status and
        `reason`, the runtime errors and assumptions, `needs`, the facts on
        each output column, the routes engines ran the plan by, and the rest
        `str(report)` says. Conditions appear as their labels. Within 1.x
        the format only gains keys (`docs/stability.md`).

        Args:
            indent: Indent the JSON by this many spaces; None writes one line.

        Returns:
            The JSON document, keys sorted.
        """
        from sverify import report_json

        return json.dumps(report_json.to_json(self), indent=indent, sort_keys=True)

    @staticmethod
    def from_json(data: str | Mapping[str, Any]) -> Report:
        """A report from what `to_json` wrote, by this version of sverify or
        an earlier one. Keys this version does not know are left out.

        The report has the same verdict, postconditions, issues, needs,
        facts and routes. It holds no plan, and its conditions are their
        labels, so it does not `run`, `check_inputs` or `to_substrait`.

        Args:
            data: The JSON, as text or parsed.

        Returns:
            The report.

        Raises:
            ValueError: The document's `format` is newer than this version
                reads.
        """
        from sverify import report_json

        return report_json.from_json(data)

    @staticmethod
    def from_substrait(data: str | bytes | Mapping[str, Any]) -> Report:
        """Read a plan `to_substrait` exported, and prove its contract again
        with the checker (#664).

        The plan goes to the checker as it was exported, pinned options,
        shims and all, with the preconditions and postconditions it
        carries; the report says what the checker proves of it now. For an
        export of a verified plan, `proved` is true again, with the same
        postconditions.

        Args:
            data: The export: protobuf JSON (a string or its dict) or bytes.

        Returns:
            A `Report` of the plan: its postconditions with their status,
            the runtime errors the checker cannot rule out, the facts on
            each output column and the options the proof depends on. Facts
            are in Lean's notation, and nothing is known of the Ibis types.

        Raises:
            ValueError: The plan carries no sverify contract, or the
                checker rejects the plan.
        """
        from sverify.substrait_export import recheck

        return recheck(data)

    @overload
    def to_substrait(
        self,
        format: Literal["json"] = "json",
        *,
        shims: Literal["apply", "annotate", "refuse"] = "apply",
    ) -> str: ...

    @overload
    def to_substrait(
        self,
        format: Literal["binary"],
        *,
        shims: Literal["apply", "annotate", "refuse"] = "apply",
    ) -> bytes: ...

    def to_substrait(
        self,
        format: Literal["json", "binary"] = "json",
        *,
        shims: Literal["apply", "annotate", "refuse"] = "apply",
    ) -> str | bytes:
        """The verified plan for any conforming Substrait consumer, with its
        contract as metadata (#664).

        Every function call names its YAML's URN, its compound name and its
        output type (Substrait 0.106). Every option the proof depends on
        (`depends`) is pinned in the call's options at the reference's
        behaviour. Where Substrait has no option for a choice the proof uses
        (a spec gap, `upstream/bugs/ST-*.json`), `shims` decides: `"apply"`
        rewrites the plan into well-specified Substrait, `"annotate"` keeps
        it and records the choice in the metadata as an assumption the
        consumer must honour, and `"refuse"` refuses the export. A gap where
        the reference raises needs no shim in any mode: the preconditions,
        which travel with the plan, rule those inputs out.

        The contract travels in the plan's `advanced_extensions` as an
        `io.sverify.substrait.v1.Contract`: `requires` (declared, inferred
        and assumed) and `ensures`, each in your terms and as a Substrait
        plan, and a manifest (the profile, the pinned options, the shims and
        assumptions, the observation the result holds up to, the Substrait
        version and extension URNs, sverify's version). `sv.Report.from_substrait`
        reads it back and proves the contract again.

        Args:
            format: `"json"` (protobuf JSON, a string) or `"binary"` (the
                serialized `substrait.Plan`).
            shims: What to do at a spec gap the proof depends on.

        Returns:
            The plan, as protobuf JSON or bytes.

        Raises:
            sverify.errors.ExportError: The report is not proved,
                or the plan has no conforming Substrait form that keeps the
                proof; the message names the reason and the gap.
        """
        from sverify import substrait_export

        return substrait_export.export(self, format, shims=shims)

    def substrait_contract(
        self, *, shims: Literal["apply", "annotate", "refuse"] = "apply"
    ) -> dict:
        """The contract `to_substrait` embeds, as JSON, for a sidecar file."""
        from sverify import substrait_export

        return substrait_export.contract_json(self, shims=shims)

    def to_sql(self, dialect: Any = "duckdb") -> str:
        """The verified plan as SQL whose meaning is the proof's, in
        `dialect`.

        The SQL keeps every run-time check, as `run` does. Where the report
        is `deterministic` (no window ties on data that meets the
        preconditions), windows need no row-order tiebreak, so Snowflake and
        Spark take them. A plan verified under an engine's semantics
        (`semantics="duckdb"`) is written only for an engine its route
        reaches (`sverify.routes.choose`). Snowflake takes plans verified
        under the reference. Run the SQL on data that meets the
        preconditions (`requires`); `run` checks them first
        (`check_inputs`).

        Args:
            dialect: `"duckdb"` (the default), `"snowflake"` or `"spark"`,
                or one of `sverify.engines.DUCKDB`, `SNOWFLAKE` and `SPARK`.

        Returns:
            One SQL query, reading the plan's tables by the names it was
            verified with.

        Raises:
            ValueError: The report has no plan (it was not made by
                `verify`), or `dialect` is unknown.
            sverify.errors.UnverifiedRunError: The plan is not proved.
            sverify.errors.RouteError: No route takes the plan to the
                dialect's engine.
            sverify.errors.Unsupported: The dialect cannot express the plan.

        Examples:
            ```python
            report = sv.verify(
                "SELECT host, max(cpu) AS m FROM t GROUP BY host",
                tables={"t": t},
                ensures=[sv.unique("host")],
            )
            print(report.to_sql("snowflake"))
            ```
        """
        from sverify.sql import to_sql

        if self.internal_plan is None:
            raise ValueError("this report has no plan: it was not made by sv.verify")
        d, finite = self._sql_route(dialect)
        return to_sql(
            written_plan(self.internal_plan), d, deterministic=self.deterministic, finite=finite
        )

    def _sql_route(self, dialect: Any) -> tuple[Any, bool]:
        """The dialect `dialect` names, and whether its SQL checks the
        reference's `±∞` precondition, for this report's plan; refused as
        `run` refuses it."""
        from sverify import routes
        from sverify.sql import dialect_of

        d = dialect_of(dialect)
        if d.name in ("duckdb", "spark"):
            chosen = routes.choose(self, d.name)
        else:
            # Snowflake has no profile: it takes the reference's translation.
            reason = None
            if not routes.verified(self):
                reason = routes.not_verified(self)
            elif self.semantics != "reference":
                reason = (
                    f"verified under {self.semantics} semantics; {d.name} SQL is written "
                    "only for plans verified under the reference"
                )
            chosen = routes.Route(
                d.name,
                None if reason else "translated",
                self.semantics,
                reason or "the reference's translation",
                self.deterministic,
                cls="refused" if reason else None,
            )
        if chosen.refused:
            reason = chosen.reason.removesuffix("; run(..., unverified=True) runs it anyway")
            chosen = replace(chosen, reason=reason)
            if not routes.verified(self):
                raise UnverifiedRunError(self, chosen)
            raise routes.RouteError(chosen)
        return d, self.semantics == "reference" or chosen.kind == "translated"

    def check_inputs(self, con: Connection) -> None:
        """Check the preconditions (`requires`, the inferred bounds among
        them) and the `SUM`s assumed to fit (`assumed`) on the tables of
        `con`, before anything runs: a batch that breaks one is refused
        with the precondition as the message (#444, goal 1).

        Raises:
            PreconditionError: A precondition or an assumed `SUM` does not
                hold on the data.
        """
        for t, conds in self._conditions.items():
            if not con.has(t):
                continue
            table = con.table(t)
            for c in conds:
                if n := violations(table, c):
                    raise PreconditionError(
                        f"{n} row(s) of {t} violate {label(c)}: refused before the run"
                        + self._source(t, c),
                        source=t,
                        condition=c,
                        rows=violating_rows(table, c),
                    )
        if self.assumed and self.internal_plan is not None:
            # The proved DuckDB translation checks each assumption as it runs:
            # a SUM as it adds up, an operation on finite doubles as it gives
            # its result (#575). It runs first, so a batch that breaks one is
            # refused before the plan runs on any engine, Polars included.
            try:
                run_plan(con, written_plan(self.internal_plan), "duckdb")
            except Exception as e:
                message = str(e)
                if "overflow in SUM" not in message and "overflow to infinity" not in message:
                    raise
                broken = ", ".join(_assumption(i) for i in self.assumed)
                raise PreconditionError(
                    f"the batch breaks an assumed precondition, {broken}: refused before the run"
                ) from e

    def _source(self, table: str, c: Condition) -> str:
        """Where a precondition the data breaks came from, and what to do,
        for one the report inferred."""
        lab = label(c)
        if lab not in {label(x) for x in self._inferred.get(table, [])}:
            return ""
        issue = self._inferred_from.get(lab)
        where = f" ({issue.kind} otherwise)" if issue is not None else ""
        what = f" from `{issue.what}`{where}" if issue is not None else ""
        return (
            f". The precondition was inferred{what}: drop those rows before the transform, "
            f"`{table}.filter({lab})`, and compute on the rest; or guard the "
            "operation with a CASE; or state the precondition in requires as a fact "
            "about your data"
            if issue is not None
            else f". The precondition was inferred: drop those rows first, `{table}.filter({lab})`"
        )

    def run(
        self,
        con: Connection,
        engine: Engine | Any = None,
        *,
        route: RouteKind | Literal["auto"] = "auto",
        unverified: bool = False,
        reproducible: Observation | None = None,
        check_requires: bool = True,
        streaming: Literal["allow", "require"] = "allow",
        check_inputs: bool | None = None,
        deterministic: bool | None = None,
    ) -> pa.Table:
        """Run the plan this report checked (`plan`) over the tables of
        `con`, so the result is the one the report is about (#461).

        The plan reads the tables by the names it was verified with, and
        runs on `engine` as `sverify.engines.run` runs a plan, with the
        meaning `Rel.eval` gives it.

        A plan that is not proved (`proved` is False) is refused
        (`UnverifiedRunError`), with what was not proved in the message;
        `unverified=True` runs it anyway, and
        says so: a warning (`UnverifiedRunWarning`), the route `"unverified"`
        in `routes`, and `sverify.verified: false` in the result's schema
        metadata.

        The run first chooses how the proof reaches the engine
        (`sverify.routes.choose`, #444): `"auto"` takes the plan natively
        where it was verified under the engine's profile, through the
        reference's translation where it was verified under the reference,
        by the option-wise transfer check, or by a re-check under the
        engine's profile, and refuses it otherwise. The route goes into
        `routes`. Where `ensures` names no observation (`sv.equivalent`),
        the engine's doubles may differ from the reference's within the
        plan's bound (`epsilon`), except in the columns a postcondition
        reads.

        Args:
            con: The connection whose tables the plan reads (`sv.connect()`).
            engine: `"duckdb"`, `"polars"`, `"datafusion"`, `"spark"`, or a
                Spark session. Default: the connection's engine.
            route: `"auto"` (the default) chooses a route; `"native"`,
                `"translated"`, `"transfer"` or `"recheck"` takes that one or
                refuses (`"reference"` is a deprecated alias of
                `"translated"`).
            unverified: Run a plan that is not proved, without a route.
                Default False: such a plan is refused.
            reproducible: What a rerun must reproduce (D20): the
                engine's run-to-run variation must refine it, as a sink's
                `reproducible=` states it; `sv.equivalent()` asks for the
                same rows and bits (D10). Default None: determinism is only
                reported (`deterministic`).
            check_requires: Check the preconditions (`requires`, the
                inferred bounds among them) and the assumed `SUM`s on the
                tables of `con` before the run, and refuse a batch that
                breaks one (`check_inputs`, #444 goal 1, #604), as
                `transform(check_requires=)` does on bound inputs. Default
                True. False skips the check, for a caller that has made it
                already: the report's guarantee then holds only on data that
                meets them, and a batch that does not may raise on the
                engine.
            streaming: On Polars, `"require"` refuses a plan any of whose
                nodes runs on the in-memory engine
                (`polars_engine.fallback_nodes`); `"allow"` (the default)
                runs it. Either way a chosen route records the nodes in
                `Route.fallbacks`.
            check_inputs: Deprecated alias of `check_requires`.

        Returns:
            The result as an Arrow table, with the transformation's output
            names.

        Raises:
            ValueError: The report has no plan (it was not made by
                `verify`), or `engine` is unknown.
            sverify.errors.UnverifiedRunError: The plan is not proved, and
                `unverified` is False. It is a `VerificationError` and a
                `RouteError`.
            sverify.errors.RouteError: No route takes the plan to `engine`,
                or, with `streaming="require"`, a node of its Polars plan
                runs on the in-memory engine.
            sverify.routes.EngineVersionError: The engine's major version is
                not the one its profile's facts were probed at.
            sverify.errors.PreconditionError: With `check_inputs`, a
                precondition does not hold on the data: nothing ran.

        Examples:
            Verify a query, then run what was verified:

            ```python
            con = sv.connect()
            con.put("t", pa.table({"host": ["a", "a", "b"], "cpu": [1, 5, 7]}))
            report = sv.verify(
                "SELECT host, max(cpu) AS m FROM t WHERE cpu > 3 GROUP BY host",
                tables={"t": con.table("t")},
                ensures=[sv.unique("host")],
            )
            result = report.run(con)  # refused if report.proved is False
            ```
        """
        from sverify import routes

        if self.internal_plan is None:
            raise ValueError("this report has no plan to run: it was not made by sv.verify")
        if check_inputs is not None:
            warnings.warn(
                "Report.run(check_inputs=...) is deprecated; write check_requires=...",
                DeprecationWarning,
                stacklevel=2,
            )
            check_requires = check_inputs
        reproducible = _deterministic_arg("Report.run", deterministic, reproducible)
        kind: str | None = None
        target = engine if engine is not None else con.engine
        chosen = None
        if unverified and not routes.verified(self):
            chosen = routes.unverified(self, target)
            self.routes[chosen.engine] = chosen
            kind = chosen.kind
            warnings.warn(
                f"running on {chosen.engine} unverified: {chosen.reason}",
                routes.UnverifiedRunWarning,
                stacklevel=2,
            )
        else:
            chosen = routes.choose(self, target, route, reproducible=reproducible)
            self.routes[chosen.engine] = chosen
            kind = chosen.kind
            if chosen.refused:
                if not routes.verified(self):
                    raise UnverifiedRunError(self, chosen)
                raise routes.RouteError(chosen)
        if check_requires:
            self.check_inputs(con)
        if target == "polars" and (chosen is not None or streaming == "require"):
            self._streaming(con, chosen, streaming)
        # The check of an overflow to ±∞ is the reference's precondition
        # (#575): it is written for a plan verified under the reference, and
        # for one that reaches the engine through the reference's route.
        finite = self.semantics == "reference" or kind == "translated"
        out = run_plan(
            con,
            written_plan(self.internal_plan),
            engine,
            finite=finite,
            # A proved report's `deterministic` justifies Spark's windows
            # without a row-order tiebreak (`to_sql`'s `deterministic`).
            tie_free=self.deterministic and kind != "unverified",
        )
        if kind == "unverified":
            meta = {**(out.schema.metadata or {}), b"sverify.verified": b"false"}
            out = out.replace_schema_metadata(meta)
        return out

    def _assumed(self) -> list[Issue]:
        """The assumptions a report shows: not those about an operation
        that may raise a division by zero anyway."""
        raising = {i.expr for i in self.errors if i.kind == "division by zero"}
        return [i for i in self.assumed if i.expr not in raising]

    def _inferred_note(self, lab: str) -> str:
        issue = self._inferred_from.get(lab)
        return " (inferred)" if issue is None else f" (inferred from {issue.what})"

    def _streaming(self, con: Connection, chosen: Any, streaming: str) -> None:
        """Record the in-memory nodes of the plan's Polars streaming plan in
        its route, and refuse it with `streaming="require"` if it has any."""
        import dataclasses

        from sverify import polars_engine, routes
        from sverify.engine import read_tables

        assert self.internal_plan is not None
        plan = json.loads(written_plan(self.internal_plan))
        tables = {t: con._arrow[t] for t in read_tables(plan)}
        nodes = tuple(polars_engine.plan_fallbacks(plan, tables))
        if chosen is not None:
            chosen = dataclasses.replace(chosen, fallbacks=nodes)
            self.routes[chosen.engine] = chosen
        if streaming == "require" and nodes:
            refused = routes.Route(
                engine="polars",
                kind=None,
                profile=chosen.profile if chosen is not None else self.semantics,
                reason=(
                    f"{len(nodes)} node(s) of the streaming plan run on the in-memory engine "
                    f"(streaming='require'): " + "; ".join(n[:120] for n in nodes)
                ),
                fallbacks=nodes,
            )
            self.routes["polars"] = refused
            raise routes.RouteError(refused)

    @property
    def proved(self) -> bool:
        """Every postcondition holds and no runtime error is possible. With
        an observation (`sv.equivalent`), no postcondition depends on what
        it ignores, and some engine's doubles meet it (`floats_unmet`).
        Under `semantics="substrait"`, the reference's proof also carries
        over (`transfer` is empty)."""
        return (
            all(c.portable for c in self.ensures)
            and not self.errors
            and not self._transfer
            and not self.needs
            and not self.floats_unmet
        )

    @property
    def floats_unmet(self) -> str | None:
        """Why no engine's doubles meet the observation's `floats` (exact
        doubles, or a tolerance below the plan's bound), in words; None
        where one does (`floats_on`)."""
        if not self._floats_on or not all(self._floats_on.values()):
            return None
        return "; ".join(f"on {e}: {'; '.join(ps)}" for e, ps in self._floats_on.items())

    def _observes_lines(self) -> list[str]:
        """The `observes:` line: the observation, the plan's bound beside a
        stated tolerance, and which engines' doubles meet it."""
        from sverify import routes as _routes

        obs = self.observation
        bound = _routes.plan_bound(self._epsilon)
        if obs == _observation.PLAN_BOUND and bound is None:
            return []
        line = f"observes: {obs}"
        if obs.floats != "plan" and bound is not None:
            line += f"; the plan's bound on its doubles is {_observation._bound_text(bound)}"
        if not self._floats_on:
            return [line]
        met = [e for e, ps in self._floats_on.items() if not ps]
        missed = [e for e, ps in self._floats_on.items() if ps]
        want = "exact doubles" if obs.floats == "exact" else "the tolerance"
        if not missed:
            line += f"; {', '.join(met)} meet {want}"
        elif not met:
            line += f"; NOT met: no engine meets {want}"
            line += _routes._cap_text(_routes.max_rows_fix(self, "", obs))
        else:
            line += f"; {', '.join(met)} meet {want}, {', '.join(missed)} do not"
        return [line] + [f"  on {e}: {p}" for e in missed for p in self._floats_on[e]]

    @property
    def needs(self) -> list[Needed]:
        """The preconditions the proof needs that `requires` does not state,
        one `Needed` each: the table, the column, the comparison and the
        bound, the SQL, the condition ready for `requires=`, the runtime
        error it rules out and the fixes in words. These are the bounds
        sverify inferred (`infer_bounds`) and does not assume, so the list
        is empty unless `on_inferred="error"`. `suggested_requires` adds
        them to the stated preconditions.

            report = sv.verify(expr)
            if not report.proved:
                report = sv.verify(expr, requires=report.suggested_requires)
        """
        if self._on_inferred != "error":
            return []
        return self._inferred_needs()

    def _inferred_needs(self) -> list[Needed]:
        """Every inferred bound (`inferred`) as a `Needed`, assumed or not.

        Building them (an Ibis deferred and a text each) is most of the cost
        of `str(report)` and `to_json`, which read `needs` several times,
        so they are kept until what they are built from changes; `verify`
        sets those fields after constructing the report."""
        key = (
            self._dialect,
            tuple((t, tuple(map(str, cs))) for t, cs in self._inferred.items()),
            tuple((lab, id(i)) for lab, i in self._inferred_from.items()),
        )
        cached = self.__dict__.get("_needs_cache")
        if cached is not None and cached[0] == key:
            return list(cached[1])
        out = self._build_inferred_needs()
        self.__dict__["_needs_cache"] = (key, tuple(out))
        return out

    def _build_inferred_needs(self) -> list[Needed]:
        return [
            _needed(
                t,
                c,
                self._dialect,
                self._inferred_from.get(label(c)),
                self._needs_text(t, [label(c)]),
            )
            for t, cs in self._inferred.items()
            for c in cs
        ]

    @property
    def suggested_requires(self) -> dict[str, list[Condition]]:
        """The `requires=` mapping that states every precondition the proof
        uses: the stated ones and those sverify inferred (`needs`, and the
        bounds `on_inferred="warn"` or `"ignore"` assumes), per input table,
        ready to pass to `verify` or to paste into a contract."""
        out: dict[str, list[Condition]] = {}
        for t, cs in self._conditions.items():
            out[t] = [c for c in cs if not isinstance(c, Inferred)]
        for n in self._inferred_needs():
            have = out.setdefault(n.table, [])
            if n.condition is not None and n.label not in {label(c) for c in have}:
                have.append(n.condition)
        return {t: cs for t, cs in out.items() if cs}

    @property
    def needed(self) -> dict[str, list[str]]:
        """Deprecated: `needs`. Their labels per input table."""
        warnings.warn(
            "Report.needed is deprecated; read Report.needs",
            DeprecationWarning,
            stacklevel=2,
        )
        return {t: list(labs) for t, labs in _labels_by_table(self.needs).items()}

    @property
    def needed_text(self) -> list[str]:
        """Deprecated: `Needed.text` of each of `needs`."""
        warnings.warn(
            "Report.needed_text is deprecated; read Needed.text of report.needs",
            DeprecationWarning,
            stacklevel=2,
        )
        return self._needs_lines()

    @property
    def needed_conditions(self) -> dict[str, list[Condition]]:
        """Deprecated: `Needed.condition` of each of `needs`, or the whole
        mapping as `suggested_requires`."""
        warnings.warn(
            "Report.needed_conditions is deprecated; read Needed.condition of report.needs, "
            "or report.suggested_requires",
            DeprecationWarning,
            stacklevel=2,
        )
        out: dict[str, list[Condition]] = {}
        for n in self.needs:
            if n.condition is not None:
                out.setdefault(n.table, []).append(n.condition)
        return out

    @property
    def equivalence(self) -> Observation:
        """The equivalence the result is proved up to: `sv.equivalent(...)` in
        `ensures`, or rows as a multiset with exact values (`observation`)."""
        return self.observation

    def needs_text(self, table: str, labs: Sequence[str]) -> str:
        """Deprecated: `Needed.text` of each of `needs`."""
        warnings.warn(
            "Report.needs_text() is deprecated; read Needed.text of report.needs",
            DeprecationWarning,
            stacklevel=2,
        )
        return self._needs_text(table, labs)

    def needs_lines(self, needed: Mapping[str, Sequence[str]] | None = None) -> list[str]:
        """Deprecated: `Needed.text` of each of `needs`."""
        warnings.warn(
            "Report.needs_lines() is deprecated; read Needed.text of report.needs",
            DeprecationWarning,
            stacklevel=2,
        )
        return self._needs_lines(needed)

    def _needs_text(self, table: str, labs: Sequence[str]) -> str:
        """Needed preconditions on one table that come from one operation,
        where they come from, and the fixes."""
        issues = [i for lab in labs if (i := self._inferred_from.get(lab)) is not None]
        kinds = " or ".join(dict.fromkeys(i.kind for i in issues))
        where = f", inferred from `{issues[0].what}` ({kinds} otherwise)" if issues else ""
        both = " and ".join(labs)
        it = "it" if len(labs) == 1 else "them"
        cond = labs[0] if len(labs) == 1 else " & ".join(labs)
        return (
            f"{both} on {table}{where}: declare {it} in requires (each run then checks "
            f"{it} on the data), or rewrite so no row needs {it} (`{table}.filter({cond})` "
            f"first, or a CASE); on_inferred='warn' assumes {it} instead"
        )

    def _needs_lines(self, needed: Mapping[str, Sequence[str]] | None = None) -> list[str]:
        """`_needs_text` for each table and operation (the labels of `needs`
        by default; `inferred`, as labels, for a warning)."""
        out = []
        if needed is None:
            needed = _labels_by_table(self.needs)
        for t, labs in needed.items():
            groups: dict[str, list[str]] = {}
            for lab in labs:
                issue = self._inferred_from.get(lab)
                groups.setdefault(issue.what if issue else lab, []).append(lab)
            out += [self._needs_text(t, g) for g in groups.values()]
        return out

    @property
    def errors(self) -> list[Issue]:
        """The `issues` an engine fails on at run time (`Issue.error` is true)."""
        return [i for i in self.issues if i.error]

    @property
    def warnings(self) -> list[Issue]:
        """The `issues` that do not count against a proof. None do: an
        `SUM` that may leave its type is an error (`errors`)."""
        return [i for i in self.issues if not i.error]

    @property
    def suggestions(self) -> dict[str, list[Needed]]:
        """For each unproved postcondition with one, the preconditions under
        which it would be proved, one `Needed` each, by the postcondition's
        label (`{"(_.y <= 100)": [Needed(table="orders", label="(_.x <= 50)", …)]}`)."""
        return {
            c.label: [
                _needed(t, x, self._dialect, text=f"{label(x)} on {t} would prove {c.label}")
                for t, cs in c.suggested.items()
                for x in cs
            ]
            for c in self.ensures
            if c.suggested
        }

    @property
    def unproved(self) -> list[CheckedCondition]:
        """The postconditions in `ensures` that were not proved."""
        return [c for c in self.ensures if not c.proved]

    @property
    def notes(self) -> list[str]:
        """What the report notes about the result as a whole, as `str(report)`
        prints them after "note: ": that rows may tie in an `ORDER BY`
        (`deterministic` is False, `ties` says which keys would help), and
        that the proof holds for the `params` given only."""
        out = [] if self.deterministic else [self._ties_hint()]
        if self._params:
            out.append(f"{PARAMS_NOTE}: {', '.join(self._params)}")
        return out

    def route(
        self,
        engine: Any,
        route: RouteKind | Literal["auto"] = "auto",
        *,
        reproducible: Observation | None = None,
    ) -> Route:
        """The route by which `run` would take the plan to `engine`, and the
        plan's class there, without running it: the route `report.routes`
        records after a run (D13).

        Args:
            engine: The engine's name (`"duckdb"`, `"polars"`, …) or a Spark
                session.
            route: `"auto"` (the default) tries the routes in turn; a route
                by name (`"native"`, `"reference"`, `"transfer"`,
                `"recheck"`) is taken or refused.
            reproducible: What a rerun must reproduce, as `run` takes it.

        Returns:
            The `Route`: its `kind`, `cls` (`"exact"`, `"observed"`, `"shim"`
            or `"refused"`), `observation` and `reason`. A plan that is not
            proved is refused, with `reason` saying so.

        Raises:
            EngineVersionError: The installed engine is another major
                version than its profile's.
            EngineSettingsError: A setting the engine's profile depends on
                differs from its facts'.
        """
        from sverify import routes as _routes

        return _routes.choose(self, engine, route, reproducible=reproducible)

    def _all_hints(self) -> list[str]:
        """`hints`, and the general overflow hint for an overflow neither they
        nor its own `Issue.hint` cover."""
        truncated = any(h.startswith(TRUNC_HINT) for h in self._hints)
        covered = [
            i
            for i in self.errors
            if i.kind == "overflow" and (i.hint or truncated and _truncates(i.expr))
        ]
        if any(i.kind == "overflow" and i not in covered for i in self.errors):
            return [*self._hints, OVERFLOW_HINT]
        return self._hints

    @property
    def verdict(self) -> str:
        """The report's first line: "proved", or "NOT proved: " and what is
        missing, counted ("1 of 2 postconditions not proved, 1 possible
        runtime error")."""
        return "proved" if self.proved else f"NOT proved: {', '.join(self._counts())}"

    def _counts(self) -> list[str]:
        """What keeps the plan from being proved, counted."""

        def n(k: int, one: str, many: str | None = None) -> str:
            return f"{k} {one if k == 1 else many or one + 's'}"

        out = []
        if unproved := self.unproved:
            out.append(f"{len(unproved)} of {n(len(self.ensures), 'postcondition')} not proved")
        if ignored := [c for c in self.ensures if c.proved and c.ignores]:
            out.append(
                f"{n(len(ignored), 'postcondition')} "
                f"{'depends' if len(ignored) == 1 else 'depend'} on what the observation ignores"
            )
        if self.errors:
            out.append(n(len(self.errors), "possible runtime error"))
        if needed := len(self.needs):
            out.append(n(needed, "precondition") + " needed")
        if self._transfer:
            out.append(n(len(self._transfer), "option") + " where Substrait allows more")
        if self.floats_unmet:
            out.append("no engine's doubles meet the observation")
        return out or ["see the report"]

    def _ties_hint(self) -> str:
        """The note on ties (#688): where the order is open, and the key
        that closes it, where one on an input reaches the ORDER BY."""
        from sverify._user_text import named

        out = TIES_HINT.format(_ORDERED.get(self._dialect, _ORDERED["ibis"]))
        plan = json.loads(self.internal_plan) if self.internal_plan else None
        places = [named(t.what, plan) for t in self._tie_places]
        if places and all(places):
            out += f" ({'; '.join(dict.fromkeys(p for p in places if p))})"
        if self.ties:
            keys = " and ".join(
                f"{', '.join(f'`{k}`' for k in ks)} in the requires of {t!r}"
                for t, ks in self.ties.items()
            )
            return f"{out}. For a reproducible result, declare {keys}"
        return (
            f"{out}. For a reproducible result, order by columns that are unique there; "
            "no key on an input that sverify follows reaches them"
        )

    def __str__(self) -> str:
        lines = [self.verdict]
        needed = _labels_by_table(self.needs)
        for table, conds in self.requires.items():
            inferred = {label(c) for c in self._inferred.get(table, [])}
            lines += [
                f"requires {table}: {c}" + (self._inferred_note(c) if c in inferred else "")
                for c in conds
                if c not in needed.get(table, ())
            ]
        lines += [f"needs: {n}" for n in self._needs_lines()]
        for c in self.ensures:
            lines.append(f"ensures {c.label}: {c.message}")
            if c.counterexample is not None:
                lines.append(f"  counterexample: {c.counterexample}")
            if c.suggested:
                lines.append(f"  {_would_hold(c)}")
        lines += [f"assumes: {i.assumption}" for i in self._assumed()]
        for i in self.errors:
            lines.append(f"may fail: {i.message}")
            if i.hint:
                lines.append(f"  hint: {i.hint}")
        lines += [f"hint: {h}" for h in self._all_hints()]
        lines += [f"note: {n}" for n in self.notes]
        lines.append(f"semantics: {self.semantics}")
        lines += [f"  {_transfer_failure(f)}" for f in self._transfer or ()]
        lines += self._observes_lines()
        lines += [f"route on {e}: {r}" for e, r in self.routes.items()]
        if self.facts or self.rows is not None:
            lines.append("known about the output:")
            if self.rows is not None:
                lines.append(f"  rows: at most {self.rows:,}")
            lines += [f"  {name}: {value}" for name, value in self.facts.items()]
        return "\n".join(lines)

    def _repr_markdown_(self) -> str:
        def status(c: CheckedCondition) -> str:
            if c.proved:
                return "✅ proved"
            if c.checked:
                return f"☑️ {c.why}; {DATA_CHECK}"
            if c.counterexample is None:
                return f"❌ {c.why}"
            return f"❌ {c.why}; fails on `{c.counterexample}`".replace("|", "\\|")

        rows = []
        for c in self.ensures:
            rows.append(f"| `{c.label}` | {status(c)} |")
            if c.suggested:
                rows.append(f"| suggestion | {_would_hold(c).replace('|', '\\|')} |")
        for n in self._needs_lines():
            rows.append(f"| needs | ❌ {n.replace('|', '\\|')} |")
        # Issues quote expressions, which may contain `|` (a regex, an OR).
        for i in self.errors:
            note = f" ({RUNTIME_CHECK})" if _assumable(i) else ""
            rows.append(
                f"| runtime | ❌ may fail: {(str(i) + _cause(i)).replace('|', '\\|')}{note} |"
            )
            if i.hint:
                rows.append(f"| hint | {i.hint.replace('|', '\\|')} |")
        inferred = [
            f"`{label(c)}` on {t}" for t, cs in self._inferred.items() for c in cs if not self.needs
        ]
        inferred += [
            f"SUM of `{i.what}` {_sum_assumed(i)}"
            if _sum(i)
            else f"`{i.shown or i.expr}` {FINITE_ASSUMED}"
            for i in self._assumed()
        ]
        rows += [f"| hint | {h.replace('|', '\\|')} |" for h in self._all_hints()]
        facts = [f"| `{n}` | {v} |" for n, v in self.facts.items()]
        if self.rows is not None:
            facts.insert(0, f"| (rows) | at most {self.rows:,} |")
        note = [f"**{self.verdict}**", ""]
        note += [] if self.deterministic else [f"> ⚠️ {self._ties_hint()}", ""]
        if self._params:
            note += [f"> ℹ️ {PARAMS_NOTE}: {', '.join(self._params)}", ""]
        if inferred:
            note += [f"> ℹ️ assumed (inferred): {', '.join(inferred)}", ""]
        note += [f"> semantics: {self.semantics}", ""]
        return "\n".join(
            [
                *note,
                "| postcondition | status |",
                "|---|---|",
                *rows,
                "",
                "| output column | known values |",
                "|---|---|",
                *facts,
            ]
        )


_REPORT_INTERNAL = [
    "windows_total",
    "tie_places",
    "guard_free",
    "unchecked",
    "optimized",
    "rewrites",
    "inferred",
    "implied",
    "params",
    "hints",
    "bounds",
    "relations",
    "stated",
    "floats_on",
    "depends",
    "contract",
    "transfer",
    "epsilon",
    "rows_exact",
    "conditions",
    "dialect",
    "on_inferred",
    "inferred_from",
    "postconditions",
]
"""`Report`'s fields that are internal (B4 of the 1.0 API review): each has
an underscore, and its old name reads it with a `DeprecationWarning` for a
release. `plan` is `internal_plan`."""


_deprecated.add(Report, {**{old: "_" + old for old in _REPORT_INTERNAL}, "plan": "internal_plan"})


def _would_hold(c: CheckedCondition) -> str:
    """The suggestion line of an unproved postcondition."""
    parts = [
        f"{', '.join(f'`{label(x)}`' for x in cs)} in the requires of {t!r}"
        for t, cs in c.suggested.items()
    ]
    return "would hold with " + " and ".join(parts)


PARAMS_NOTE = "proved for these parameter values only"

#: How a report marks a postcondition `on_unproved="check"` checks on data.
DATA_CHECK = "checked on the output data"

#: The functions whose order of ties is open, in each input language.
_ORDERED = {
    "ibis": "first(), last(), group_concat(), mode(), argmin() or argmax()",
    "sql": "FIRST, LAST, STRING_AGG, MODE, ARG_MIN or ARG_MAX",
}

TIES_HINT = (
    "rows may tie in the ORDER BY of a window, of a LIMIT or of {}, so the engine "
    "decides their order and a rerun may give other rows. The postconditions are "
    "proved for every order"
)


class VerificationError(SverifyError):
    """A postcondition, or the absence of runtime errors, could not be proved.

    Import it from `sverify.errors`. The message's first line counts what
    is missing; then one line per finding: each needed precondition, each
    unproved postcondition with what the checker established about it, and
    each possible runtime error with its hint. `report` holds the rest.

    Attributes:
        report: The `Report` of the failed proof.
    """

    def __init__(self, report: Report):
        self.report = report
        super().__init__(error_text(report))


def error_text(report: Report) -> str:
    """A `VerificationError`'s message (#687): what is missing, counted, and
    one line per finding with its hint, each hint once; `e.report` has the
    full report."""
    lines = [f"{', '.join(report._counts())} (e.report has the details)"]
    lines += [f"  needs: {n}" for n in report._needs_lines()]
    for c in report.ensures:
        if not c.proved:
            line = f"  not proved: {c.label}: {c.why}"
            if c.counterexample is not None:
                line += f" (counterexample: {c.counterexample})"
            lines.append(line)
            if c.suggested:
                lines.append(f"    {_would_hold(c)}")
        elif c.ignores:
            lines.append(f"  not proved: {c.label}: {_observation.why(c.ignores)}")
    hints: list[str] = []
    for i in report.errors:
        lines.append(f"  may fail: {i.message}")
        if i.hint and i.hint not in hints:
            hints.append(i.hint)
            lines.append(f"    hint: {i.hint}")
    lines += [f"  hint: {h}" for h in report._all_hints() if h not in hints]
    lines += [f"  {_transfer_failure(f)}" for f in report._transfer or ()]
    if report.floats_unmet:
        lines.append(f"  doubles: {report.floats_unmet}")
    return "\n".join(lines)


class UnverifiedRunError(VerificationError, RouteError):
    """A run or refresh of a plan that is not proved, refused (#690).

    Import it from `sverify.errors`. It is a `VerificationError`, so
    `except VerificationError` catches every "not proved", and a
    `RouteError`, as the refusal was before 0.6. `run(..., unverified=True)`
    or `refresh(unverified=True)` runs the plan anyway, and
    `transform(on_unproved="warn")` makes a node's refreshes do so.

    Attributes:
        report: The `Report` that is not proved.
        route: The refused `Route`, whose `reason` says what was not proved.
    """

    def __init__(self, report: Report, route: Route):
        self.report = report
        self.route = route
        Exception.__init__(self, f"refused on {route.engine}: {route.reason}")


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


class PostconditionError(SverifyError):
    """Output data violates a postcondition (only raised by runtime checks).

    Import it from `sverify.errors`. Raised with `on_unproved="check"`,
    when a postcondition the checker could not prove fails on the output rows. The
    message says how many output rows violate which condition.
    """


# Doubles, timestamps and dates are integer codes in the Lean model
# (SubstraitLean/Float.lean). A double with magnitude m = |x| * 2^1074 has
# code ±(2m + 1), and zero (-0.0 too) has code 0, which orders codes like SQL
# engines order doubles (-inf < ... < 0.0 < ... < +inf < NaN, one NaN).
# Timestamps are microseconds, dates days.
MAX_MAG = (2**53 - 1) * 2**2045
INF_MAG, NAN_MAG = MAX_MAG + 1, MAX_MAG + 2


def decode_double(code: int) -> float:
    """The double of a code (`FloatCode.toFloat`): zero is `0`, NaN the one NaN."""
    if code == 0:
        return 0.0
    sign = -1.0 if code < 0 else 1.0
    mag = (abs(code) - 1) // 2
    if mag >= NAN_MAG:
        return math.nan
    if mag == INF_MAG:
        return sign * math.inf
    return sign * float(Fraction(mag, 2**1074))


_EPOCH_DAY = date(1970, 1, 1)
_MICROSECOND = timedelta(microseconds=1)


def render_fact(abstract: dict, dtype: Any) -> str | None:
    """Describe a column's abstract value for doubles, decimals (their unscaled
    integers, #250), timestamps, dates and intervals (microseconds); None
    keeps Lean's own description."""
    rng = abstract.get("int")
    span: tuple[int, int] | None = None
    if (dec := abstract.get("decimal")) is not None:
        # The plan's own type, which Lean states: Ibis may type a decimal
        # product at another scale than the model computes it.
        scale = dec["scale"]
        # The wider precision: the plan may declare more digits than the model
        # needs (DuckDB's SUM is DECIMAL(38, s)), or fewer (Ibis types `a + a`
        # at `a`'s), and the model computes exactly.
        same = dtype.is_decimal() and dtype.scale == scale and dtype.precision is not None
        precision = max(dtype.precision, dec["precision"]) if same else dec["precision"]
        show = lambda k: f"{Decimal(k).scaleb(-scale):.{scale}f}"  # noqa: E731
        noun = f"a decimal({precision}, {scale})"
    elif dtype.is_floating():
        show: Callable[[int], str] = lambda k: repr(decode_double(k))  # noqa: E731
        noun = "a double"
    elif dtype.is_timestamp():
        epoch = datetime(1970, 1, 1)
        span = (datetime.min - epoch) // _MICROSECOND, (datetime.max - epoch) // _MICROSECOND
        show = lambda k: (  # noqa: E731
            (epoch + timedelta(microseconds=k)).isoformat(sep=" ")
            if span[0] <= k <= span[1]
            else f"{k:+} µs from 1970-01-01"
        )
        noun = "a timestamp"
    elif dtype.is_date():
        span = (date.min - _EPOCH_DAY).days, (date.max - _EPOCH_DAY).days
        show = lambda k: (  # noqa: E731
            (_EPOCH_DAY + timedelta(days=k)).isoformat()
            if span[0] <= k <= span[1]
            else f"{k:+} days from 1970-01-01"
        )
        noun = "a date"
    elif dtype.is_interval():
        show = lambda k: str(timedelta(microseconds=k))  # noqa: E731
        noun = "an interval"
    else:
        return None
    parts = []
    if rng is not None:
        lo = None if rng["lo"] is None else int(rng["lo"])
        hi = None if rng["hi"] is None else int(rng["hi"])
        if not dtype.is_floating():
            # Bounds near the 64-bit limits go without saying (as in Lean's text).
            lo = None if lo is not None and lo <= -(2**60) else lo
            hi = None if hi is not None and hi >= 2**60 else hi
        if span is not None:
            # So do bounds past what a Python date or datetime holds, the years
            # 1 to 9999: a DATE cast from a TIMESTAMP reaches far beyond (#435).
            lo = None if lo is not None and lo < span[0] else lo
            hi = None if hi is not None and hi > span[1] else hi
        if lo is None and hi is None:
            parts.append(f"any {noun.split(' ', 1)[1]}")
        elif lo is not None and hi is not None and lo == hi:
            parts.append(f"{noun} = {show(lo)}")
        elif dtype.is_floating():
            # Codes are 0 and odd numbers of magnitude 3 or more; a bound
            # between two codes reads best against its neighbour, zero first.
            def valid(k: int) -> bool:
                return k == 0 or (k % 2 == 1 and abs(k) >= 3)

            def up(k: int) -> int:
                """The smallest code ≥ k."""
                return k if valid(k) else 0 if k in (-2, -1) else 3 if k in (1, 2) else k + 1

            def down(k: int) -> int:
                """The largest code ≤ k."""
                return k if valid(k) else 0 if k in (1, 2) else -3 if k in (-2, -1) else k - 1

            def ge(k: int) -> str:
                n = up(k)
                return f"≥ {show(n)}" if n in (k, 0) else f"> {show(down(k - 1))}"

            def le(k: int) -> str:
                p = down(k)
                return f"≤ {show(p)}" if p in (k, 0) else f"< {show(up(k + 1))}"

            if hi is None:
                parts.append(f"{noun} {ge(lo)}")  # type: ignore[arg-type]
            elif lo is None:
                parts.append(f"{noun} {le(hi)}")
            else:
                parts.append(f"{noun} {ge(lo)} and {le(hi)}")
        elif hi is None:
            parts.append(f"{noun} ≥ {show(lo)}")  # type: ignore[arg-type]
        elif lo is None:
            parts.append(f"{noun} ≤ {show(hi)}")
        else:
            parts.append(f"{noun} in [{show(lo)}, {show(hi)}]")
    if abstract.get("null"):
        parts.append("NULL")
    return " or ".join(parts) if parts else "nothing (no rows)"


def _code_literal(dtype: Any, code: int) -> str | None:
    """The SQL literal of a value Lean codes as the integer `code`, for the
    types whose order is the order of their codes: integers, dates (days)
    and timestamps without a time zone (microseconds). None for the rest."""
    try:
        if dtype.is_integer():
            return str(code)
        if dtype.is_date():
            return f"DATE '{(_EPOCH + timedelta(days=code)).date().isoformat()}'"
        if dtype.is_timestamp() and dtype.timezone is None and dtype.scale in (None, 6):
            ts = _EPOCH + timedelta(microseconds=code)
            return f"TIMESTAMP '{ts.isoformat(sep=' ', timespec='microseconds')}'"
    except OverflowError:
        return None
    return None


_INT64_ENDS = (-(2**63), 2**63 - 1)


def _implied_sql(raw: Sequence[dict], schemas: Mapping[str, Any]) -> dict[str, str]:
    """The implied predicates of Lean's report as SQL, per table: the
    disjunction of each abstract row's column bounds. A bound on a type
    without an order-preserving literal is left out, which only weakens the
    condition; a table where some abstract row keeps no bound gets none."""
    out: dict[str, str] = {}
    for entry in raw:
        schema = schemas.get(entry["table"])
        if schema is None:
            continue
        names = list(schema.names)
        disjuncts = []
        for bounds in entry["any"]:
            conj = []
            for b in bounds:
                col = names[b["col"]]
                ref = '"' + col.replace('"', '""') + '"'
                for op, v in ((">=", b["lo"]), ("<=", b["hi"])):
                    if v is None or (schema[col].is_integer() and int(v) in _INT64_ENDS):
                        continue  # no bound, or only the type's own range
                    lit = _code_literal(schema[col], int(v))
                    if lit is not None:
                        conj.append(f"{ref} {op} {lit}")
            if not conj:
                break
            disjuncts.append(" AND ".join(conj))
        else:
            if disjuncts:
                out[entry["table"]] = " OR ".join(f"({d})" for d in disjuncts)
    return out


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


@dataclass(frozen=True)
class Needed:
    """A precondition a proof needs that `requires` does not state: a bound
    on one input column. `Report.needs` lists those the proof needs
    (`on_inferred="error"` does not assume them), `Issue.needs` those that
    rule out one runtime error, and `Report.suggestions` those under which
    an unproved postcondition would be proved."""

    table: str
    """The input table."""
    column: str | None
    """The input column it is on."""
    op: str | None
    """`>=`, `>`, `<=`, `<`, `<>` or `IS NOT NULL`; None if it is none of
    these."""
    value: str | None
    """The bound, as a SQL literal (`9000000000000000000`,
    `TIMESTAMP '2000-01-01 00:00:00'`); None for `IS NOT NULL`."""
    sql: str
    """The whole condition as DuckDB's SQL, NULL passing where the column
    is nullable: `"qty" IS NULL OR "qty" < 9000000000000000000`."""
    label: str
    """The condition as `Report.needed` lists it: `(_.qty < 9 * 10**18)`."""
    code: str
    """The condition as the Python a user writes in `requires`, for an
    editor's quick fix: `_.qty < 9 * 10**18`, `_.qty != 0`,
    `_.qty.notnull()`. `sql` is the form for a SQL contract."""
    issue: Issue | None
    """The runtime error it rules out, and where; None where it rules out
    none (a suggestion for a postcondition) or is the `Issue`'s own."""
    condition: Condition | None = None
    """The condition, ready for `requires=`: an Ibis deferred for an Ibis
    transform (`_.qty < 9 * 10**18`, or `_.qty.isnull() | (_.qty < 9 * 10**18)`
    where `qty` may be NULL, as the bound lets NULL pass), `sql` for a SQL
    one or where the bound has no Ibis form (an Ibis transform reads SQL
    conditions too)."""
    text: str = ""
    """The precondition in words: where it comes from, and the fixes."""


def _deterministic_arg(
    where: str, deterministic: bool | None, reproducible: Observation | None
) -> Observation | None:
    """`reproducible`, with the deprecated `deterministic=True` (B5 of the
    1.0 API review) read as `sv.equivalent()`."""
    if deterministic is None:
        return reproducible
    warnings.warn(
        f"{where}(deterministic=...) is deprecated; write reproducible=sv.equivalent() "
        "(Report.deterministic stays as the fact)",
        DeprecationWarning,
        stacklevel=3,
    )
    if deterministic and reproducible is None:
        return _observation.Observation()
    return reproducible


def _needed(
    table: str,
    c: Condition,
    dialect: str,
    issue: Issue | None = None,
    text: str = "",
) -> Needed:
    """A `Needed` for the condition `c` on `table`: an `Inferred` bound, or
    a label where the bound is not at hand."""
    lab = label(c)
    column = getattr(c, "column", None)
    op, value = c.parts() if isinstance(c, Inferred) else (None, None)
    sql = str(c) if isinstance(c, str) else lab
    n = Needed(table, column, op, value, sql, lab, _unparen(lab), issue, text=text)
    cond = _needed_deferred(n) if dialect == "ibis" else None
    return replace(n, condition=cond if cond is not None else n.sql)


def _labels_by_table(needs: Sequence[Needed]) -> dict[str, tuple[str, ...]]:
    """The labels of `needs` per input table, in order."""
    out: dict[str, tuple[str, ...]] = {}
    for n in needs:
        out[n.table] = (*out.get(n.table, ()), n.label)
    return out


def _sql_value(value: str) -> Any:
    """The Python value of a SQL literal `Needed.value` gives: an integer,
    a double, a decimal, a date or a timestamp; None for anything else."""
    if re.fullmatch(r"-?\d+", value):
        return int(value)
    if re.fullmatch(r"-?\d+\.\d+", value):
        return Decimal(value)
    try:
        if (m := re.fullmatch(r"DATE '(.+)'", value)) is not None:
            return date.fromisoformat(m[1])
        if (m := re.fullmatch(r"TIMESTAMP '(.+)'", value)) is not None:
            return datetime.fromisoformat(m[1])
        x = float(value)
    except ValueError:
        return None
    return x if math.isfinite(x) else None


def _needed_deferred(n: Needed) -> Deferred | None:
    """`n` as an Ibis deferred, letting NULL pass where its SQL does; None
    where it has no such form."""
    if n.column is None or n.op is None:
        return None
    col: Any = ibis._[n.column]
    if n.op == "IS NOT NULL":
        return col.notnull()
    v = _sql_value(n.value or "")
    if v is None:
        return None
    ops_ = {">=": col >= v, ">": col > v, "<=": col <= v, "<": col < v, "<>": col != v}
    cmp = ops_[n.op]
    nulls = '"' + n.column.replace('"', '""') + '" IS NULL OR '
    return col.isnull() | cmp if n.sql.startswith(nulls) else cmp


def _nice(x: int, up: bool) -> tuple[int, str]:
    """A round number near `x`, at or above it if `up`, else at or below,
    and how to write it: `2**62`, `3 * 10**18` or `1_000`."""
    if x < 0:
        v, text = _nice(-x, not up)
        return -v, f"-{text}" if v else "0"
    if x < 10**6:
        return x, f"{x:_}"
    k = x.bit_length() - 1
    two = 2 ** (k + 1 if up and 2**k < x else k)
    e = len(str(x)) - 1
    d = x // 10**e + (1 if up and x % 10**e else 0)
    ten = d * 10**e
    better = min if up else max
    v = better(two, ten)
    if v == two:
        return v, f"2**{v.bit_length() - 1}"
    d, e = (v // 10**e, e) if v // 10**e < 10 else (1, e + 1)
    return v, (f"10**{e}" if d == 1 else f"{d} * 10**{e}")


_EPOCH = datetime(1970, 1, 1)
_US_MIN = (datetime.min - _EPOCH) // timedelta(microseconds=1)
_US_MAX = (datetime.max - _EPOCH) // timedelta(microseconds=1)


def _year_of(code: int, per_year_unit: timedelta) -> int:
    """The year of a timestamp (microseconds) or date (days) code, clamped to
    Python's years."""
    us = code * (per_year_unit // timedelta(microseconds=1))
    if us < _US_MIN:
        return 1
    if us > _US_MAX:
        return 9999
    return (_EPOCH + timedelta(microseconds=us)).year


def _bound_conditions(col: str, dtype: Any, lo: int | None, hi: int | None) -> list[Inferred]:
    """`lo <= col <= hi` as conditions, rounded inward to round numbers (or
    whole years), each side its own condition. Empty for a type the
    inference does not write bounds for."""
    ref = f"_.{col}" if col.isidentifier() else f"_[{col!r}]"
    sql = '"' + col.replace('"', '""') + '"'
    # NULL cannot overflow, so a bound lets it pass.
    null = f"{sql} IS NULL OR " if dtype.nullable else ""
    out = []
    if dtype.is_integer():
        # A side at or past 64 bits holds for every integer column, and its
        # constant (2**63) would be a HUGEINT, which the lift refuses (#616).
        # A narrower column's own limits stay, the proof needs them stated,
        # each a constant of the column's type, so it is a fact about the
        # column (`v <= 127` on a TINYINT, not `v < 128`).
        if lo is not None and lo <= -(2**63):
            lo = None
        if hi is not None and hi >= 2**63 - 1:
            hi = None
        if lo is not None:
            if lo <= dtype.bounds.lower:
                v, text = dtype.bounds.lower, f"{dtype.bounds.lower:_}"
            else:
                v, text = _nice(lo, up=True)
            out.append(Inferred(f"{null}{sql} >= {v}", f"({ref} >= {text})"))
        if hi is not None:
            if hi >= dtype.bounds.upper:
                top = dtype.bounds.upper
                out.append(Inferred(f"{null}{sql} <= {top}", f"({ref} <= {top:_})"))
            else:
                v, text = _nice(hi + 1, up=False)
                out.append(Inferred(f"{null}{sql} < {v}", f"({ref} < {text})"))
        return out
    if dtype.is_floating():
        return _double_conditions(ref, sql, null, lo, hi)
    if dtype.is_decimal() and dtype.scale is not None:
        scale = dtype.scale

        def dec(k: int) -> str:
            return f"{Decimal(k).scaleb(-scale):.{scale}f}"

        # Large bounds as round whole numbers (`5 * 10**35`), small ones exactly.
        if lo is not None:
            if abs(lo) >= 10 ** (scale + 6):
                v, text = _nice(-((-lo) // 10**scale), up=True)
                out.append(Inferred(f"{null}{sql} >= {dec(v * 10**scale)}", f"({ref} >= {text})"))
            else:
                out.append(Inferred(f"{null}{sql} >= {dec(lo)}", f"({ref} >= {dec(lo)})"))
        if hi is not None:
            if abs(hi) >= 10 ** (scale + 6):
                v, text = _nice(hi // 10**scale + 1, up=False)
                out.append(Inferred(f"{null}{sql} < {dec(v * 10**scale)}", f"({ref} < {text})"))
            else:
                out.append(Inferred(f"{null}{sql} <= {dec(hi)}", f"({ref} <= {dec(hi)})"))
        return out
    if dtype.is_timestamp() and dtype.timezone is None:
        unit, kind, py = timedelta(microseconds=1), "TIMESTAMP", "datetime"
    elif dtype.is_date():
        unit, kind, py = timedelta(days=1), "DATE", "date"
    else:
        return []

    def code(year: int) -> int:
        return (datetime(year, 1, 1) - _EPOCH) // unit

    def lit(year: int) -> str:
        day = date(year, 1, 1)
        return f"{kind} '{day.isoformat()}{' 00:00:00' if kind == 'TIMESTAMP' else ''}'"

    if lo is not None:
        y = _year_of(lo, unit)
        if code(y) < lo:
            y += 1
        out.append(Inferred(f"{null}{sql} >= {lit(y)}", f"({ref} >= {py}({y}, 1, 1))"))
    if hi is not None:
        y = _year_of(hi + 1, unit)
        out.append(Inferred(f"{null}{sql} < {lit(y)}", f"({ref} < {py}({y}, 1, 1))"))
    return out


# Codes of the smallest positive and the largest finite double.
_TINY_CODE = 1
_MAX_CODE = 2 * MAX_MAG + 1


def _double_conditions(
    ref: str, sql: str, null: str, lo: int | None, hi: int | None
) -> list[Inferred]:
    """`lo <= col <= hi` on double codes: `> 0` for the smallest positive
    double, round powers of two near ±2⁶³ (a cast to BIGINT), and the
    decoded doubles otherwise."""

    def num(x: float) -> str:
        if x.is_integer() and abs(x) >= 1e6:
            return _nice(int(x), up=x < 0)[1]
        return repr(x)

    out = []
    if lo is not None:
        if lo == _TINY_CODE:
            out.append(Inferred(f"{null}{sql} > 0", f"({ref} > 0)"))
        elif lo > -_MAX_CODE:
            x = decode_double(lo)
            out.append(Inferred(f"{null}{sql} >= {x!r}", f"({ref} >= {num(x)})"))
        else:
            x = decode_double(-_MAX_CODE)
            out.append(Inferred(f"{null}{sql} >= {x!r}", f"({ref} >= {x!r})"))
    if hi is not None:
        nxt = decode_double(hi + 1)
        if hi < _MAX_CODE and nxt.is_integer() and abs(nxt) >= 1e6:
            # Just below a round number: `< 2**63`.
            out.append(Inferred(f"{null}{sql} < {nxt!r}", f"({ref} < {num(nxt)})"))
        else:
            x = decode_double(min(hi, _MAX_CODE))
            out.append(Inferred(f"{null}{sql} <= {x!r}", f"({ref} <= {x!r})"))
    return out


def _ne_condition(col: str, dtype: Any, k: int) -> Inferred | None:
    """`col != k`, for a code `k` of the column's type (a divisor's 0)."""
    ref = f"_.{col}" if col.isidentifier() else f"_[{col!r}]"
    sql = '"' + col.replace('"', '""') + '"'
    null = f"{sql} IS NULL OR " if dtype.nullable else ""
    if dtype.is_integer():
        v = str(k)
    elif dtype.is_floating():
        v = repr(decode_double(k))
    elif dtype.is_decimal() and dtype.scale is not None:
        v = f"{Decimal(k).scaleb(-dtype.scale):.{dtype.scale}f}"
    else:
        return None
    return Inferred(f"{null}{sql} <> {v}", f"({ref} != {v})")


def _not_null_condition(col: str) -> Inferred:
    """`col IS NOT NULL` (a divisor's `COUNT` of the column)."""
    ref = f"_.{col}" if col.isidentifier() else f"_[{col!r}]"
    sql = '"' + col.replace('"', '""') + '"'
    return Inferred(f"{sql} IS NOT NULL", f"{ref}.notnull()")


def _suggested(
    bound: dict | None, schemas: Mapping[str, ibis.Schema], assumable: Container[str]
) -> dict[str, list[Condition]]:
    """The preconditions Lean suggests for an unproved postcondition, on the
    tables whose `requires` the caller states; none for a split or a why."""
    if bound is None or bound["why"] is not None or bound["split"]:
        return {}
    conds = _render_needs(bound["needs"], schemas)
    return {t: list[Condition](cs) for t, cs in conds.items() if t in assumable and cs}


def _render_needs(
    needs: Sequence[dict], schemas: Mapping[str, ibis.Schema]
) -> dict[str, list[Inferred]]:
    """The conditions of a list of `{table, col, lo, hi}`, `{table, col,
    ne}` or `{table, col, not_null}` (column positions, integer codes as
    strings), per table."""
    out: dict[str, list[Inferred]] = {}
    for n in needs:
        schema = schemas.get(n["table"])
        if schema is None or n["col"] >= len(schema):
            continue
        col = list(schema)[n["col"]]
        have = out.setdefault(n["table"], [])
        if n.get("not_null"):
            new = [_not_null_condition(col)] if schema[col].nullable else []
        elif "ne" in n:
            c = _ne_condition(col, schema[col], int(n["ne"]))
            new = [] if c is None else [c]
        else:
            lo, hi = (None if n[k] is None else int(n[k]) for k in ("lo", "hi"))
            new = _bound_conditions(col, schema[col], lo, hi)
        for c in new:
            c.column = col
        have += [c for c in new if c not in have]
    return {t: cs for t, cs in out.items() if cs}


def _why_hint(why: str, show: Callable[[str], str]) -> str:
    """Why no bound on an input column rules an issue out, from the
    inference's reason (`SubstraitLean/Infer.lean`), in the user's terms."""
    m = re.fullmatch(r"it divides by (.+), which the inference does not look into", why)
    if m and re.fullmatch(r"-?0(\.0*)?d?", m[1]):
        return "it divides by the constant 0, so every row it reaches raises: change the divisor"
    m = re.fullmatch(r"(it divides by|it reads|its base is) (.+)(, which .*)", why)
    if m:
        why = f"{m[1]} `{show(m[2])}`{m[3]}"
    return f"sverify found no bound on an input column that rules it out: {why}"


def _hint(
    bound: dict | None,
    schemas: Mapping[str, ibis.Schema],
    assumable: Container[str],
    show: Callable[[str], str] = lambda e: e,
) -> str | None:
    """What a report suggests for one overflow, from what the inference
    found (`SubstraitLean/Infer.lean`)."""
    if bound is None:
        return None
    if bound["why"] is not None:
        return _why_hint(bound["why"], show)
    conds = _render_needs(bound["needs"], schemas)
    if not conds:
        return None

    def code(cs: Sequence[Inferred]) -> str:
        return ", ".join(f"`{label(c)}`" for c in cs)

    parts = []
    for t, cs in conds.items():
        if t in assumable:
            parts.append(f"{code(cs)} in the requires of {t!r}")
        else:
            parts.append(f"{code(cs)} in the ensures of {t!r}")
    lead = "no single bound rules it out; for example, state " if bound["split"] else "state "
    return lead + " and ".join(parts)


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


def column_names(schema: ibis.Schema) -> list[str]:
    return [name for name, _ in schema.items()]


def leaf_tables(expr: ir.Table) -> dict[str, ibis.Schema]:
    leaves = expr.op().find((ops.UnboundTable, ops.DatabaseTable))
    return {t.name: t.schema for t in leaves if isinstance(t, ops.UnboundTable | ops.DatabaseTable)}


def resolve(cond: Condition, table: ir.Table) -> ir.BooleanValue:
    if isinstance(cond, Deferred):
        return cond.resolve(table)
    if callable(cond):
        return cond(table)
    return cond  # type: ignore[return-value]


def bind_params(expr: ir.Table, params: Mapping[ir.Scalar, Any]) -> ir.Table:
    """`expr` with each `ibis.param` in `params` replaced by its value, a
    literal of the parameter's type (#58), as Ibis's `execute(params=...)`
    binds them.

    Raises:
        TypeError: A key is not an `ibis.param`, or a value does not fit its
            type.
    """
    mapping: dict[Any, Any] = {}
    for p, value in params.items():
        op = p.op() if isinstance(p, ir.Expr) else None
        if not isinstance(op, ops.ScalarParameter):
            raise TypeError(f"params keys must be ibis.param expressions, not {p!r}")
        try:
            lit = ibis.literal(value, type=op.dtype)
        except Exception as e:  # noqa: BLE001 - Ibis raises several kinds
            raise TypeError(f"{value!r} is not a value of the parameter's type {op.dtype}") from e
        mapping[op] = lit.op()
    return expr.op().replace(mapping).to_expr()


def condition_query(table: Transform, cond: Condition, semantics: str = "reference") -> Transform:
    """A query selecting one condition column from a table or transformation:
    SQL for a SQL condition on a SQL transformation, an Ibis expression
    otherwise (a SQL condition on an Ibis table is a SQL model over it, with
    `semantics`)."""
    if isinstance(cond, str):
        query = f'SELECT ({cond}) AS "c" FROM {{}} AS "t"'
        if isinstance(table, str):
            return query.format(f"({table})")
        from sverify.ibis_substrait import SQLModel, Unsupported, sql_model_schema

        query = query.format('"t"')
        try:
            schema = sql_model_schema(query, {"t": table.schema()}, semantics)
        except Unsupported as e:
            raise Unsupported(f"condition {cond!r}: {e}") from e
        return SQLModel(query, (table.op(),), ("t",), schema, "duckdb", semantics).to_expr()
    if isinstance(table, str):
        raise TypeError("Ibis conditions need an Ibis transformation; use a SQL string instead")
    return table.select(c=resolve(cond, table))


def requires_by_input(
    requires: Mapping[str, Sequence[Condition]] | Sequence[Condition] | None,
    inputs: Sequence[str],
    kind: str = "table",
    error: type[Exception] = ValueError,
) -> dict[str, Sequence[Condition]]:
    """`requires` as a mapping from input to its conditions (#408). A plain
    list is the conditions on the only input; a key that names no input
    raises `error`, naming the key, the inputs and a close match."""
    if requires is None:
        return {}
    if not isinstance(requires, Mapping):
        conds: list[Any] = (
            [requires] if isinstance(requires, str | TableCondition | Key) else list(requires)
        )
        if len(inputs) != 1:
            raise error(
                f"requires: a list of conditions needs exactly one input {kind}, and there "
                f"are {len(inputs)} ({', '.join(inputs) or 'none'}); key them by {kind}, "
                "as requires={name: [...]}"
            )
        return {inputs[0]: expand_keys(conds)}
    for key in requires:
        if key in inputs:
            continue
        lower = {i.lower(): i for i in inputs}
        close = [lower[k] for k in difflib.get_close_matches(str(key).lower(), lower, n=1)]
        hint = f"; did you mean {close[0]!r}?" if close else ""
        raise error(
            f"requires: unknown {kind} {key!r}; the inputs are: {', '.join(inputs) or 'none'}"
            + hint
        )
    return {t: expand_keys(cs) for t, cs in requires.items()}


def default_counterexamples() -> int:
    """How many inputs `verify`, a transform's call and
    `ContractedTransform.check` try per unproved postcondition when not told:
    the `SVERIFY_COUNTEREXAMPLES` environment variable, else 200. An editor
    or a CI step that only needs the verdicts sets it to 0."""
    raw = os.environ.get("SVERIFY_COUNTEREXAMPLES", "").strip()
    if not raw:
        return 200
    try:
        n = int(raw)
    except ValueError:
        raise ValueError(f"SVERIFY_COUNTEREXAMPLES must be an integer, not {raw!r}") from None
    if n < 0:
        raise ValueError(f"SVERIFY_COUNTEREXAMPLES must be 0 or more, not {n}")
    return n


def verify(
    query: Transform,
    /,
    *,
    requires: Mapping[str, Sequence[Condition]] | Sequence[Condition] | None = None,
    ensures: Sequence[Condition] = (),
    tables: Mapping[str, ibis.Schema | ir.Table] | None = None,
    counterexamples: int | None = None,
    params: Mapping[ir.Scalar, Any] | None = None,
    semantics: Semantics | None = None,
    on_inferred: OnInferred = "error",
    infer: bool | None = None,
) -> Report:
    """Try to prove `ensures` about `query` (an Ibis table expression or a
    SQL query) from `requires`, a mapping from table name to conditions.

    `tables` gives the input schemas; it is only needed for SQL transforms.
    For each unproved postcondition, up to `counterexamples` small inputs are
    tried for one that breaks it (`sverify.counterexample`); 0 skips that.

    A proof is about the plan `transform` compiles to, under `Rel.eval`. An
    Ibis expression compiles with sverify's own producer, so it means what
    `docs/ibis-semantics.md` says, whichever Ibis backend it came from; where
    Ibis backends disagree (`%` on Polars, `-0.0 == 0.0` on DataFusion, …),
    no backend's `execute` is guaranteed to match. `sverify.engines.run`
    runs the verified plan with that meaning (or fails) on DataFusion, DuckDB and
    Polars. A SQL string, and a SQL condition, is DuckDB's SQL, lifted by
    `sverify.sql_lift` with `semantics`: the reference semantics by default,
    or what DuckDB computes with `semantics="duckdb"` (#411). The report
    says which (`Report.semantics`).

    Unlike `transform`, `verify` checks nothing on data and raises nothing
    when a postcondition is unproved: it returns the report.

    Args:
        transform: The transformation, as an Ibis table expression or a SQL
            query.
        requires: Preconditions, as a mapping from input table name to its
            conditions (Ibis expressions, SQL snippets, `unique` or
            `references`), or, for a transformation with one input, a list
            of its conditions. They are assumed, not checked. Default: none.
        ensures: Postconditions on the output to prove, including `unique`
            keys. Default: none, which still reports the facts and possible
            runtime errors.
        tables: Input schemas by table name, as Ibis schemas, anything
            `ibis.schema` accepts, Ibis tables, or mappings of column names
            to DuckDB's type names (`{"id": "BIGINT", "name": "VARCHAR NOT
            NULL"}`, `input_schema`). Needed for SQL transforms; an Ibis
            expression's own tables are found from it.
        counterexamples: How many small inputs to try per unproved
            postcondition when searching for one that breaks it; 0 skips the
            search. Default: the `SVERIFY_COUNTEREXAMPLES` environment
            variable, else 200 (`default_counterexamples`).
        params: Values for the `ibis.param`s of an Ibis transform, as Ibis's
            `execute(params=...)` takes them. The report is about the
            transform with these values (`bind_params`); an unbound parameter
            is refused.
        semantics: What the SQL `verify` lifts means, the transformation
            if it is a SQL string and every SQL condition: `"reference"`
            (the default), sverify's reference semantics, where an
            operation that would create a NaN raises; or `"duckdb"`, what
            DuckDB computes, NaN and ±inf included. An `sv.sql` expression
            inside an Ibis transformation keeps its own `semantics`. Unstated
            (None), it is `"duckdb"` for a transformation whose SQL is all
            `sv.sql(..., semantics="duckdb")`, else `"reference"`.
            `"polars"` checks an Ibis transformation under Polars's
            profile (#444); the checker refuses it until it has one.
            `"substrait"` checks an Ibis transformation under Substrait's
            own semantics (`Profile.substrait`, #444): the proof under the
            reference holds there where Substrait allows nothing more at
            the options the plan meets, and `Report.transfer` names the
            options where it allows more.
        on_inferred: What a precondition sverify infers does. sverify
            infers the bounds on input columns that rule out integer
            overflow (`infer_bounds`: `amount * 2` on BIGINT needs
            `_.amount < 2**62`) and the `IS NOT NULL`s a postcondition
            needs (`Report.inferred`). `"error"` (the default): the plan is
            not proved without it, and the report says where it came from
            and how to state it (`Report.needed`). `"warn"`: it is assumed,
            checked on the data before each run, and a warning names it
            (`InferredPreconditionWarning`). `"ignore"`: it is assumed and
            checked without a warning. `"off"`: nothing is inferred or
            assumed, so an integer `SUM` that may leave 64 bits, or a double
            operation that may overflow to ±inf, is an error too, which the
            other values check on the data while the job runs
            (`Report.assumed`); each `Issue.hint` suggests a bound.
            `"silent"` is a deprecated spelling of `"ignore"`.
        infer: Deprecated: `infer=False` is `on_inferred="off"`.

    Returns:
        A `Report` with the status of each postcondition, the possible
        runtime errors, and what is known about each output column.

    Raises:
        ValueError: `requires` names an unknown table, `unique` or
            `references` names an unknown column or table, or the checker
            fails on the request (for example on a plan outside the Lean
            model).

    Examples:
        A SQL query (DuckDB's SQL), with its input schema:

        ```python
        import ibis
        import sverify as sv
        from ibis import _

        orders = ibis.table({"id": "int64", "amount": "int64"}, name="orders")

        report = sv.verify(
            "select id, amount from orders where amount > 0",
            tables={"orders": orders},
            ensures=["amount > 0"],
        )
        report.proved  # True
        ```

        An Ibis expression, with preconditions:

        ```python
        report = sv.verify(
            orders.select(orders.id, total=orders.amount + 1),
            requires={"orders": [_.amount >= 0]},
            ensures=[_.total >= 1],
        )
        report.facts["total"]  # 'an integer ≥ 1'
        ```
    """
    transform = query
    on_inferred = _folded_infer(on_inferred, infer, "verify")
    bound: list[str] = []
    if params:
        if isinstance(transform, str):
            raise TypeError("params bind the ibis.param values of an Ibis expression, not SQL")
        transform = bind_params(transform, params)
        bound = [
            f"param{k} ({p.type()}) = {v!r}" for k, (p, v) in enumerate(params.items(), start=1)
        ]
    inputs = list(tables or {})
    if not isinstance(transform, str):
        inputs += [t for t in leaf_tables(transform) if t not in inputs]
    if semantics is None:
        semantics = _expr_semantics(transform)
    return infer_bounds(
        transform,
        requires=requires_by_input(requires, inputs),
        ensures=expand_keys(ensures),
        tables=tables,
        counterexamples=default_counterexamples() if counterexamples is None else counterexamples,
        params=bound,
        infer=on_inferred != "off",
        semantics=_checked_semantics(semantics),
        on_inferred=on_inferred,
    )


def _unparen(code: str) -> str:
    """`code` without the one pair of parentheses around all of it."""
    if not (code.startswith("(") and code.endswith(")")):
        return code
    depth = 0
    for i, ch in enumerate(code):
        depth += {"(": 1, ")": -1}.get(ch, 0)
        if depth == 0 and i < len(code) - 1:
            return code
    return code[1:-1]


def input_schema(s: Any) -> ibis.Schema:
    """An input of `verify(tables=...)` as an Ibis schema: an Ibis table or
    schema, or a mapping of column names to types, each an Ibis type or
    type name (`"int64"`, `"!string"`) or DuckDB's (`"BIGINT"`, `"HUGEINT"`,
    `"VARCHAR NOT NULL"`), as `CREATE TABLE` and `DESCRIBE` write them."""
    if isinstance(s, ir.Table):
        return s.schema()
    if isinstance(s, ibis.Schema) or not isinstance(s, Mapping):
        return ibis.schema(s)
    return ibis.schema({c: _column_type(c, t) for c, t in s.items()})


def _column_type(col: str, t: Any) -> Any:
    """`t` as an Ibis type: Ibis's own names first, then DuckDB's."""
    if not isinstance(t, str):
        return t
    try:
        return ibis.dtype(t)
    except Exception:  # noqa: BLE001 - Ibis raises several kinds
        pass
    from ibis.backends.sql.datatypes import DuckDBType

    text = t.strip()
    m = re.fullmatch(r"(.*?)\s+NOT\s+NULL", text, re.IGNORECASE)
    unknown = ValueError(
        f"tables: column {col!r} has type {t!r}, which is neither an Ibis type nor one of DuckDB's"
    )
    try:
        dtype = DuckDBType.from_string(m[1] if m else text)
    except Exception as e:  # noqa: BLE001
        raise unknown from e
    if dtype.is_unknown():
        raise unknown
    return dtype.copy(nullable=not m)


def infer_bounds(
    transform: Transform,
    *,
    requires: Mapping[str, Sequence[Condition]],
    ensures: Sequence[Condition],
    tables: Mapping[str, ibis.Schema | ir.Table] | None,
    counterexamples: int,
    params: list[str],
    infer: bool = True,
    inputs: Collection[str] | None = None,
    semantics: Semantics = "reference",
    on_inferred: OnInferred = "ignore",
) -> Report:
    """`verify`, with the bounds that rule out overflow inferred (#244).

    Lean's `SubstraitLean/Infer.lean` runs the range analysis backwards: for
    each overflow it may not rule out, the range of each input column that
    does (`amount * 2` on BIGINT fits when `amount < 2**62`). Those bounds
    are candidates only. The ones on the tables in `assume` (all tables if
    None) are added to `requires`, rounded inward to round numbers, and the
    contract is proved again, as if the user had written them: a wrong bound
    makes that proof fail, never pass wrongly. For the rest, and for
    overflows without a unique bound (the product of two columns), the
    report's `Issue.hint` suggests one.

    `inputs` are the tables whose preconditions the caller states (None:
    all): their bounds are assumed with `infer`, and suggested for
    `requires`; bounds on other tables (results of other contracted
    transformations) are suggested for those tables' `ensures`.

    An observation in `ensures` (`sv.equivalent`) is no condition to prove:
    it goes to `Report.observation`, and each other postcondition that
    depends on what it ignores says so (`CheckedCondition.ignores`)."""
    observed, ensures = _observation.split(ensures)
    report = _infer_bounds(
        transform, requires, ensures, tables, counterexamples, params, infer, inputs, semantics
    )
    conditions = {t: list(cs) for t, cs in requires.items()}
    _merge(conditions, report._inferred)
    report._conditions = conditions
    opened = {} if report._windows_total or isinstance(transform, str) else _open_columns(transform)
    out = _observed(report, observed or _observation.PLAN_BOUND, ensures, opened)
    out._stated = observed is not None
    from sverify import routes as _routes

    if out.observation.floats == "plan":
        out.observation = replace(out.observation, bound=_routes.plan_bound(out._epsilon))
    else:
        out._floats_on = _routes.floats_on(out)
    out._on_inferred = _checked_on_inferred(on_inferred)
    if not out.deterministic and not isinstance(transform, str):
        out.ties = _confirmed_ties(transform, requires, out, tables, params, inputs, semantics)
    if on_inferred == "warn" and out._inferred:
        warnings.warn(
            "assumed inferred precondition(s): "
            + "; ".join(
                n.split(": declare")[0]
                for n in out._needs_lines(
                    {t: [label(c) for c in cs] for t, cs in out._inferred.items()}
                )
            ),
            InferredPreconditionWarning,
            stacklevel=3,
        )
    return out


OnInferred = Literal["error", "warn", "ignore", "off"]

OnUnproved = Literal["error", "check", "warn"]


class InferredPreconditionWarning(UserWarning):
    """A precondition sverify inferred is assumed (`on_inferred="warn"`)."""


def _checked_on_inferred(v: str) -> OnInferred:
    if v == "silent":
        warnings.warn(
            'on_inferred="silent" is deprecated; write on_inferred="ignore"',
            DeprecationWarning,
            stacklevel=4,
        )
        return "ignore"
    if v not in ("error", "warn", "ignore", "off"):
        raise ValueError(f"on_inferred must be 'error', 'warn', 'ignore' or 'off', not {v!r}")
    return v  # type: ignore[return-value]


def _checked_on_unproved(v: str) -> OnUnproved:
    """`on_unproved`, with the deprecated `"runtime"` read as `"check"`."""
    if v == "runtime":
        warnings.warn(
            'on_unproved="runtime" is deprecated; write on_unproved="check"',
            DeprecationWarning,
            stacklevel=3,
        )
        return "check"
    if v not in ("error", "check", "warn"):
        raise ValueError(f"on_unproved must be 'error', 'check' or 'warn', not {v!r}")
    return v  # type: ignore[return-value]


def _folded_infer(on_inferred: str, infer: bool | None, where: str) -> OnInferred:
    """`on_inferred`, with the deprecated `infer=` folded in (#690):
    `infer=False` is `on_inferred="off"`."""
    on_inferred = _checked_on_inferred(on_inferred)
    if infer is None:
        return on_inferred
    if infer:
        warnings.warn(
            f"{where}(infer=True) is deprecated: it is the default; drop it "
            f"(on_inferred={on_inferred!r} says what an inferred precondition does)",
            DeprecationWarning,
            stacklevel=3,
        )
        return on_inferred
    warnings.warn(
        f'{where}(infer=False) is deprecated; write on_inferred="off"',
        DeprecationWarning,
        stacklevel=3,
    )
    return "off"


def _observed(
    report: Report,
    observed: Observation,
    ensures: Sequence[Condition],
    opened: Mapping[str, str],
) -> Report:
    """`report` with the observation, and each postcondition marked with the
    components it depends on that the observation ignores, or that the plan
    leaves open (`opened`, D1, D12). A proved condition holds for every
    choice the plan leaves open, so only an unproved one is marked with
    those."""
    checked = [
        replace(
            c,
            reads=None if (r := _reads(cond, report.output)) is None else tuple(r),
            approx=isinstance(cond, Approx),
            nullable=None
            if r is None or any(c not in report.facts for c in r)
            else tuple(c for c in r if "NULL" in report.facts[c]),
            ignores=tuple(
                _observation.dependencies(
                    observed,
                    cond,
                    report.output,
                    _reads(cond, report.output),
                    {} if c.proved else opened,
                    _order_free(cond, report.output, opened),
                )
            ),
        )
        for cond, c in zip(ensures, report.ensures, strict=True)
    ]
    return replace(report, ensures=checked, observation=observed)


def _open_columns(expr: ir.Table) -> dict[str, str]:
    """The output columns of aggregates whose value the reference leaves
    open: `"picks"` for `first`, `last` or `arbitrary` without an order,
    `"elements"` for `collect` or `group_concat` without one."""
    out: dict[str, str] = {}
    for agg in expr.op().find(ops.Aggregate):
        if not isinstance(agg, ops.Aggregate):
            continue
        for name, metric in agg.metrics.items():
            if (
                isinstance(metric, ops.First | ops.Last)
                and not metric.order_by
                or isinstance(metric, ops.Arbitrary)
            ):
                out[name] = "picks"
            elif isinstance(metric, ops.ArrayCollect | ops.GroupConcat) and not metric.order_by:
                out[name] = "elements"
    names = set(expr.columns)
    return {n: why for n, why in out.items() if n in names}


#: Functions of a list that ignore the order of its elements.
_ORDER_FREE = (
    ops.ArrayLength,
    ops.ArrayContains,
    ops.ArrayMin,
    ops.ArrayMax,
    ops.ArraySum,
    ops.ArrayMean,
    ops.ArraySort,
    ops.ArrayDistinct,
    ops.ArrayAll,
    ops.ArrayAny,
)


def _order_free(cond: Condition, columns: Mapping[str, Any], opened: Mapping[str, str]) -> set[str]:
    """The open list columns `cond` reads only through functions that ignore
    the order of the elements."""
    lists = {n for n, why in opened.items() if why == "elements"}
    if not lists or isinstance(cond, str | TableCondition) or not columns:
        return set()
    if isinstance(cond, Approx):
        return _order_free(cond.cond, columns, opened)
    try:
        expr = resolve(cond, ibis.table(ibis.schema(dict(columns)), name="t"))
    except Exception:  # noqa: BLE001 - an unreadable condition reads every column
        return set()
    bare: set[str] = set()

    def walk(node: Any, guarded: bool) -> None:
        if isinstance(node, ops.Field):
            if not guarded:
                bare.add(node.name)
            return
        if isinstance(node, Node):
            inner = guarded or isinstance(node, _ORDER_FREE)
            for arg in node.__args__:
                for child in arg if isinstance(arg, tuple) else (arg,):
                    walk(child, inner)

    walk(expr.op(), False)
    read = set(_reads(cond, columns) or ())
    return {n for n in lists & read if n not in bare}


def _reads(cond: Condition, columns: Mapping[str, Any]) -> list[str] | None:
    """The output columns `cond` reads; None where that is not known."""
    if isinstance(cond, Unique | RowsPer):
        return list(cond.cols)
    if isinstance(cond, References | ArrivesWithin):
        return [cond.col]
    if isinstance(cond, MaxRows):
        return []
    if isinstance(cond, Approx):
        return _reads(cond.cond, columns)
    if isinstance(cond, str):
        import sqlglot
        from sqlglot import exp

        try:
            parsed = sqlglot.parse_one(cond, read="duckdb")
        except sqlglot.errors.ParseError:
            return None
        return [c.name for c in parsed.find_all(exp.Column)]
    if not columns:
        return None
    try:
        expr = resolve(cond, ibis.table(ibis.schema(dict(columns)), name="t"))
        return [f.name for f in expr.op().find(ops.Field) if isinstance(f, ops.Field)]
    except Exception:  # noqa: BLE001 - an unreadable condition reads every column
        return None


def _infer_bounds(
    transform: Transform,
    requires: Mapping[str, Sequence[Condition]],
    ensures: Sequence[Condition],
    tables: Mapping[str, ibis.Schema | ir.Table] | None,
    counterexamples: int,
    params: list[str],
    infer: bool,
    inputs: Collection[str] | None,
    semantics: Semantics,
) -> Report:
    def once(reqs: Mapping[str, Sequence[Condition]], n: int):
        return _verify_once(transform, reqs, ensures, tables, n, params, inputs, semantics)

    def finish(report: Report, schemas: Mapping[str, Any], widened) -> Report:
        """The reasons and hints each confirmed by a proof (#688)."""

        def proves(cond: Condition) -> bool:
            again = _verify_once(transform, widened, [cond], tables, 0, params, inputs, semantics)
            return all(e.proved for e in again[0].ensures)

        report = _confirm_suggestions(report, requires, once)
        report = _key_reasons(transform, report, requires, ensures, schemas, inputs, once)
        report = _null_reasons(transform, report, ensures, proves)
        return _confirm_hints(report, requires, once)

    if not infer:
        report, _raw, schemas = once(requires, counterexamples)
        return finish(report, schemas, requires)
    # Counterexamples only for the final proof.
    report, raw, schemas = once(requires, 0)
    extra = {
        t: cs for t, cs in _render_needs(raw, schemas).items() if inputs is None or t in inputs
    }
    if extra:
        guarded = and_or_hints(report.issues, transform)
        widened = {t: list(cs) for t, cs in requires.items()}
        _merge(widened, extra)
        first = report.issues
        report = once(widened, counterexamples)[0]
        report._inferred = {t: list[Condition](cs) for t, cs in extra.items()}
        report._inferred_from = {
            label(c): i
            for cs in extra.values()
            for c in cs
            for i in reversed(first)
            if label(c) in i._labels
        }
        # An inferred precondition that a guard under AND/OR would have made
        # unnecessary with a CASE (#604): say so.
        report._hints += [h for h in guarded if h not in report._hints]
    elif counterexamples and report.unproved:
        report = once(requires, counterexamples)[0]
    report = _null_preconditions(transform, report, requires, ensures, inputs, once)
    widened = {t: list(cs) for t, cs in requires.items()}
    _merge(widened, report._inferred)
    report = finish(report, schemas, widened)
    # A SUM that may overflow is assumed to fit, and an operation on finite
    # doubles to stay finite (#575), both checked on the data while the job
    # runs: the row caps (#219) and the bounds do not rule them out.
    report.assumed = [i for i in report.issues if _assumable(i)]
    report.issues = [i for i in report.issues if not _assumable(i)]
    return report


#: The kind an inferred `IS NOT NULL` names as its source (#655).
NULL_KIND = "a NULL result"


def _null_preconditions(
    transform: Transform,
    report: Report,
    requires: Mapping[str, Sequence[Condition]],
    ensures: Sequence[Condition],
    inputs: Collection[str] | None,
    once: Callable[..., Any],
) -> Report:
    """`report` with the `IS NOT NULL` preconditions that prove a
    postcondition failing only on NULL (`TRUE or NULL`), inferred like the
    bounds (#655): for each column it reads that passes on an input
    column, `_.<column>.notnull()` on that input, kept if the postcondition
    is then proved. A postcondition that may also be FALSE gets none."""
    if isinstance(transform, str):
        return report
    found: dict[str, list[Condition]] = {}
    source: dict[str, Issue] = {}
    by_label = {label(c): c for c in ensures if not isinstance(c, TableCondition)}
    root = transform.op()
    for c in report.ensures:
        cond = by_label.get(c.label)
        if c.proved or cond is None:
            continue
        if set(c.value.replace(" or ", ", ").split(", ")) != {"TRUE", "NULL"}:
            continue
        for t, base in _input_columns(root, _reads(cond, report.output) or []):
            if inputs is not None and t not in inputs:
                continue
            new = getattr(ibis._, base).notnull()
            if label(new) in {label(x) for x in [*requires.get(t, []), *found.get(t, [])]}:
                continue
            found.setdefault(t, []).append(new)
            source[label(new)] = Issue(NULL_KIND, c.label, False, shown=c.label)
    if not found:
        return report
    widened = {t: list(cs) for t, cs in requires.items()}
    _merge(widened, report._inferred)
    _merge(widened, found)
    again = once(widened, 0)[0]
    proved = {e.label for e in again.ensures if e.proved}
    if not all(c.proved or c.label in proved for c in report.ensures if c.label in by_label):
        # Only where it proves every postcondition that failed on NULL alone.
        kept_for = {iss.expr for iss in source.values() if iss.expr in proved}
        found = {t: [x for x in cs if source[label(x)].expr in kept_for] for t, cs in found.items()}
        found = {t: cs for t, cs in found.items() if cs}
        if not found:
            return report
        widened = {t: list(cs) for t, cs in requires.items()}
        _merge(widened, report._inferred)
        _merge(widened, found)
        again = once(widened, 0)[0]
    inferred = {t: list(cs) for t, cs in report._inferred.items()}
    _merge(inferred, found)
    again._inferred = inferred
    again._inferred_from = {**report._inferred_from, **source}
    again._hints = report._hints
    return again


def _confirm_hints(report: Report, requires, once) -> Report:
    """`report` with only the hints a proof confirms (#688): each possible
    runtime error whose hint proposes preconditions is verified again with
    them added to `requires` (and to what was inferred), and its hint is
    dropped if the error remains."""
    tried: dict[str, set[tuple[str, str]]] = {}
    issues = []
    for i in report.issues:
        if i.hint_needs:
            key = repr(sorted((t, sorted(label(c) for c in cs)) for t, cs in i.hint_needs.items()))
            if key not in tried:
                widened = {t: list(cs) for t, cs in requires.items()}
                _merge(widened, report._inferred)
                _merge(widened, i.hint_needs)
                again = once(widened, 0)[0]
                tried[key] = {(j.kind, j.expr) for j in again.issues if j.error}
            if (i.kind, i.expr) in tried[key]:
                i = replace(i, hint=i.unconfirmed, hint_needs={}, unconfirmed=None, needs=[])
        issues.append(i)
    return replace(report, issues=issues)


def _key_sources(
    transform: Transform, cols: Sequence[str], schemas: Mapping[str, Any]
) -> tuple[str, list[str]] | None:
    """The input table and its columns an output key comes from: traced
    through an Ibis expression, or for SQL, the one input with every column
    of the same name."""
    if isinstance(transform, str):
        origins = [_sql_origin(transform, c, schemas) for c in cols]
    else:
        origins = [_origin(transform.op(), c) for c in cols]
    if any(o is None for o in origins) or len({o[0] for o in origins if o}) != 1:
        return None
    return origins[0][0], [o[1] for o in origins if o]  # type: ignore[index]


def _sql_origin(sql: str, col: str, schemas: Mapping[str, Any]) -> tuple[str, str] | None:
    """The input table and column a SQL query's output column passes on
    unchanged (SQLGlot's lineage), if there is one."""
    import sqlglot.expressions as exp
    from sqlglot.lineage import lineage

    try:
        schema = {t: {c: str(d) for c, d in sch.items()} for t, sch in schemas.items()}
        root = lineage(col, sql, schema=schema, dialect="duckdb")
        nodes = list(root.walk())
    except Exception:  # noqa: BLE001 - no lineage, no origin
        return None
    leaves = [n for n in nodes if not n.downstream]
    for n in nodes:
        e = n.expression.this if isinstance(n.expression, exp.Alias) else n.expression
        if not isinstance(e, exp.Column | exp.Table):
            return None
    if len(leaves) != 1 or not isinstance(leaves[0].source, exp.Table):
        return None
    table = leaves[0].source.name
    return (table, leaves[0].name.split(".")[-1]) if table in schemas else None


def _key_reasons(
    transform: Transform,
    report: Report,
    requires: Mapping[str, Sequence[Condition]],
    ensures: Sequence[Condition],
    schemas: Mapping[str, Any],
    inputs: Collection[str] | None,
    once: Callable[..., Any],
) -> Report:
    """`report` with the reason each unproved `unique(...)` is not a key, in
    terms of the input it comes from (#688): declare the input's key where
    that proves it (checked), say the key is lost on the way where it is
    already declared, or that no key on an input reaches the column."""
    keys = {label(c): c for c in ensures if isinstance(c, Unique)}
    ensured = []
    for c in report.ensures:
        key = keys.get(c.label)
        if c.proved or key is None:
            ensured.append(c)
            continue
        src = _key_sources(transform, key.cols, schemas)
        out = ", ".join(f"`{x}`" for x in key.cols)
        if src is None:
            reason = (
                f"{out} {'is' if len(key.cols) == 1 else 'are'} computed, or "
                f"{'comes' if len(key.cols) == 1 else 'come'} from several inputs, "
                "and no key on an input makes it a key here"
            )
        else:
            t, base = src
            want = unique(*base)
            where = ", ".join(f"{t}.{b}" for b in base)
            stated = {label(x) for x in requires.get(t, [])}
            came = f"{out} {'comes' if len(key.cols) == 1 else 'come'} from {where}"
            if want.label in stated:
                reason = (
                    f"{came}, whose key {want.label} is lost on the way: a join, a union "
                    "or an UNNEST can repeat a value"
                )
            elif inputs is not None and t not in inputs:
                reason = f"{came}, which has no key on it"
            else:
                widened = {k: list(v) for k, v in requires.items()}
                _merge(widened, report._inferred)
                widened.setdefault(t, []).append(want)
                again = once(widened, 0)[0]
                if any(e.label == c.label and e.proved for e in again.ensures):
                    code = "sv.unique(" + ", ".join(repr(b) for b in base) + ")"
                    reason = f"{came}: declare `{code}` in the requires of {t!r}"
                else:
                    reason = (
                        f"{came}, and a key there does not make it one here: a join or a "
                        "union can repeat a value"
                    )
        ensured.append(replace(c, detail=f"the preconditions do not make it a key: {reason}"))
    return replace(report, ensures=ensured)


def _null_reasons(
    transform: Transform,
    report: Report,
    ensures: Sequence[Condition],
    proves: Callable[[Condition], bool],
) -> Report:
    """`report` with a way out for each postcondition that fails only on
    NULL (#688): allowing NULL in the column that is NULL, as code in the
    transformation's language, where the checker proves the condition so
    relaxed."""
    conds = {label(c): c for c in ensures if not isinstance(c, TableCondition)}
    ensured = []
    for c in report.ensures:
        cond = conds.get(c.label)
        parts = set(c.value.replace(" or ", ", ").split(", "))
        if c.proved or cond is None or c.detail or "FALSE" in parts or "NULL" not in parts:
            ensured.append(c)
            continue
        cols = c.nullable if c.nullable is not None else _reads(cond, report.output) or ()
        for col in [x for x in cols if "NULL" in report.facts.get(x, "NULL")]:
            if isinstance(cond, str) and isinstance(transform, str):
                relaxed: Condition = f"({cond}) OR {col} IS NULL"
                code = relaxed
            elif isinstance(cond, Deferred):
                relaxed = cond | getattr(ibis._, col).isnull()
                code = label(relaxed)
            else:
                continue
            if proves(relaxed):
                c = replace(
                    c,
                    detail=(
                        f"it may be NULL on some rows, where {col} is NULL: to allow that, "
                        f"state `{code}`"
                    ),
                )
                break
        ensured.append(c)
    return replace(report, ensures=ensured)


def _confirm_suggestions(report: Report, requires, once) -> Report:
    """`report` with only the suggestions a proof confirms: each unproved
    postcondition's suggested preconditions are added to `requires` (and to
    what was inferred), and kept if the postcondition is then proved."""
    ensures = []
    for c in report.ensures:
        if c.suggested:
            widened = {t: list(cs) for t, cs in requires.items()}
            _merge(widened, report._inferred)
            _merge(widened, c.suggested)
            again = once(widened, 0)[0]
            if not any(e.label == c.label and e.proved for e in again.ensures):
                c = replace(c, suggested={})
        ensures.append(c)
    return replace(report, ensures=ensures)


def _verify_once(
    transform: Transform,
    requires: Mapping[str, Sequence[Condition]],
    ensures: Sequence[Condition],
    tables: Mapping[str, ibis.Schema | ir.Table] | None,
    counterexamples: int,
    bound: list[str],
    inputs: Collection[str] | None,
    semantics: Semantics = "reference",
) -> tuple[Report, list[dict], dict[str, ibis.Schema]]:
    """One proof (see `verify`), with the bounds Lean inferred and the input
    schemas."""
    if semantics in _PROFILE_REQUESTS and isinstance(transform, str):
        raise ValueError(
            f"semantics={semantics!r} checks Ibis transformations; "
            "SQL is DuckDB's, so its semantics is 'duckdb' or 'reference'"
        )
    schemas = {name: input_schema(s) for name, s in (tables or {}).items()}
    if not isinstance(transform, str):
        schemas = {**leaf_tables(transform), **schemas}
    con = connect()
    for name, schema in schemas.items():
        con.create(name, schema)

    def lift(query: Any) -> Semantics:
        # A SQL condition (an inferred bound, say) is DuckDB's SQL, lifted
        # under the reference where the profile has no lift of its own.
        own = not (isinstance(query, str) and semantics in _PROFILE_REQUESTS)
        return semantics if own else "reference"

    def plan(query: Transform) -> Any:
        return json.loads(plan_json(con, query, lift(query)))

    def table_ref(name: str, cond: Condition) -> Transform:
        if isinstance(transform, str) and isinstance(cond, str):
            return f"SELECT * FROM {q(name)}"
        return con.table(name)

    def output(cond: Condition) -> Transform:
        """The transformation as `cond` reads it: an Ibis condition on a SQL
        transformation reads the lifted query as an Ibis relation over the
        input tables, as in an `sv.sql` body (#438)."""
        if not isinstance(transform, str) or isinstance(cond, str):
            return transform
        from sverify.ibis_substrait import SQLModel, sql_model_schema

        names = tuple(schemas)
        inputs: Any = tuple(con.table(n).op() for n in names)
        return SQLModel(
            transform,
            inputs,
            names,
            sql_model_schema(transform, schemas, semantics),
            "duckdb",
            semantics,
        ).to_expr()

    req_conds = [
        (t, c) for t, cs in requires.items() for c in cs if not isinstance(c, TableCondition)
    ]

    def query(where: str, n: int, table: Transform, c: Condition) -> Transform:
        """`condition_query`, with an Ibis error named by the condition it
        is in (#687)."""
        from ibis.common.exceptions import IbisError

        try:
            return condition_query(table, c, lift(c))
        except IbisError as e:
            msg = f"{where} condition {n}, {label(c)}, does not type-check: {e}"
            try:
                err = type(e)(msg)
            except Exception:  # noqa: BLE001 - an error class with another signature
                err = TypeError(msg)
            raise err from e

    req_plans = []
    for t, cs in requires.items():
        for n, c in enumerate(cs, start=1):
            if not isinstance(c, TableCondition):
                req_plans.append(plan(query(f"requires {t}", n, table_ref(t, c), c)))
    ens_plans = []
    for n, c in enumerate(ensures, start=1):
        if isinstance(c, TableCondition):
            continue
        p = plan(query("ensures", n, output(c), c))
        p["relations"][0]["root"]["names"] = [label(c)]
        ens_plans.append(p)
    transform_plan = plan(transform)
    out_cols: list[str] = transform_plan["relations"][0]["root"]["names"]

    def names(t: str) -> Sequence[str]:
        return column_names(schemas[t])

    def entries(kind: str) -> dict[str, list]:
        return {
            t: [
                c.plan_entry(t, names)
                for c in cs
                if isinstance(c, TableCondition) and c.entry == kind
            ]
            for t, cs in requires.items()
        }

    keys = entries("keys")
    ensures_keys = [_positions(c.cols, out_cols) for c in ensures if isinstance(c, Unique)]
    foreign_keys = entries("references")
    caps = {t: min(ns) for t, ns in entries("max_rows").items() if ns}
    per_key = {t: ps for t, ps in entries("rows_per").items() if ps}
    contract = {
        "requires": req_plans,
        "ensures": ens_plans,
        "transform": transform_plan,
        "keys": keys,
        "ensures_keys": ensures_keys,
        "references": foreign_keys,
        "max_rows": caps,
        "rows_per": per_key,
    }

    if semantics in _PROFILE_REQUESTS:
        contract["profile"] = semantics
    code, stdout, stderr = run_checker(("--contract",), json.dumps(contract))
    if code not in (0, 4):
        raise checker_failed("--contract", stderr)
    out = json.loads(stdout)
    if semantics in _PROFILE_REQUESTS and out.get("profile") != semantics:
        raise ValueError(
            f'this checker cannot check under semantics="{semantics}" yet (#444, step 3a)'
        )
    # SQL's types come from the lift, so a timestamp is described as one (#452).
    from sverify.ibis_substrait import sql_model_schema

    result = (
        sql_model_schema(transform, schemas, semantics)
        if isinstance(transform, str)
        else transform.schema()
    )
    dtypes = dict(result.items())

    def describe(f: dict) -> str:
        dtype = dtypes.get(f["name"])
        return (render_fact(f["abstract"], dtype) if dtype is not None else None) or f["value"]

    assumable: Container[str] = schemas if inputs is None else inputs
    rows = iter(out["ensures"])
    key_results = iter(out["keys"])
    req_named = [(t, p) for (t, _), p in zip(req_conds, req_plans, strict=True)]
    ens_iter = iter(ens_plans)
    key_iter = iter(ensures_keys)

    def find(target: dict | Sequence[int]) -> Counterexample | None:
        if not counterexamples:
            return None
        with _stages.stage("counterexamples"):
            return search_counterexample(
                schemas,
                req_named,
                keys,
                transform_plan,
                target,
                budget=counterexamples,
                references=foreign_keys,
            )

    def next_key() -> tuple[bool, Counterexample | None]:
        ok = next(key_results)["proved"]
        cols = next(key_iter)
        return ok, None if ok else find(cols)

    checked = []
    for c in ensures:
        if isinstance(c, TableCondition):
            checked.append(c.ensured(out, next_key))
        else:
            e = next(rows)
            p = next(ens_iter)
            ties = bool(e.get("ties"))
            # It depends on how ties are ordered, which the search, on
            # `Rel.eval`'s one order, rarely shows; breaking the ties with
            # a key proves it (#691).
            cex = None if e["proved"] or ties else find(p)
            suggested = _suggested(e.get("suggest"), schemas, assumable)
            checked.append(
                CheckedCondition(
                    e["name"], e["proved"], e["value"], cex, suggested=suggested, ties=ties
                )
            )
        checked[-1].condition = c
    from sverify import _user_text

    dialect: _user_text.Dialect = "sql" if isinstance(transform, str) else "ibis"
    seen = _user_text.columns(transform_plan)
    temporal = {
        c for sch in [*schemas.values(), result] for c, t in sch.items() if t.is_timestamp()
    }

    def shown(e: str, measure: bool = False) -> str | None:
        n = _user_text.named(e, transform_plan, measure, seen)
        return None if n is None else _user_text.pretty(n, dialect, temporal)

    def show(e: str) -> str:
        return shown(e) or e

    raw_issues = [
        i
        for i in out["issues"]
        # An overflow to ±∞ is the reference's precondition (#575): DuckDB's
        # semantics allows it, as DuckDB gives ±∞.
        if semantics == "reference" or i["kind"] != INFINITE
    ]
    report = Report(
        semantics=semantics,
        _dialect=dialect,
        requires={t: [label(c) for c in cs] for t, cs in requires.items()},
        ensures=checked,
        facts={f["name"]: describe(f) for f in out["facts"]},
        not_null=[
            f["name"]
            for f in out["facts"]
            if f["name"] in dtypes and f.get("abstract", {}).get("null") is False
        ],
        deterministic=out["deterministic"],
        _windows_total=out.get("windows_total", out["deterministic"]),
        _tie_places=tie_places(out),
        issues=_issues(
            raw_issues,
            # Ibis's `//` and `%` floor, and the producer writes them in the
            # reference's form (`floorDivOf`), as does a FLOOR option.
            floor=dialect == "ibis" or '"FLOOR"' in json.dumps(transform_plan),
            hint=lambda b: _hint(b, schemas, assumable, show),
            needs=lambda b: _render_needs(b["needs"], schemas),
            column=lambda e: _sum_column(transform, e),
            shown=shown,
            guess=lambda e: _guess_bounds(e, schemas, assumable, dialect),
            dialect=dialect,
        ),
        _guard_free=out["guard_free"],
        _unchecked=out.get("unchecked"),
        _optimized=out["optimized"],
        _rewrites=out["rewrites"],
        _params=bound,
        _bounds=_int_bounds(out["facts"], dtypes),
        rows=out.get("rows"),
        _relations=[
            RelationRows(r["op"], r["depth"], r["rows"], r["group_rows"])
            for r in out.get("relations", [])
        ],
        _implied=_implied_sql(out.get("implied", []), schemas),
        internal_plan=json.dumps(transform_plan),
        _depends=out.get("depends"),
        _epsilon=out.get("epsilon"),
        _rows_exact=out.get("rows_exact"),
        _contract=contract,
        _transfer=(out.get("transfer") or {}).get("failures") if semantics == "substrait" else None,
        output=dtypes,
        _postconditions=list(ensures),
        inputs=dict(schemas),
    )
    if not isinstance(transform, str) and report.issues:
        report._hints = overflow_hints(transform, requires, report)
    report._hints += and_or_hints(report.issues, transform)
    if not isinstance(transform, str):
        report._hints += rounding_hints(transform, ensures, checked, out["facts"], dtypes)
        if semantics != "polars":
            report._hints += division_hints(transform)
    return report, out["inferred"], schemas


def _guess_bounds(
    shown: str, schemas: Mapping[str, ibis.Schema], assumable: Container[str], dialect: str
) -> dict[str, list[Condition]]:
    """Bounds on the input columns an expression names, wide enough for
    most data: timestamps and dates in [1900, 2200), integers within ±10⁹,
    doubles and decimals within ±10⁶.
    A hint proposes them only where a proof confirms they rule its issue
    out (`_confirm_hints`, #688)."""
    names = set(re.findall(r"(?<![\w.'\"])([A-Za-z_]\w*)\b(?!\s*\()", shown))
    names |= set(re.findall(r"\w+\(([A-Za-z_]\w*)\)", shown))
    out: dict[str, list[Condition]] = {}
    for t, schema in schemas.items():
        if t not in assumable:
            continue
        for col, dtype in schema.items():
            if col not in names:
                continue
            q = f'"{col}"' if not col.isidentifier() else col
            if dtype.is_timestamp() or dtype.is_date():
                ctor, sql = ("datetime", "TIMESTAMP") if dtype.is_timestamp() else ("date", "DATE")
                lo, hi = (datetime, datetime) if ctor == "datetime" else (date, date)
                conds: list[Condition] = (
                    [getattr(ibis._, col) >= lo(1900, 1, 1), getattr(ibis._, col) < hi(2200, 1, 1)]
                    if dialect == "ibis"
                    else [f"{q} >= {sql} '1900-01-01'", f"{q} < {sql} '2200-01-01'"]
                )
            elif dtype.is_integer():
                conds = (
                    [getattr(ibis._, col) >= -1_000_000_000, getattr(ibis._, col) <= 1_000_000_000]
                    if dialect == "ibis"
                    else [f"{q} >= -1000000000", f"{q} <= 1000000000"]
                )
            elif dtype.is_floating() or dtype.is_decimal():
                conds = (
                    [getattr(ibis._, col) >= -1_000_000, getattr(ibis._, col) <= 1_000_000]
                    if dialect == "ibis"
                    else [f"{q} >= -1000000", f"{q} <= 1000000"]
                )
            else:
                continue
            out.setdefault(t, []).extend(conds)
    return out


def _merged_bound(bounds: Sequence[dict | None]) -> dict | None:
    """One inference result for the issues reported as one (`_issues`): the
    bounds each needs, the tightest per column, where every one has bounds;
    else the first reason none does."""
    if len(bounds) == 1:
        return bounds[0]
    found = [b for b in bounds if b is not None]
    if len(found) < len(bounds):
        return next((b for b in found if b["why"] is not None), None)
    if why := next((b for b in found if b["why"] is not None), None):
        return why
    ranges: dict[tuple[str, int], dict] = {}
    other: list[dict] = []
    for b in found:
        for n in b["needs"]:
            if "lo" not in n and "hi" not in n:
                if n not in other:
                    other.append(n)
                continue
            have = ranges.setdefault((n["table"], n["col"]), {**n})
            for k, pick in (("lo", max), ("hi", min)):
                vals = [int(v) for v in (have.get(k), n.get(k)) if v is not None]
                have[k] = str(pick(vals)) if vals else None
    return {
        "why": None,
        "split": any(b["split"] for b in found),
        "needs": [*ranges.values(), *other],
    }


def _issues(
    raw: Sequence[dict],
    floor: bool,
    hint: Callable[[dict | None], str | None],
    needs: Callable[[dict], Mapping[str, Sequence[Inferred]]],
    column: Callable[[str], str | None],
    shown: Callable[..., str | None],
    guess: Callable[[str], dict[str, list[Condition]]] = lambda e: {},
    dialect: str = "ibis",
) -> list[Issue]:
    """The checker's issues, one per expression the user wrote and kind
    (#687): the sub-expressions of an expression that may overflow, and the
    branches of the reference's form of a floor division (`_user_text.fold`),
    are reported as the expression, with the bounds that rule out all of
    them."""
    from sverify._user_text import fold

    groups: dict[tuple[str, str], list[dict]] = {}
    for kind in dict.fromkeys(i["kind"] for i in raw):
        members = [i for i in raw if i["kind"] == kind]
        for i, key in zip(members, fold([i["expr"] for i in members], floor), strict=True):
            groups.setdefault((kind, key), []).append(i)
    out = []
    for (kind, expr), members in groups.items():
        error = any(i["error"] for i in members) or kind == INFINITE
        constant = any(i.get("constant", False) for i in members)
        bound = _merged_bound([i["bound"] for i in members])
        if constant:
            text = CONSTANT_HINT
        elif any(i["error"] for i in members):
            text = hint(bound)
        else:
            text = INFINITE_HINT if kind == INFINITE else None
        code: Mapping[str, Sequence[Condition]] = (
            needs(bound) if bound and bound.get("why") is None else {}
        )
        named_as = expr
        if m := re.fullmatch(r"TO_DECIMAL_(\d+)\(.*\)", expr):
            # A double's cast to a decimal: the precision is the cast's
            # around it, `DECIMAL_p_s(TO_DECIMAL_s(x))`.
            outer = re.compile(rf"DECIMAL_(\d+)_{m[1]}\({re.escape(expr)}\)")
            if found := next((x for i in raw if (x := outer.search(i["expr"]))), None):
                named_as = found[0]
        user = shown(named_as, kind in ("SUM overflow", INFINITE))
        fallback = None
        # The inference does not reach the columns (a window's value, a cast):
        # bounds on the columns the expression names, if a proof confirms
        # them (#688).
        guessed = (
            guess(user) if error and not constant and bound and bound.get("why") and user else {}
        )
        if guessed:
            code, fallback = guessed, text
            text = (
                "bound the columns it reads: state "
                + " and ".join(
                    f"{', '.join(f'`{label(c)}`' for c in cs)} in the requires of {t!r}"
                    for t, cs in guessed.items()
                )
                + " (or tighter bounds your data keeps)"
            )
        out.append(
            Issue(
                kind,
                expr,
                # Lean keeps the IEEE value of an overflow to ±∞ (#575), and
                # a report counts it as a `SUM` overflow: assumed with
                # `infer`, an error without.
                error,
                text,
                column(expr) if kind == "SUM overflow" else None,
                constant,
                any(i.get("under_and_or", False) for i in members),
                tuple(label(c) for cs in code.values() for c in cs) if not fallback else (),
                user,
                # The inference's preconditions, as data; a guess is not one.
                [_needed(t, c, dialect) for t, cs in code.items() for c in cs]
                if error and not fallback
                else [],
                hint_needs={t: list(cs) for t, cs in code.items()} if error else {},
                unconfirmed=fallback,
            )
        )
    return out


DIVISION_HINT = (
    "Ibis `//` floors and `%` truncates, so `({a} // {b}) * {b} + {a} % {b} == {a}` "
    "fails for negative {a}: bound {a} below by 0 in `requires`, or write the plan in SQL, "
    "where `//` truncates (guide: 'Integer division in Ibis and SQL')"
)


def division_hints(transform: ir.Table) -> list[str]:
    """For each integer `a // b` and `a % b` the Ibis expression applies to the
    same operands: that the pair does not split `a` for negative values
    (#693)."""
    import ibis.expr.operations as ops

    node = transform.op()
    mods = {
        (m.left, m.right)
        for m in node.find(ops.Modulus)
        if isinstance(m, ops.Modulus) and m.dtype.is_integer()  # pyrefly: ignore
    }
    hints: list[str] = []
    for d in node.find(ops.FloorDivide):
        if isinstance(d, ops.FloorDivide) and d.dtype.is_integer() and (d.left, d.right) in mods:
            hint = DIVISION_HINT.format(a=_ibis_text(d.left), b=_ibis_text(d.right))
            if hint not in hints:
                hints.append(hint)
    return hints


def _ibis_text(node: Any) -> str:
    """An operand as the user wrote it, as far as it is a column or literal."""
    import ibis.expr.operations as ops

    if isinstance(node, ops.Field):
        return node.name
    if isinstance(node, ops.Literal):
        return str(node.value)
    return "the operand"


def rounding_hints(
    transform: ir.Table,
    ensures: Sequence[Condition],
    checked: Sequence[CheckedCondition],
    facts: Sequence[dict],
    dtypes: Mapping[str, Any],
) -> list[str]:
    """For each unproved comparison of a double column with a number that the
    column's proved bounds miss only by rounding (by at most `1e-6` of the
    number, #85): how much, and the `approx` that proves it."""
    import ibis.expr.operations as ops

    bounds = {}
    for f in facts:
        dtype, b = dtypes.get(f["name"]), f["abstract"].get("int")
        if dtype is not None and dtype.is_floating() and b is not None:
            bounds[f["name"]] = tuple(
                None if v is None else decode_double(int(v)) for v in (b["lo"], b["hi"])
            )
    hints = []
    for cond, c in zip(ensures, checked, strict=True):
        if c.proved or not isinstance(cond, Deferred):
            continue
        try:
            node = cond.resolve(transform).op()
        except Exception:  # noqa: BLE001 - only a hint
            continue
        if not isinstance(node, ops.Less | ops.LessEqual | ops.Greater | ops.GreaterEqual):
            continue
        col, lit = node.left, node.right
        if not (isinstance(col, ops.Field) and isinstance(lit, ops.Literal)):
            continue
        if not lit.dtype.is_numeric() or col.name not in bounds:
            continue
        k = float(lit.value)
        lo, hi = bounds[col.name]
        above = isinstance(node, ops.Less | ops.LessEqual)
        edge = hi if above else lo
        if edge is None or not math.isfinite(edge):
            continue
        excess = edge - k if above else k - edge
        if 0 < excess <= 1e-6 * max(1.0, abs(k)):
            hints.append(
                f"{c.label} holds up to rounding: {col.name} is proved within {excess:.3g} of "
                f"{k:g} (#85); state it as sv.approx({c.label})"
            )
    return hints


def _int_bounds(facts: Sequence[dict], dtypes: Mapping[str, Any]) -> dict:
    """The integer bounds of the integer output columns in the checker's `facts`."""
    out = {}
    for f in facts:
        dtype, b = dtypes.get(f["name"]), f["abstract"].get("int")
        if dtype is not None and dtype.is_integer() and b is not None:
            out[f["name"]] = tuple(None if v is None else int(v) for v in (b["lo"], b["hi"]))
    return out


def _origin(rel: Node, name: str) -> tuple[str, str] | None:
    """The base table and column that column `name` of relation `rel` passes
    on unchanged, if there is one."""
    if isinstance(rel, ops.UnboundTable | ops.DatabaseTable):
        return rel.name, name
    if isinstance(rel, ops.SelfReference):
        return _origin(rel.parent, name) if name in rel.parent.schema else None
    values = getattr(rel, "values", None)
    if isinstance(rel, ops.Aggregate):
        values = {**rel.groups, **rel.metrics}
    if values is not None:
        return _value_origin(values[name]) if name in values else None
    parent = getattr(rel, "parent", None)
    if parent is not None and name in parent.schema:
        return _origin(parent, name)
    return None


def _confirmed_ties(
    transform: ir.Table,
    requires: Mapping[str, Sequence[Condition]],
    report: Report,
    tables: Mapping[str, ibis.Schema | ir.Table] | None,
    params: list[str],
    inputs: Collection[str] | None,
    semantics: Semantics,
) -> dict[str, list[str]]:
    """`tie_keys`, where declaring them makes the result determined (#688):
    a key the checker cannot follow to the ORDER BY (through a join, say) is
    not suggested."""
    keys = tie_keys(transform)
    stated = {t: {label(c) for c in cs} for t, cs in requires.items()}
    keys = {
        t: [k for k in ks if k not in stated.get(t, set())]
        for t, ks in keys.items()
        if inputs is None or t in inputs
    }
    keys = {t: ks for t, ks in keys.items() if ks}
    if not keys:
        return {}
    widened = {t: list(cs) for t, cs in requires.items()}
    _merge(widened, report._inferred)
    for t, ks in keys.items():
        for k in ks:
            cols = re.fullmatch(r"unique\((.*)\)", k)
            if cols:
                widened.setdefault(t, []).append(unique(*cols[1].split(", ")))
    again = _infer_bounds(transform, widened, [], tables, 0, params, False, inputs, semantics)
    return keys if again.deterministic else {}


def tie_keys(expr: ir.Table) -> dict[str, list[str]]:
    """The `sv.unique(...)` per input table that leaves no ties in the
    ORDER BY of a window or of an ordered aggregate (`first`, `last`, …):
    its partition (or grouping) and order columns, as labels (#655)."""
    out: dict[str, list[str]] = {}

    def add(fields: Sequence[Any]) -> None:
        cols = [o for f in fields if (o := _value_origin(f)) is not None]
        tables = {t for t, _c in cols}
        if len(tables) != 1 or len(cols) != len(fields):
            return
        (t,) = tables
        lab = label(unique(*dict.fromkeys(c for _t, c in cols)))
        if lab not in out.setdefault(t, []):
            out[t].append(lab)

    def fields_of(values: Sequence[Any]) -> list[Any]:
        found: list[Any] = []
        for v in values:
            v = getattr(v, "expr", v)
            found += [f for f in v.find(ops.Field) if isinstance(f, ops.Field) and f not in found]
        return found

    for agg in expr.op().find(ops.Aggregate):
        if not isinstance(agg, ops.Aggregate):
            continue
        for metric in agg.metrics.values():
            order = getattr(metric, "order_by", None)
            if order:
                add(fields_of([*agg.groups.values(), *order]))
    for win in expr.op().find(ops.WindowFunction):
        if isinstance(win, ops.WindowFunction) and win.order_by:
            add(fields_of([*win.group_by, *win.order_by]))
    return out


def _input_columns(rel: Node, names: Sequence[str]) -> list[tuple[str, str]]:
    """The base table columns the output columns `names` of `rel` read:
    the column itself where it is passed on, else the columns its value
    reads that are passed on (`length(s)` reads `s`)."""
    out: list[tuple[str, str]] = []
    values = getattr(rel, "values", None)
    if isinstance(rel, ops.Aggregate):
        values = {**rel.groups, **rel.metrics}
    for name in names:
        if (o := _origin(rel, name)) is not None:
            found = [o]
        elif values is not None and name in values:
            fields = [f for f in values[name].find(ops.Field) if isinstance(f, ops.Field)]
            found = [o for f in fields if (o := _value_origin(f)) is not None]
        else:
            found = []
        out += [o for o in found if o not in out]
    return out


def _value_origin(value: Node) -> tuple[str, str] | None:
    """The base table and column a value is, if it is a column passed on
    unchanged."""
    if isinstance(value, ops.Field):
        return _origin(value.rel, value.name)
    return None


#: The bound a SUM hint proposes for an unbounded side of a column.
SUM_BOUND = 1_000_000_000


#: What a report suggests for an error under `AND`/`OR` (#604, D19).
AND_OR_HINT = (
    "`{}` is inside an AND or OR you wrote (`{}`), and DuckDB and Polars evaluate "
    "both operands on every row, so a guard in the other operand does not keep it "
    "from raising. Guard the operation itself with {} (a boolean CASE is "
    "evaluated whole, as AND and OR are), or state the guard as a precondition"
)

_IDENT = re.compile(r"(?<![\w.'\"])([A-Za-z_]\w*)\b(?!\s*\()")


def _user_and_or(transform: Transform) -> list[set[str]]:
    """The columns each AND or OR the user wrote reads: Ibis's `&`, `|`
    (not those the producer writes, such as in a floor division), or SQL's
    `AND`, `OR` (every column, as the SQL is not walked)."""
    if isinstance(transform, str):
        return [set[str]()] if re.search(r"\b(AND|OR)\b", transform, re.IGNORECASE) else []
    found: list[set[str]] = []
    for op in transform.op().find((ops.And, ops.Or, ops.Xor)):
        found.append({str(f.name) for f in op.find(ops.Field)})
    # Ibis splits a filter's `&` into its predicates.
    for op in transform.op().find(ops.Filter):
        if len(op.predicates) > 1:
            found.append({str(f.name) for p in op.predicates for f in p.find(ops.Field)})
    return found


def and_or_hints(issues: Sequence[Issue], transform: Transform | None = None) -> list[str]:
    """`AND_OR_HINT` for each error under an `AND`/`OR` the user wrote, once
    per expression (#688): the checker also counts those the producer
    writes."""
    dialect = "sql" if isinstance(transform, str) else "ibis"
    held = _user_and_or(transform) if transform is not None else [set()]
    seen = []
    for i in issues:
        e = i.shown or i.expr
        if not (i.error and i.under_and_or) or e in seen:
            continue
        cols = set(_IDENT.findall(e))
        if any(not reads or cols <= reads for reads in held):
            seen.append(e)
    return [_and_or_hint(e, dialect) for e in seen]


def _and_or_hint(e: str, dialect: str = "ibis") -> str:
    """`AND_OR_HINT` for one operation, with the guard written out where it
    is a division: `ibis.cases((_.qty != 0, _.total // _.qty))`."""
    m = re.fullmatch(r"(\w+) (//|/|%) (\w+)", e)
    op = "&` or `|" if dialect == "ibis" else "AND` or `OR"
    if m and not m[3].isdigit():
        a, div, b = m.groups()
        guard = (
            f"`ibis.cases((_.{b} != 0, _.{a} {div} _.{b}))`"
            if dialect == "ibis"
            else f"`CASE WHEN {b} <> 0 THEN {a} {div} {b} END`"
        )
    else:
        guard = (
            f"`ibis.cases((<guard>, {e}))`"
            if dialect == "ibis"
            else f"`CASE WHEN <guard> THEN {e} END`"
        )
    return AND_OR_HINT.format(e, op, guard)


def overflow_hints(
    transform: ir.Table, requires: Mapping[str, Sequence[Condition]], report: Report
) -> list[str]:
    """The bounds to add to `requires` for the overflows `report` names (#379):
    lower and upper bounds on each truncated timestamp or date column, and for
    an integer `SUM` that is checked while the job runs, a bound on the
    column it adds up, with the largest group whose sum then fits 64 bits."""
    hints: list[str] = []
    # An overflow with its own hint (`infer_bounds`) has its exact bounds.
    if any(i.kind == "overflow" and _truncates(i.expr) and not i.hint for i in report.errors):
        kinds = (ops.TimestampTruncate, ops.DateTruncate, ops.TimestampBucket)
        for op in transform.op().find(kinds):
            if (origin := _value_origin(op.arg)) is None:  # type: ignore[attr-defined]
                continue
            table, col = origin
            ctor = "date" if op.arg.dtype.is_date() else "datetime"  # type: ignore[attr-defined]
            hints.append(
                f"{TRUNC_HINT} `{col}` in `requires` of {table}: truncating a value near the "
                f"ends of the timestamp range overflows. For example `_.{col} >= {ctor}(2000, "
                f"1, 1)` and `_.{col} < {ctor}(2100, 1, 1)`"
            )
    if any(_sum(i) for i in report.errors):
        for op in transform.op().find(ops.Sum):
            if (hint := _sum_hint(op, requires)) is not None:
                hints.append(hint)
    return list(dict.fromkeys(hints))


def _sum_column(transform: ir.Table | str, expr: str) -> str | None:
    """The column an integer `SUM` that Lean names `expr` (`$i`, its
    input's i-th column) adds up, named as `_sum_hint` names it, if exactly
    one `SUM` of the transformation matches."""
    if isinstance(transform, str) or not re.fullmatch(r"\$\d+", expr):
        return None
    names = set()
    for op in transform.op().find(ops.Sum):
        arg = op.arg  # type: ignore[attr-defined]
        rels = list(arg.relations)
        if not arg.dtype.is_integer() or len(rels) != 1 or not isinstance(arg, ops.Field):
            continue
        cols = rels[0].schema.names
        if arg.name not in cols or f"${cols.index(arg.name)}" != expr:
            continue
        origin = _value_origin(arg)
        names.add(origin[1] if origin else arg.name)
    return names.pop() if len(names) == 1 else None


def _sum_hint(op: Node, requires: Mapping[str, Sequence[Condition]]) -> str | None:
    """The hint for an integer `SUM`: what bounds its argument, and the
    largest group whose sum fits 64 bits."""
    arg = op.arg  # type: ignore[attr-defined]
    rels = list(arg.relations)
    if not arg.dtype.is_integer() or len(rels) != 1:
        return None
    origin = _value_origin(arg)
    what = f"`{origin[1]}`" if origin else f"`{arg.name}`"
    sub = rels[0].to_expr().select(x=arg.to_expr())
    leaves = leaf_tables(sub)
    known = {
        t: [c for c in cs if not isinstance(c, References)]
        for t, cs in requires.items()
        if t in leaves
    }
    report = verify(sub, requires=known, counterexamples=0, on_inferred="off")
    lo, hi = report._bounds.get("x", (None, None))
    # A BIGINT's own range bounds nothing: any two of its values may overflow.
    lo = None if lo is None or lo <= -(2**63) else lo
    hi = None if hi is None or hi >= 2**63 - 1 else hi
    where = f"`requires` of {origin[0]}" if origin else f"`requires` (on the columns of {what})"

    def capped(n: int) -> str:
        """The row cap that proves the sum fits (#219)."""
        return (
            f"`sv.max_rows({n:_})` in {where} proves it, and so does "
            f"`sv.rows_per(<grouping columns>, at_most={n:_})`; without a row bound, the job "
            "checks the sum as it runs"
        )

    if lo is not None and hi is not None:
        largest = max(abs(lo), abs(hi))
        if largest == 0:
            return None
        rows = (2**63 - 1) // largest
        if rows >= 2**63 - 1:
            # A group has fewer than 2^63 rows (`Rel.sumRows`, #437): the
            # sum fits, and Lean proves it.
            return None
        return (
            f"SUM of {what}: it is in [{lo}, {hi}], so a group's sum fits 64 bits for up to "
            f"{rows:,} rows; {capped(rows)}"
        )
    col = origin[1] if origin else "x"
    proposed = []
    if hi is None:
        proposed.append(f"`_.{col} <= {SUM_BOUND:_}`")
    if lo is None:
        proposed.append(f"`_.{col} >= {-SUM_BOUND:_}`")
    largest = max(SUM_BOUND, abs(lo or 0), abs(hi or 0))
    rows = (2**63 - 1) // largest
    return (
        f"SUM of {what}: bound it in {where}, for example {' and '.join(proposed)}; then a "
        f"group's sum fits 64 bits for up to {rows:,} rows, and {capped(rows)}"
    )


def violations(table: ir.Table, cond: Condition, engine: Engine | None = None) -> int:
    """Rows of a bound table where `cond` is not TRUE (FALSE or NULL), or for
    `unique`, rows beyond the first for each repeated key.

    With an engine named, the condition's plan runs there, over the tables of
    the connection `table` is bound to; otherwise Ibis counts on that
    connection."""
    if not isinstance(cond, TableCondition) and engine is not None:
        con = connection_of(table)
        if con is None:
            raise ValueError("checking a condition on an engine needs a table of sverify.connect()")
        plan = written_plan(plan_json(con, condition_query(table, cond)))
        return sum(v is not True for v in run_plan(con, plan, engine).column(0).to_pylist())
    if isinstance(cond, TableCondition):
        return cond.violations(table)
    if isinstance(cond, str):
        backend: Any = ibis.get_backend(table)
        sql = ibis.to_sql(table, dialect=backend.name)
        query = f'SELECT count(*) FROM ({sql}) AS "t" WHERE NOT coalesce(({cond}), FALSE)'
        # On the backend's own connection: Ibis 12's `backend.sql` asks DuckDB 2
        # for the query's schema with a method it no longer has.
        # `raw_sql` returns the connection itself: fetch every row, so that it
        # is free for the next query, and leave it open.
        return int(backend.raw_sql(query).fetchall()[0][0])
    count: Any = table.filter(~resolve(cond, table).fill_null(ibis.literal(False))).count()
    return _count(count)


ROWS_SHOWN = 10
"""How many violating rows a `PreconditionError` carries (`.rows`)."""


def violating_rows(table: ir.Table, cond: Condition, limit: int = ROWS_SHOWN) -> pa.Table | None:
    """Up to `limit` rows of the bound `table` where `cond` is not TRUE, or
    for `unique`, the rows of a repeated key; None for a condition on the
    table as a whole, or if the rows cannot be fetched (they only go into an
    error, which says how many rows break the condition either way)."""
    try:
        if isinstance(cond, Unique):
            cols = list(cond.cols)
            counts = table.group_by(cols).aggregate(__sverify_n=table.count())
            dup = counts.filter(counts["__sverify_n"] > 1).select(cols)
            return table.semi_join(dup, cols).limit(limit).to_pyarrow()
        if isinstance(cond, TableCondition):
            return None
        if isinstance(cond, str):
            backend: Any = ibis.get_backend(table)
            sql = ibis.to_sql(table, dialect=backend.name)
            query = (
                f'SELECT * FROM ({sql}) AS "t" WHERE NOT coalesce(({cond}), FALSE) LIMIT {limit}'
            )
            # Fetch every row, as `violations` does, so that the connection
            # is free for the next query (DuckDB 2 refuses work on a
            # connection with a result left unread).
            import pyarrow

            cur = backend.raw_sql(query)
            names = [d[0] for d in cur.description]
            rows = [dict(zip(names, r, strict=True)) for r in cur.fetchall()]
            return pyarrow.Table.from_pylist(rows, schema=table.schema().to_pyarrow())
        bad = table.filter(~resolve(cond, table).fill_null(ibis.literal(False)))
        return bad.limit(limit).to_pyarrow()
    except Exception:
        return None


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


@dataclass(frozen=True)
class Fact:
    """What table metadata says about every row of a table, as a SQL
    condition, and where it comes from ("Delta constraint", "file stats @v3").
    The metadata is trusted; facts only discharge preconditions through Lean
    (`contract_sound` on the table itself), never by name."""

    condition: str
    source: str
    rows: int | None = None
    """For a row-count fact, at most this many rows; its `condition` is then
    `TRUE` (the record counts of a table format's files, #219)."""


SCHEMA = "schema"
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


# Metadata facts of tables read from a table format (`sverify.io`), keyed
# by backend identity and table name. Tables without an entry only have
# their preconditions checked on the data: an in-memory schema is not enforced.
_facts: dict[tuple[int, str], list[Fact]] = {}


def register_facts(con: Connection, name: str, facts: Sequence[Fact] | None) -> None:
    """Record (or with None, forget) what metadata says about table `name`."""
    key = (id(con._ibis), name)
    if facts is None:
        _facts.pop(key, None)
    else:
        _facts[key] = list(facts)


def table_facts(table: ir.Table) -> list[Fact] | None:
    """Metadata facts of a base table, if it was read from a table format."""
    op = table.op()
    if not isinstance(op, ops.DatabaseTable):
        return None
    return _facts.get((id(op.source), op.name))


_proved_from: dict[tuple, frozenset[str]] = {}


def _prove_from(table: ir.Table, facts: Sequence[str], conds: Sequence[Condition]) -> set[str]:
    """Labels of `conds` that Lean proves about every row of `table` from its
    schema and `facts`. A fact the checker cannot read proves nothing."""
    name = table.op().name  # type: ignore[attr-defined]
    key = (name, str(table.schema()), tuple(facts), tuple(label(c) for c in conds))
    if key not in _proved_from:
        try:
            report = verify(
                table,
                requires={name: list(facts)},
                ensures=conds,
                counterexamples=0,
                on_inferred="off",
            )
            _proved_from[key] = frozenset(c.label for c in report.ensures if c.proved)
        except Exception:
            _proved_from[key] = frozenset()
    return set(_proved_from[key])


def discharge(
    table: ir.Table,
    name: str,
    conds: Sequence[Condition],
    engine: Engine | None,
    facts: Sequence[Fact] | None,
    what: str,
) -> list[Discharged]:
    """Establish row conditions on a bound table, reported under `name`.

    With metadata `facts`, each condition is proved from the schema alone if
    possible, else from the schema and the facts of the first sources (in
    order) that suffice. The rest are checked on the data, raising
    `PreconditionError` with "<n> <what> violate <condition>"."""
    out: list[Discharged] = []
    todo = list(conds)
    # A row cap from a row-count fact of metadata.
    counts = [(f.rows, f.source) for f in facts or [] if f.rows is not None]
    counted = {
        id(c): source
        for c in todo
        if isinstance(c, TableCondition)
        for source in [next((s for n, s in counts if c.capped_by(n)), None)]
        if source is not None
    }
    out += [Discharged(name, label(c), counted[id(c)]) for c in todo if id(c) in counted]
    todo = [c for c in todo if id(c) not in counted]
    if facts is not None:
        stages: dict[str, list[str]] = {SCHEMA: []}
        for f in facts:
            if f.rows is None:
                stages.setdefault(f.source, []).append(f.condition)
        assumed: list[str] = []
        for source, extra in stages.items():
            rowwise = [c for c in todo if not isinstance(c, TableCondition)]
            if not rowwise:
                break
            assumed += extra
            proved = _prove_from(table, assumed, rowwise)
            out += [
                Discharged(name, label(c), source, isinstance(c, Inferred))
                for c in rowwise
                if label(c) in proved
            ]
            todo = [c for c in todo if label(c) not in proved]
    for c in todo:
        if n := violations(table, c, engine):
            raise PreconditionError(
                f"{n} {what} violate {label(c)}",
                source=name,
                condition=c,
                rows=violating_rows(table, c),
            )
        out.append(Discharged(name, label(c), ON_DATA, isinstance(c, Inferred)))
    return out


def is_bound(table: ir.Table) -> bool:
    try:
        ibis.get_backend(table)
    except Exception:
        return False
    return True


class CompositionError(VerificationError):
    """A contracted transformation's precondition on an input is not implied
    by what the contracted transformation producing that input guarantees.

    Import it from `sverify.errors`. It is raised when the link is built:
    when a transform is called on another contracted transformation's result,
    or on a node (`sverify.Node`) built from one, stored or not. The message
    names both sides, for example "doubled needs (_.amount >= 0) (it may be
    FALSE on some rows) on 't'; not_null only guarantees _.amount.notnull()". With
    `on_unproved="check"` and a bound input, the precondition is checked on
    the data instead; with `on_unproved="warn"` it is a warning.

    Attributes:
        report: The `Report` of the failed proof of the link.
        consumer: The name of the transformation whose precondition failed.
        param: The parameter of `consumer` that received the input.
        producer: The name of the contracted transformation that produced it.
    """

    def __init__(self, report: Report, consumer: str, param: str, producer: str, guarantees):
        self.report = report
        self.consumer, self.param, self.producer = consumer, param, producer
        needs = ", ".join(f"{c.label} ({c.why})" for c in report.unproved)
        given = ", ".join(guarantees) or "nothing"
        Exception.__init__(
            self,
            f"{consumer} needs {needs} on {param!r}; {producer} only guarantees {given}",
        )


@dataclass(frozen=True)
class Provenance:
    """How a contracted result was made, kept so that a later contracted
    transformation (or an incremental view) can build on its guarantees.

    `body` is the result with every contracted or derived input replaced by a
    placeholder table; `assumptions` are what the proof of `body` assumed about
    each of its tables. The result satisfies `guarantees` whenever the base
    tables satisfy `external`."""

    transform: ContractedTransform
    body: ir.Table
    assumptions: dict[str, list[Condition]]
    guarantees: list[Condition]
    report: Report
    external: dict[str, list[Condition]]
    """Preconditions on base tables, of this transformation and every
    contracted transformation upstream."""
    unproved_links: list[str]
    """Preconditions on derived inputs that were checked on the data, or
    merely warned about, instead of proved, and runtime-checked
    postconditions of contracted transformations upstream."""
    checked: list[Condition] = field(default_factory=list)
    """The postconditions `on_unproved="check"` checks on the result's data
    because they were not proved: on a bound result when it is built, and in
    an incremental view on every state (`IncrementalView.checked`)."""
    policies: Policies = field(default_factory=dict)
    """For each precondition in `external`, by table and label, the
    `on_violation` of every transform that states it (None: unset)."""


def _checked_links(prov: Provenance) -> list[str]:
    """A result's runtime-checked postconditions, as seen downstream: checked
    on its own rows, they are nothing a consumer's state is checked for."""
    return [f"{prov.transform.name}: {label(c)} was checked on data" for c in prov.checked]


# Keyed by identity: Ibis ops compare by structure, and an equal expression
# built independently has not been through the contract's checks.
_provenance: dict[int, tuple[weakref.ref[Node], Provenance]] = {}


def _lookup(op: Node) -> Provenance | None:
    entry = _provenance.get(id(op))
    return entry[1] if entry is not None and entry[0]() is op else None


def _register(op: Node, prov: Provenance) -> None:
    key = id(op)
    _provenance[key] = (weakref.ref(op, lambda _, reg=_provenance: reg.pop(key, None)), prov)


def provenance(table: ir.Table) -> Provenance | None:
    """The contract behind `table`, if a contracted transformation returned it."""
    return _lookup(table.op())


def _is_base(op: Node) -> bool:
    return isinstance(op, ops.UnboundTable | ops.DatabaseTable)


def _merge(into: dict[str, list[Condition]], extra: Mapping[str, Sequence[Condition]]) -> None:
    for t, cs in extra.items():
        have = into.setdefault(t, [])
        have += [c for c in cs if label(c) not in {label(h) for h in have}]


def _fresh(name: str, taken: set[str]) -> str:
    out, n = name, 1
    while out in taken:
        n += 1
        out = f"{name}_{n}"
    taken.add(out)
    return out


@dataclass
class _Abstraction:
    """An expression with its contracted parts replaced by placeholder tables
    (assume-guarantee reasoning: a contracted result is only known by its
    guarantees)."""

    body: ir.Table
    assumptions: dict[str, list[Condition]]
    external: dict[str, list[Condition]]
    unproved_links: list[str]
    policies: Policies = field(default_factory=dict)


def _merge_policies(into: Policies, extra: Policies) -> None:
    for t, by_label in extra.items():
        have = into.setdefault(t, {})
        for lab, ps in by_label.items():
            have.setdefault(lab, set()).update(ps)


def _abstract(
    expr: ir.Table,
    placeholders: Mapping[Node, tuple[str, list[Condition]]] | None = None,
    taken: set[str] | None = None,
) -> _Abstraction:
    """Replace `placeholders` (op -> table name and its assumptions) and every
    other contracted result inside `expr` by placeholder tables."""
    placeholders = dict(placeholders or {})
    given = set(placeholders)
    taken = set(leaf_tables(expr)) | {n for n, _ in placeholders.values()} | (taken or set())
    for op in expr.op().find(lambda n: _lookup(n) is not None):
        prov = _lookup(op)
        if prov is not None and op not in placeholders and op is not expr.op():
            placeholders[op] = (_fresh(prov.transform.name, taken), list(prov.guarantees))
    mapping: dict[Node, Node] = {
        op: ibis.table(op.to_expr().schema(), name=name).op()  # type: ignore[attr-defined]
        for op, (name, _) in placeholders.items()
    }
    root = expr.op()
    body: ir.Table = (mapping[root] if root in mapping else root.replace(mapping)).to_expr()  # type: ignore[attr-defined]
    used = set(leaf_tables(body))
    out = _Abstraction(body, {}, {}, [])
    for op, (name, conds) in placeholders.items():
        if name in used and conds:
            _merge(out.assumptions, {name: conds})
        if name in used and op not in given and (prov := _lookup(op)):
            _merge(out.external, prov.external)
            _merge_policies(out.policies, prov.policies)
            out.unproved_links += prov.unproved_links + _checked_links(prov)
    return out


@dataclass
class ViewContract:
    """The contract of a (possibly composed) contracted expression, as seen by
    an incremental view: it `guarantees` its proved postconditions on every
    state whose base tables satisfy `requires`."""

    requires: dict[str, list[Condition]]
    guarantees: list[Condition]
    provenance: Provenance | None
    checked: list[Condition] = field(default_factory=list)
    """Postconditions that were not proved, which the view checks on every
    state (`on_unproved="check"`)."""
    not_null: list[str] = field(default_factory=list)
    """The columns the proved report shows never NULL (`Report.not_null`):
    they hold in every state, as `guarantees` do."""
    policies: Policies = field(default_factory=dict)
    """The `on_violation` the transforms set on each precondition in
    `requires` (`Provenance.policies`)."""


def view_contract(expr: ir.Table) -> ViewContract:
    """Collect the base-table preconditions of every contracted
    transformation inside `expr`. Refuses preconditions on derived inputs that
    were checked on data instead of proved: a view could not keep them true
    from base-table changes."""
    prov = _lookup(expr.op())
    if prov is not None:
        requires, unproved, policies = prov.external, prov.unproved_links, prov.policies
    else:
        inner = _abstract(expr)
        requires, unproved, policies = inner.external, inner.unproved_links, inner.policies
    if unproved:
        raise ValueError(
            "cannot maintain incrementally: conditions on derived inputs were "
            f"not proved ({'; '.join(unproved)})"
        )
    if per_key := [label(c) for cs in requires.values() for c in cs if isinstance(c, RowsPer)]:
        raise ValueError(
            "cannot maintain incrementally: batches are not checked against rows_per yet "
            f"(#219): {', '.join(per_key)}"
        )
    return ViewContract(
        {t: list(cs) for t, cs in requires.items()},
        list(prov.guarantees) if prov else [],
        prov,
        list(prov.checked) if prov else [],
        list(prov.report.not_null) if prov and prov.report.proved else [],
        {t: {lab: set(ps) for lab, ps in by.items()} for t, by in policies.items()},
    )


def register_view(table: ir.Table, contract: ViewContract) -> None:
    """Let contracted transformations that read a materialized view `table`
    build on the guarantees of the expression it materializes."""
    if contract.provenance is not None:
        _register(table.op(), contract.provenance)


class ContractedTransform:
    """A transformation with a contract; see `transform`.

    Call it like the function it wraps. Called on Ibis tables, it returns the
    same Ibis expression, after proving the contract. Called on sources
    (`sverify.io`) or nodes, it returns a `sverify.Node`, whose contract is
    checked when it is built. It keeps the wrapped function's name and
    docstring.

    Attributes:
        name: The wrapped function's name; also the name of the nodes it
            builds.
    """

    def __init__(
        self,
        fn: Callable[..., ir.Table],
        requires: Mapping[str, Sequence[Condition]] | Sequence[Condition] | None,
        ensures: Sequence[Condition],
        on_unproved: OnUnproved,
        check_requires: bool,
        engine: Engine | None,
        infer: bool = True,
        semantics: Semantics = "reference",
        on_inferred: OnInferred = "error",
        on_violation: Policy | None = None,
    ):
        self.fn, self.ensures = fn, expand_keys(ensures)
        self.on_violation: Policy | None = check_policy(on_violation)
        """What a refresh does with a batch of a source that breaks this
        transform's preconditions (#184); None: the source's setting."""
        self.on_inferred = on_inferred
        self.on_unproved, self.check_requires = on_unproved, check_requires
        self.infer = infer
        self.semantics = _checked_semantics(semantics)
        self.check_engine = engine
        self.name: str = fn.__name__
        self.signature = inspect.signature(fn)
        self.requires: dict[str, Sequence[Condition]] = requires_by_input(
            requires, list(self.signature.parameters), "parameter", TypeError
        )
        self.report: Report | None = None
        """The `Report` of the proof of the postconditions in the last call,
        or None before the first call: the report of this transform, as a
        node's `report` is the node's."""
        self._counterexamples: int | None = None
        self._last_preconditions: list[Discharged] = []
        """How each precondition on a bound input was established, in the
        last call: from metadata (`sverify.io` tables) or on the data."""
        self._cache: dict[tuple, Report] = {}
        functools.update_wrapper(self, fn)

    @property
    def last_report(self) -> Report | None:
        """Deprecated: `report`."""
        warnings.warn(
            "ContractedTransform.last_report is deprecated; read .report",
            DeprecationWarning,
            stacklevel=2,
        )
        return self.report

    @property
    def last_preconditions(self) -> list[Discharged]:
        """Deprecated: the refresh report carries how each precondition was
        established (`Refresh.report.preconditions`)."""
        warnings.warn(
            "ContractedTransform.last_preconditions is deprecated; a refresh report's "
            "preconditions say how each was established",
            DeprecationWarning,
            stacklevel=2,
        )
        return self._last_preconditions

    def to_substrait(
        self,
        format: Literal["json", "binary"] = "json",
        *,
        shims: Literal["apply", "annotate", "refuse"] = "apply",
    ) -> str | bytes:
        """The verified plan of the last call, with its contract as
        metadata: `Report.to_substrait` of `report`. A call proves the
        contract for its inputs' schemas, so call the transform first, on
        tables, sources or nodes; `Node.to_substrait` exports a node.

        Args:
            format: `"json"` (protobuf JSON, a string) or `"binary"` (the
                serialized `substrait.Plan`).
            shims: What to do at a spec gap the proof depends on (see
                `Report.to_substrait`).

        Returns:
            The plan, as protobuf JSON or bytes.

        Raises:
            sverify.errors.ExportError: The transform has not been called
                yet, its report is not proved, or the plan has no
                conforming Substrait form that keeps the proof.
        """
        from sverify.substrait_export import ExportError

        if self.report is None:
            raise ExportError(
                f"{self.name} has not been called yet: call it on tables, sources or "
                "nodes first, which proves its contract for their schemas"
            )
        return self.report.to_substrait(format, shims=shims)

    def _verify(
        self,
        body: ir.Table,
        assumptions: Mapping[str, Sequence[Condition]],
        ensures,
        tag: str,
        inputs: Collection[str] = (),
        infer: bool = False,
    ) -> Report:
        """Prove `ensures` of `body`, inferring bounds on the tables in
        `inputs` with `infer` (`infer_bounds`)."""
        params = [
            p for p in body.op().find(ops.ScalarParameter) if isinstance(p, ops.ScalarParameter)
        ]
        if params:
            # Ibis's SQL compiler raises a bare KeyError on them (#440).
            names = ", ".join(f"ibis.param({p.dtype})" for p in params)
            name = getattr(self.fn, "__name__", "the transformation")
            raise TypeError(
                f"{name} uses {names}: a transformation does not bind "
                "parameters yet (#354). Prove it for given values with "
                "sv.verify(expr, params={param: value}), or write the values as "
                "ibis.literal(...)"
            )
        inputs = frozenset(inputs)
        budget = (
            default_counterexamples() if self._counterexamples is None else self._counterexamples
        )
        key = (
            tag,
            inputs,
            infer,
            self.on_inferred,
            self.semantics,
            ibis.to_sql(body, dialect="duckdb"),
            tuple(sorted((n, str(s)) for n, s in leaf_tables(body).items())),
            tuple(sorted((t, tuple(label(c) for c in cs)) for t, cs in assumptions.items())),
            tuple(label(c) for c in ensures),
            budget,
        )
        if key not in self._cache:
            self._cache[key] = infer_bounds(
                body,
                requires=assumptions,
                ensures=ensures,
                tables=None,
                counterexamples=budget,
                params=[],
                infer=infer,
                inputs=inputs,
                semantics=self.semantics,
                # Only the postconditions' proof needs the user's bounds; the
                # links' and conditions' proofs infer as before.
                on_inferred=self.on_inferred if tag == "ensures" else "ignore",
            )
        return self._cache[key]

    def _check_on_data(self, table: ir.Table, param: str, conds: Sequence[Condition]) -> bool:
        """Establish preconditions on a bound input, from its metadata where
        possible (`discharge`); False if it is not bound."""
        if not is_bound(table):
            return False
        self._last_preconditions += discharge(
            table, param, conds, self.check_engine, table_facts(table), f"row(s) of {param}"
        )
        return True

    def _link(
        self,
        param: str,
        value: ir.Table,
        conds: list[Condition],
        entry: Collected | None = None,
    ) -> _Abstraction:
        """Discharge this transformation's preconditions on a derived input by
        proving them from what produced it (assume-guarantee composition).
        Returns, as `assumptions`, what may be assumed about the input."""
        prov = _lookup(value.op())
        if prov is not None:
            inner = _Abstraction(
                prov.body,
                prov.assumptions,
                prov.external,
                list(prov.unproved_links) + _checked_links(prov),
                prov.policies,
            )
            known = list(prov.guarantees)
        else:
            # A plain Ibis expression guarantees nothing by itself, but its
            # obligations may still follow from its operations.
            inner, known = _abstract(value), []
        needed = [c for c in conds if label(c) not in {label(k) for k in known}]
        out = _Abstraction(
            value, {param: known + needed}, inner.external, inner.unproved_links, inner.policies
        )
        if not needed:
            return out
        report = self._verify(inner.body, inner.assumptions, needed, f"link {param}")
        proved = {c.label for c in report.ensures if c.proved}
        unproved = [c for c in needed if label(c) not in proved]
        if not unproved:
            return out
        out.unproved_links += [f"{self.name}: {label(c)} on {param}" for c in unproved]
        if prov is None:
            # Like a base table: checked on the data when it is bound, else assumed.
            if self.check_requires:
                self._check_on_data(value, param, unproved)
            return out
        error = CompositionError(
            report, self.name, param, prov.transform.name, [label(c) for c in known]
        )
        if self.on_unproved == "warn":
            warnings.warn(str(error), stacklevel=4)
        elif self.on_unproved == "check" and self._check_on_data(value, param, unproved):
            pass
        elif entry is not None:
            entry.links.append(error)
        else:
            raise error
        return out

    def _pipe_args(self, chained: Any, inputs: Mapping[str, Any]) -> tuple[tuple, dict[str, Any]]:
        """How `Node.pipe` passes the chained node and the keyword inputs:
        the chained node in the first parameter, the rest by keyword."""
        from sverify.steps import bind

        return bind(self, chained, inputs)

    def __call__(self, *args, **kwargs) -> Any:
        """Build the result and prove the contract.

        When an input is a source (`sverify.io`) or a node, the result is a
        `sverify.Node`. The contract is checked then, on placeholder tables
        with the inputs' schemas: the postconditions are proved, and a
        precondition on another node's result must follow from what that
        node guarantees. Preconditions on sources are checked on the data
        when the node is refreshed, and then on every batch.

        Otherwise the result is the Ibis expression the wrapped function
        returns. Inputs bound to a backend have their preconditions checked
        on the data (or proved from table metadata); results of other
        contracted transformations have them proved from those
        transformations' guarantees. Then the postconditions are proved.

        Args:
            *args: The wrapped function's positional arguments: Ibis tables,
                or sources and nodes (not a mix of both).
            **kwargs: The wrapped function's keyword arguments, likewise.

        Returns:
            A `sverify.Node` if an input is a source or a node, else the Ibis
            table expression the wrapped function returns.

        Raises:
            PreconditionError: A bound input's data violates a precondition.
            CompositionError: A precondition on another contracted
                transformation's result does not follow from its guarantees.
            VerificationError: A postcondition, or the absence of runtime
                errors, could not be proved (with `on_unproved="error"`, or
                with `"check"` when the result is neither bound nor a
                node).
            PostconditionError: With `on_unproved="check"`, an unproved
                postcondition fails on the output data of a bound result. A
                node's are checked at every refresh instead
                (`sverify.Node.refresh`).
            TypeError: Sources or nodes are mixed with Ibis tables.
            ValueError: The node would read two tables of the same name.
        """
        from sverify import nodes

        if nodes.wants_node(args, kwargs):
            return nodes.derive(self, args, kwargs)
        return self._build(args, kwargs, node=False)

    def check(self, *args: Any, counterexamples: int | None = None, **kwargs: Any) -> Report:
        """Prove the contract for the input schemas, and return the report
        without raising and without reading data.

        `doubled.check(orders=schema)` is `doubled(orders)` on an unbound
        table of that schema: the postconditions are proved, the needed
        preconditions inferred, and the report kept in `report`. An
        unproved contract does not raise `VerificationError`, a bound table
        stands for its schema (its data is not read, so `requires` is not
        checked on it), and `on_unproved` does not apply. An editor, a test
        or a CI step reads the report (`Report.proved`, `Report.needed`).

        Args:
            *args: The inputs, positionally: Ibis tables, `ibis.Schema`s, or
                mappings from column name to type (`{"id": "int64"}`).
            counterexamples: Inputs tried per unproved postcondition for one
                that breaks it (`sverify.counterexample`); 0 skips the
                search. Default: `default_counterexamples()`, as a call uses.
            **kwargs: The inputs by parameter name, likewise.

        Returns:
            The `Report` of the proof.

        Raises:
            TypeError: The inputs do not match the function's parameters, or
                one is no table or schema (a source or a node: check the
                transform on its `schema` instead).
        """
        bound = self.signature.bind(*args, **kwargs)
        for name, value in bound.arguments.items():
            if isinstance(value, ir.Table):
                value = value.schema()
            if isinstance(value, Mapping) and not isinstance(value, ibis.Schema):
                value = ibis.schema(value)
            if not isinstance(value, ibis.Schema):
                raise TypeError(
                    f"{self.name}.check: {name} must be an Ibis table or a schema, "
                    f"not {type(value).__name__}"
                )
            bound.arguments[name] = ibis.table(value, name=name)
        before = self._counterexamples
        self._counterexamples = counterexamples
        try:
            self._build(bound.args, bound.kwargs, node=False, raise_unproved=False)
        except VerificationError as e:  # from a link of a composed input
            self.report = e.report
        finally:
            self._counterexamples = before
        assert self.report is not None
        return self.report

    def _build(
        self,
        args: Sequence[Any],
        kwargs: Mapping[str, Any],
        *,
        node: bool,
        raise_unproved: bool = True,
    ) -> ir.Table:
        """The result and its proof. A `node` result (`nodes.derive`, on
        placeholder tables) has its runtime-checked postconditions checked
        at every refresh instead of now."""
        inputs = self.signature.bind(*args, **kwargs).arguments
        self._last_preconditions = []
        entry = None
        if (collected := COLLECTING.get()) is not None:
            entry = Collected(self, node)
            collected.append(entry)
        result = self.fn(*args, **kwargs)
        placeholders: dict[Node, tuple[str, list[Condition]]] = {}
        base: dict[str, list[Condition]] = {}
        bound_inputs: dict[str, tuple[str, ir.Table]] = {}
        # Placeholders of plain expressions (a memtable, a filtered table):
        # their preconditions are checked on the data like a base table's.
        plain: dict[str, tuple[str, ir.Table]] = {}
        external: dict[str, list[Condition]] = {}
        policies: Policies = {}
        unproved_links: list[str] = []
        taken = set(leaf_tables(result))
        for param, value in inputs.items():
            if not isinstance(value, ir.Table):
                continue
            conds = list(self.requires.get(param, ()))
            op = value.op()
            if _is_base(op) and _lookup(op) is None:
                # Data from outside: checked when bound to a backend.
                _merge(base, {op.name: conds})  # type: ignore[attr-defined]
                bound_inputs.setdefault(op.name, (param, value))  # type: ignore[attr-defined]
                if self.check_requires:
                    self._check_on_data(value, param, conds)
                continue
            link = self._link(param, value, conds, entry)
            _merge(external, link.external)
            _merge_policies(policies, link.policies)
            unproved_links += link.unproved_links
            if op in placeholders:  # the same input under two parameters
                name, assumed = placeholders[op]
                _merge({name: assumed}, {name: link.assumptions[param]})
            else:
                prov = _lookup(op)
                name = _fresh(prov.transform.name if prov else param, taken)
                placeholders[op] = (name, link.assumptions[param])
                if prov is None:
                    plain[name] = (param, value)
        abstraction = _abstract(result, placeholders, taken)
        assumptions = {**abstraction.assumptions}
        _merge(assumptions, base)
        report = self.report = self._verify(
            abstraction.body, assumptions, self.ensures, "ensures", {*base, *plain}, self.infer
        )
        # Inferred bounds on the inputs are preconditions like the rest:
        # checked on the data (or proved from metadata) and passed on,
        # before any check on the output reads them.
        for t, conds in report._inferred.items():
            _merge(assumptions, {t: conds})
            if t in plain:
                param, value = plain[t]
                unproved_links += [f"{self.name}: {label(c)} on {param}" for c in conds]
            else:
                _merge(base, {t: conds})
                param, value = bound_inputs[t]
            if self.check_requires:
                self._check_on_data(value, param, conds)
        checked: list[Condition] = []
        if not report.proved and raise_unproved:
            # Runtime errors cannot be checked on the data beforehand: in
            # "check" mode the engine raises them if they happen.
            if self.on_unproved == "check" and (node or is_bound(result)):
                unproved = {c.label for c in report.unproved}
                checked = [c for c in self.ensures if label(c) in unproved]
                report = self.report = _marked_checked(report)
                for c in [] if node else checked:
                    if n := violations(result, c, self.check_engine):
                        raise PostconditionError(f"{n} output row(s) violate {label(c)}")
            elif entry is not None:
                pass  # collected: the caller reads the report
            elif self.on_unproved == "warn":
                warnings.warn(str(VerificationError(report)), stacklevel=3)
            else:
                raise VerificationError(report)
        if entry is not None:
            entry.report = report
            entry.params = {t: p for t, (p, _) in {**bound_inputs, **plain}.items()}
        _merge(external, abstraction.external)
        _merge(external, base)
        _merge_policies(policies, abstraction.policies)
        _merge_policies(
            policies,
            {t: {label(c): {self.on_violation} for c in cs} for t, cs in base.items()},
        )
        proved = {c.label for c in report.ensures if c.proved}
        _register(
            result.op(),
            Provenance(
                transform=self,
                body=abstraction.body,
                assumptions=assumptions,
                guarantees=[c for c in self.ensures if label(c) in proved],
                report=report,
                external=external,
                unproved_links=unproved_links + abstraction.unproved_links,
                checked=checked,
                policies=policies,
            ),
        )
        return result


def _marked_checked(report: Report) -> Report:
    """`report` (cached, so left as it is) with its unproved postconditions
    marked as checked on data."""
    ensures = [c if c.proved else replace(c, checked=True) for c in report.ensures]
    return replace(report, ensures=ensures)


def transform(
    requires: Mapping[str, Sequence[Condition]] | Sequence[Condition] | None = None,
    ensures: Sequence[Condition] = (),
    *,
    on_unproved: OnUnproved | Literal["runtime"] = "error",
    check_requires: bool = True,
    check_engine: Engine | None = None,
    semantics: Semantics = "reference",
    on_inferred: OnInferred = "error",
    engine: Engine | None = None,
    infer: bool | None = None,
    on_violation: Policy | None = None,
) -> Callable[[Callable[..., ir.Table]], ContractedTransform]:
    """Decorate a function from Ibis tables to an Ibis table with a contract.

    `requires` maps parameter names to conditions on that input. On each call
    the postconditions are proved (cached per input schema and expression) and
    the report is kept in `.report`; see the module docstring. With
    `on_unproved="check"`, unproved postconditions are checked on the output
    data instead: on inputs bound to a connection, when the transform is
    called; on a node, at every refresh, on the rows the batch inserts, before
    its sink commits. The report marks them `checked`. `check_engine` says
    where those checks on data run (see the module docstring).

    Piped from a source (`sverify.io`) or a node, `orders.pipe(doubled)`, or
    called on one, `doubled(orders)`, the transform builds a `sverify.Node`
    instead of an Ibis expression: transforms compose over sources,
    `.write(sink)` stores a result, and `refresh` keeps it up to date (see
    `sverify.Node`). `Node.pipe` also takes a plain function, which is a
    transform with no contract.

    Args:
        requires: Preconditions, as a mapping from parameter name to
            conditions on that input (or, for a function of one table, a
            list of its conditions): Ibis expressions (`_.amount >= 0`),
            functions of the table, SQL snippets (`"amount >= 0"`), `unique`
            or `references`. Default: none.
        ensures: Postconditions on the result, in the same forms (but not
            `references`). Default: none, which still rules out runtime
            errors.
        on_unproved: What happens when a postcondition, or a precondition on
            another contracted transformation's result, is not proved:
            `"error"` (the default) raises; `"check"` checks a postcondition
            on the output data instead (bound inputs, or a node at every
            refresh) and a precondition on a bound input's data; `"warn"`
            emits a warning and returns the result, and a node's refreshes
            run it unverified, each with an `UnverifiedRunWarning`
            (`refresh(unverified=True)`). `"runtime"` is a deprecated
            spelling of `"check"`.
        check_requires: Whether to check preconditions on the data of bound
            inputs at call time. Default True. False with an
            `on_violation` other than `"error"` raises `ValueError`: that
            setting acts on those checks.
        check_engine: Where checks on data run: `"duckdb"`, `"polars"` or
            `"datafusion"` run each condition's plan as Lean wrote it; None
            (the default) runs them through Ibis on the inputs' connection.
            `refresh(engine=)` says where a node's plan runs.
        semantics: What the contract's SQL conditions mean in its proofs,
            as `verify`'s: `"reference"` (the default) or `"duckdb"`.
        on_inferred: What a precondition sverify infers does, as
            `verify`'s. sverify infers the bounds it needs (`amount * 2` on
            BIGINT needs `_.amount < 2**62`). `"error"` (the default): the
            contract is not proved until `requires` states it or the
            transformation no longer needs it (`Report.needed`). `"warn"`:
            it is assumed and checked on the data or proved from table
            metadata, with an `InferredPreconditionWarning`. `"ignore"`:
            the same without the warning. `"off"`: nothing is inferred or
            assumed, so an integer `SUM` that may leave 64 bits is an error
            too, which the other values check on the data while the job
            runs (`Report.assumed`). `"silent"` is a deprecated spelling of
            `"ignore"`.
        engine: Deprecated alias of `check_engine`.
        infer: Deprecated: `infer=False` is `on_inferred="off"`.
        on_violation: What a refresh does with a batch of a source that
            breaks one of these preconditions, inferred ones included
            (#184): `"error"` raises `PreconditionError`; `"quarantine"`
            sets the offending rows aside with the reason, in the node's
            quarantine table, and the rest flows; `"hold"` commits nothing
            for the batch and holds the node at its versions until a later
            version of the source meets the preconditions. Default None:
            the source's `on_violation`, else `"error"`. Where two
            transforms state the same condition, the stricter holds.

    Returns:
        A decorator that turns the function into a `ContractedTransform`.

    Raises:
        TypeError: When decorating, if `requires` names a parameter the
            function does not have. Calls raise `PreconditionError`,
            `CompositionError`, `VerificationError` or `PostconditionError`
            from `sverify.errors` (see `ContractedTransform.__call__`).

    Examples:
        A contract that holds, on a source, and what the checker worked out about
        the output:

        ```python
        import pyarrow as pa
        import sverify as sv
        from ibis import _
        from sverify.io import StaticSource

        orders = StaticSource(
            pa.table({"id": [1, 2], "amount": [30, 5]}), name="orders"
        )

        @sv.transform(
            requires={"orders": [_.amount >= 0, _.id.notnull()]},
            ensures=[_.doubled >= 0, _.doubled.notnull(), "id IS NOT NULL"],
        )
        def doubled(orders):
            return orders.filter(orders.amount > 10).select(orders.id, doubled=orders.amount * 2)

        big = orders.pipe(doubled)  # a Node, proved here (as doubled(orders))
        doubled.report.proved  # True
        doubled.report.facts["doubled"]  # 'an integer ≥ 22'
        big.refresh()
        big.to_arrow().to_pylist()  # [{'id': 1, 'doubled': 60}]
        ```

        Transforms compose: the downstream precondition is proved from the
        upstream guarantee, and a link that does not hold is refused:

        ```python
        from sverify.errors import CompositionError

        @sv.transform(requires={"t": [_.doubled >= 0]}, ensures=[_.plus >= 1])
        def plus_one(t):
            return t.select(t.id, plus=t.doubled + 1)

        big.pipe(plus_one)  # proved from what doubled guarantees

        @sv.transform(requires={"t": [_.doubled >= 100]})
        def huge(t):
            return t

        try:
            big.pipe(huge)
        except CompositionError as e:
            print(str(e).split(";")[0])
        # huge needs (_.doubled >= 100) (it may be FALSE on some rows) on 't'
        ```

        A postcondition that does not follow is refused:

        ```python
        from sverify.errors import VerificationError

        @sv.transform(requires={"orders": [_.amount >= 0]}, ensures=[_.total > 5])
        def total(orders):
            return orders.select(orders.id, total=orders.amount + 1)

        try:
            orders.pipe(total)
        except VerificationError as e:
            print(str(e).splitlines()[0])
        # could not prove: (_.total > 5) (it may be FALSE on some rows)
        ```
    """
    on_inferred = _folded_infer(on_inferred, infer, "transform")
    if engine is not None:
        warnings.warn(
            "transform(engine=...) is deprecated; write check_engine=... (where checks on "
            "data run; refresh(engine=...) says where the plan runs)",
            DeprecationWarning,
            stacklevel=2,
        )
        if check_engine is None:
            check_engine = engine
    on_unproved = _checked_on_unproved(on_unproved)
    check_policy(on_violation)
    if not check_requires and on_violation not in (None, "error"):
        raise ValueError(
            f"on_violation={on_violation!r} acts on the checks of the preconditions on the "
            "data, which check_requires=False turns off"
        )
    return lambda fn: ContractedTransform(
        fn,
        requires,
        ensures,
        on_unproved,
        check_requires,
        check_engine,
        on_inferred != "off",
        semantics,
        on_inferred,
        on_violation,
    )
