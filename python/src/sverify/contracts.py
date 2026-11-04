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
postcondition raises `VerificationError` that says what Lean could establish,
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
import re
import warnings
import weakref
from collections.abc import Callable, Collection, Container, Mapping, Sequence
from dataclasses import dataclass, field, replace
from datetime import date, datetime, timedelta
from decimal import Decimal
from fractions import Fraction
from typing import Any, Literal

import ibis
import ibis.expr.operations as ops
import ibis.expr.types as ir
from ibis.common.deferred import Deferred
from ibis.common.graph import Node

from sverify.counterexample import Counterexample
from sverify.counterexample import search as search_counterexample
from sverify.engine import (
    Connection,
    Engine,
    connect,
    connection_of,
    create_table,
    plan_json,
    run_checker,
    run_plan,
    written_plan,
)


def q(name: str) -> str:
    """Quote a SQL identifier."""
    return '"' + name.replace('"', '""') + '"'


@dataclass(frozen=True)
class Unique:
    """No two rows agree on these columns (see `unique`).

    Attributes:
        cols: The key's column names, in the order given to `unique`.
    """

    cols: tuple[str, ...]


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
class References:
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


def references(col: str, *legacy: str, to: ir.Column | tuple[str, str] | None = None) -> References:
    """A foreign key: every non-NULL value of `col` occurs in the column `to`
    of another table.

    Only for `requires`, where it is checked on the data like `unique` (the
    referenced table must be bound to the same backend). With a key on the
    referenced column it lets `Rel.optimize` turn a left join on it into an
    inner join (`Report.optimized`). Not supported by incremental views.

    Args:
        col: The referencing column of the input the condition is on.
        *legacy: Deprecated: the referenced table and column as two more
            positional strings, `references(col, table, other)`, which are
            easy to swap. Use `to=`.
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
    if legacy:
        if to is not None or len(legacy) != 2:
            raise TypeError("references() takes a column and to=(table, column)")
        warnings.warn(
            "references(col, table, other) is deprecated; write "
            f"references({col!r}, to=({legacy[0]!r}, {legacy[1]!r})) or to=<table>.<column>",
            DeprecationWarning,
            stacklevel=2,
        )
        table, other = legacy
    elif to is None:
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
class ArrivesWithin:
    """Rows arrive at most `lateness` late on `col` (see `arrives_within`).

    Attributes:
        col: The time column, a timestamp.
        lateness: How far behind the latest `col` seen a changed row may be.
    """

    col: str
    lateness: timedelta


def arrives_within(
    col: str, *, days: float = 0, hours: float = 0, minutes: float = 0, seconds: float = 0
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
        days: The lateness, added up with the other units.
        hours: The lateness, added up with the other units.
        minutes: The lateness, added up with the other units.
        seconds: The lateness, added up with the other units.

    Returns:
        An `ArrivesWithin` condition, for `requires`.

    Raises:
        ValueError: The lateness is negative.
    """
    lateness = timedelta(days=days, hours=hours, minutes=minutes, seconds=seconds)
    if lateness < timedelta(0):
        raise ValueError(f"arrives_within needs a lateness of 0 or more, not {lateness}")
    return ArrivesWithin(col, lateness)


@dataclass(frozen=True)
class MaxRows:
    """At most `n` rows (see `max_rows`).

    Attributes:
        n: The cap.
    """

    n: int


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
class Approx:
    """A condition relaxed by a relative tolerance (see `approx`).

    Attributes:
        cond: The condition, an Ibis expression or a function of the table.
        rel: The relative tolerance.
    """

    cond: Any
    rel: float

    def __call__(self, table: ir.Table) -> ir.BooleanValue:
        return _relax(resolve(self.cond, table), self.rel)


def _relax(expr: ir.BooleanValue, rel: float) -> ir.BooleanValue:
    """`expr` with each comparison against a number `k` moved outward by
    `rel · max(1, |k|)`."""
    import ibis.expr.operations as ops

    def slack(k: Any) -> float:
        return rel * max(1.0, abs(float(k)))

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
        raise TypeError(
            "approx relaxes comparisons of a column with a number, combined with AND and OR; "
            f"it cannot relax {node.__class__.__name__}"
        )

    return go(expr.op())


def approx(cond: Any, rel: float = 1e-6) -> Approx:
    """A postcondition that holds up to rounding: every comparison of a column
    with a number `k` in `cond` is relaxed by `rel · max(1, |k|)`.

    `_.avg <= 100` may fail by the last bits after `AVG` of doubles rounds;
    `approx(_.avg <= 100)` is `_.avg <= 100.0001`, which the checker proves
    from the error bounds of #85 when the inputs have a row cap
    (`max_rows`), and which runs as that condition at run time. The default
    `rel = 1e-6` covers the error of a `SUM` or `AVG` over any cap up to
    `2³²` rows, about `n · 2⁻⁵³` relative to the values' bound. Comparisons
    combine with AND and OR; `BETWEEN` and `=` widen on both sides.

    Args:
        cond: An Ibis condition (`_.avg <= 100`) or a function of the table.
        rel: The relative tolerance, `1e-6` by default.

    Returns:
        A condition for `ensures` (or `requires`).

    Raises:
        TypeError: `cond` is a SQL snippet.
    """
    if isinstance(cond, str):
        raise TypeError("approx takes an Ibis condition, not SQL; write the slack in the SQL")
    return Approx(cond, rel)


Semantics = Literal["reference", "duckdb"]
"""What a check's SQL means: sverify's reference semantics (the default) or
DuckDB's (#411)."""


def _checked_semantics(semantics: str) -> Semantics:
    if semantics not in ("reference", "duckdb"):
        raise ValueError(f"semantics must be 'reference' or 'duckdb', not {semantics!r}")
    return semantics  # type: ignore[return-value]


TableCondition = (Unique, References, ArrivesWithin, MaxRows)
"""Conditions on a whole table or its batches, not on each row."""

Condition = (
    Deferred
    | ir.BooleanValue
    | str
    | Unique
    | References
    | ArrivesWithin
    | MaxRows
    | Callable[[ir.Table], ir.BooleanValue]
)
Transform = ir.Table | str


@dataclass
class CheckedCondition:
    """One postcondition in a `Report`, and what became of its proof."""

    label: str
    """The condition as written, e.g. "(_.amount >= 0)" or "unique(id)"."""
    proved: bool
    """Whether Lean proved it."""
    value: str
    """What Lean established about the condition, e.g. "TRUE or NULL"."""
    counterexample: Counterexample | None = None
    """For an unproved condition: inputs meeting the preconditions on which
    it fails, if the search (`sverify.counterexample`) found one."""
    checked: bool = False
    """For an unproved condition with `on_unproved="runtime"`: it is checked
    on the output data instead, on a bound result when it is built, or on a
    node at every refresh before its sink commits."""
    suggested: dict[str, list[Condition]] = field(default_factory=dict)
    """For an unproved condition: preconditions on the inputs, per table,
    under which Lean proves it (`_.x * 2 <= 100` holds with `_.x <= 50`).
    Never assumed: adding them is the author's choice."""

    @property
    def why(self) -> str:
        """Why it is not proved, in words: what Lean found the condition may
        be on a row that meets the preconditions, and, where it may be NULL,
        how to rule that out."""
        parts = set(self.value.replace(" or ", ", ").split(", "))
        if "TRUE" not in parts and parts == {"FALSE"}:
            return "it is FALSE on every row"
        bad = [v for v in ("FALSE", "NULL") if v in parts]
        if not bad:
            return f"Lean only knows it is {self.value}"
        why = f"it may be {' or '.join(bad)} on some rows"
        if "NULL" in bad:
            why += (
                ", where a column it reads is NULL: declare the column NOT NULL in the schema "
                "(`!int64`) or add `_.<column>.notnull()` to `requires`"
            )
        return why


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
    "fits {} in every group (inferred; checked on the data while the job "
    "runs, which raises if it does not)"
)

#: A decimal `SUM`'s argument in Lean's notation: `DECIMAL_p_s(…)`.
_DECIMAL_ARG = re.compile(r"DECIMAL_(\d+)_(\d+)\(")


def _sum(issue: Issue) -> bool:
    """Whether `issue` is a `SUM` that may leave its type."""
    return issue.kind == "SUM overflow"


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
    "domain error", or "SUM overflow" (a `SUM` leaving its type: 64 bits for
    integers, the result's precision for decimals)."""
    expr: str
    """The operation, in Lean's notation (`$i` is the operation's i-th input
    column)."""
    error: bool
    """True if a proof must rule it out. Every issue is one; a "SUM overflow"
    is also checked while the job runs, where the transformation's SQL raises
    too."""
    hint: str | None = None
    """For an overflow: the bound that would rule it out, as code to add to
    a contract, or why no bound on a column does (`infer_bounds`). None if
    there is nothing to suggest."""
    column: str | None = None
    """For a "SUM overflow": the column the SUM adds up, named as in its
    hint (the base table's column where it is passed on unchanged). None if
    `expr` is not a single column."""

    @property
    def what(self) -> str:
        """The column, or else the expression, a report names the issue by."""
        return self.column or self.expr

    def __str__(self) -> str:
        return f"{self.kind}: {self.expr}"


@dataclass
class Report:
    """What Lean proved about a transformation, returned by `verify` and kept
    in `ContractedTransform.last_report`.

    `str(report)` lists each postcondition with its status, the possible
    runtime errors and warnings, and what is known about each output column;
    in a notebook the report renders as tables.
    """

    requires: dict[str, list[str]]
    """The preconditions that were assumed, as labels, per input table."""
    ensures: list[CheckedCondition]
    """Each postcondition, in the order given: its label, whether it was
    proved, what Lean established about it, and a counterexample if one was
    found."""
    facts: dict[str, str] = field(default_factory=dict)
    """What Lean established about each output column."""
    deterministic: bool = True
    """False when rows may tie in the ORDER BY of a window or of an ordered
    aggregate (`first`, `last`, `group_concat`; without an `order_by` every
    row ties): the engine then picks an order, and nothing is proved about
    the result."""
    issues: list[Issue] = field(default_factory=list)
    """Runtime errors, SUM overflows among them, Lean could not rule out; when
    empty, the transformation provably runs without them."""
    guard_free: bool = False
    """The only issues are `SUM`s that may overflow: on data that meets
    the preconditions, the transformation's SQL (`sverify.engines.to_sql`)
    and Polars plan give the same result with `guards=False`, without
    per-row checks (`Rel.guardFree_sound`)."""
    unchecked: dict | None = None
    """The expressions that run correctly without their checks, on data that
    meets the preconditions (`Rel.evalG_marks`), as a tree parallel to the
    plan; pass it to `sverify.engines.to_sql(..., unchecked=...)` with the
    same plan, and only the other expressions keep their checks. None when
    Lean found none (a left join with a filter on its right side, for one)."""
    optimized: dict | None = None
    """The transformation as a Substrait JSON plan, rewritten with the facts
    and keys of the preconditions (`Rel.optimize` in
    `SubstraitLean/Semantic.lean`): for example a `DISTINCT` over a key is
    gone. On data that meets the preconditions it gives the same rows
    (`Rel.optimize_sound`); pass it to `sverify.engines.to_sql`, or as JSON
    to `sverify.engines.run`, instead of the transformation. None if Lean
    did not return one."""
    rewrites: list[str] = field(default_factory=list)
    """The rewrites in `optimized`, such as "DISTINCT on a key"."""
    inferred: dict[str, list[Condition]] = field(default_factory=dict)
    """The bounds inferred to rule out overflow (`infer_bounds`), per input
    table: also in `requires`, and assumed like the rest of it."""
    assumed: list[Issue] = field(default_factory=list)
    """The `SUM`s assumed to fit their type in every group (64 bits for
    integers, the result's precision for decimals), inferred
    like the bounds in `inferred`: those the inputs' row caps (`max_rows`,
    #219) and the values' range do not prove to fit. The job checks each sum
    on the data while it runs and raises if it does not fit. The proof holds under this assumption
    (`Rel.noIssue_of_sumsFit`). With `infer=False` they are errors instead."""
    params: list[str] = field(default_factory=list)
    """The `ibis.param` values the transformation was verified with
    (`verify(..., params=...)`), as `param1 (int64) = 5`: every proof is for
    these values only."""
    hints: list[str] = field(default_factory=list)
    """What to add to the contract for the `issues` it names (#379): bounds
    on a truncated timestamp column, or on the column an integer `SUM` adds
    up, with the largest group the bound lets fit."""
    bounds: dict[str, tuple[int | None, int | None]] = field(
        default_factory=dict, repr=False, compare=False
    )
    rows: int | None = None
    """At most this many output rows, from the inputs' row caps (`max_rows`
    in `requires`, `Rel.maxRows`); None if nothing bounds them."""
    semantics: Semantics = "reference"
    """What the SQL the report lifted means (`verify(semantics=...)`):
    `"reference"`, sverify's reference semantics, or `"duckdb"`, what DuckDB
    computes (#411)."""
    """The integer bounds Lean found on each integer output column, lowest
    and highest (None: unbounded), for hints."""

    @property
    def proved(self) -> bool:
        """Every postcondition holds and no runtime error is possible."""
        return all(c.proved for c in self.ensures) and not self.errors

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
    def suggestions(self) -> dict[str, dict[str, list[str]]]:
        """For each unproved postcondition with one, the preconditions per
        input table under which it would be proved, as code
        (`{"(_.y <= 100)": {"orders": ["(_.x <= 50)"]}}`)."""
        return {
            c.label: {t: [label(x) for x in cs] for t, cs in c.suggested.items()}
            for c in self.ensures
            if c.suggested
        }

    @property
    def unproved(self) -> list[CheckedCondition]:
        """The postconditions in `ensures` that were not proved."""
        return [c for c in self.ensures if not c.proved]

    def _hints(self) -> list[str]:
        """`hints`, and the general overflow hint for an overflow neither they
        nor its own `Issue.hint` cover."""
        truncated = any(h.startswith(TRUNC_HINT) for h in self.hints)
        covered = [
            i
            for i in self.errors
            if i.kind == "overflow" and (i.hint or truncated and _truncates(i.expr))
        ]
        if any(i.kind == "overflow" and i not in covered for i in self.errors):
            return [*self.hints, OVERFLOW_HINT]
        return self.hints

    def __str__(self) -> str:
        lines = []
        for table, conds in self.requires.items():
            inferred = {label(c) for c in self.inferred.get(table, [])}
            lines += [
                f"requires {table}: {c}" + (" (inferred)" if c in inferred else "") for c in conds
            ]
        for c in self.ensures:
            mark = "proved" if c.proved else f"NOT proved: {c.why}"
            if c.checked:
                mark += f"; {DATA_CHECK}"
            lines.append(f"ensures {c.label}: {mark}")
            if c.counterexample is not None:
                lines.append(f"  counterexample: {c.counterexample}")
            if c.suggested:
                lines.append(f"  {_would_hold(c)}")
        lines += [f"assumes: SUM of {i.what} {_sum_assumed(i)}" for i in self.assumed]
        for i in self.errors:
            lines.append(f"may fail: {i}" + (f" ({RUNTIME_CHECK})" if _sum(i) else ""))
            if i.hint:
                lines.append(f"  hint: {i.hint}")
        lines += [f"hint: {h}" for h in self._hints()]
        if not self.deterministic:
            lines.append(f"note: {TIES_HINT}")
        if self.params:
            lines.append(f"note: {PARAMS_NOTE}: {', '.join(self.params)}")
        lines.append(f"semantics: {self.semantics}")
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
        # Issues quote expressions, which may contain `|` (a regex, an OR).
        for i in self.errors:
            note = f" ({RUNTIME_CHECK})" if _sum(i) else ""
            rows.append(f"| runtime | ❌ may fail: {str(i).replace('|', '\\|')}{note} |")
            if i.hint:
                rows.append(f"| hint | {i.hint.replace('|', '\\|')} |")
        inferred = [f"`{label(c)}` on {t}" for t, cs in self.inferred.items() for c in cs]
        inferred += [f"SUM of `{i.what}` {_sum_assumed(i)}" for i in self.assumed]
        rows += [f"| hint | {h.replace('|', '\\|')} |" for h in self._hints()]
        facts = [f"| `{n}` | {v} |" for n, v in self.facts.items()]
        if self.rows is not None:
            facts.insert(0, f"| (rows) | at most {self.rows:,} |")
        note = [] if self.deterministic else [f"> ⚠️ {TIES_HINT}", ""]
        if self.params:
            note += [f"> ℹ️ {PARAMS_NOTE}: {', '.join(self.params)}", ""]
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


def _would_hold(c: CheckedCondition) -> str:
    """The suggestion line of an unproved postcondition."""
    parts = [
        f"{', '.join(f'`{label(x)}`' for x in cs)} in the requires of {t!r}"
        for t, cs in c.suggested.items()
    ]
    return "would hold with " + " and ".join(parts)


PARAMS_NOTE = "proved for these parameter values only"

#: How a report marks a postcondition `on_unproved="runtime"` checks on data.
DATA_CHECK = "checked on the output data"

TIES_HINT = (
    "rows may tie in the ORDER BY of a window or of first(), last() or group_concat(), so the "
    "engine decides their order. Declare `unique(...)` on the partition (or grouping) and "
    "order columns of the input."
)


class VerificationError(Exception):
    """A postcondition, or the absence of runtime errors, could not be proved.

    Import it from `sverify.errors`. The message names each unproved
    postcondition with what Lean established about it, and each possible
    runtime error, followed by the full report.

    Attributes:
        report: The `Report` of the failed proof.
    """

    def __init__(self, report: Report):
        self.report = report
        problems = [f"{c.label} ({c.why})" for c in report.unproved]
        problems += [f"no runtime error ({i})" for i in report.errors]
        super().__init__(f"could not prove: {', '.join(problems)}\n{report}")


class PreconditionError(Exception):
    """Input data violates a precondition.

    Import it from `sverify.errors`. Raised when a contracted transformation
    is called on inputs bound to a backend, or a node is refreshed (on the
    full source tables the first time, then on each batch of changes), and a
    precondition does not hold on the rows. The message says how many rows
    violate which condition, for example
    "2 row(s) of orders violate (_.amount >= 0)".
    """


class PostconditionError(Exception):
    """Output data violates a postcondition (only raised by runtime checks).

    Import it from `sverify.errors`. Raised with `on_unproved="runtime"`,
    when a postcondition Lean could not prove fails on the output rows. The
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


class Inferred(str):
    """A bound inferred to rule out an overflow (#244): a SQL condition on one
    column of an input table, labelled as the Ibis code that states it
    (`(_.amount < 2**62)`). NULL passes, since only a value can overflow. It
    is checked, proved and reported like a precondition the user wrote."""

    text: str

    def __new__(cls, sql: str, text: str) -> Inferred:
        out = super().__new__(cls, sql)
        out.text = text
        return out


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
        if lo is not None:
            v, text = _nice(lo, up=True)
            out.append(Inferred(f"{null}{sql} >= {v}", f"({ref} >= {text})"))
        if hi is not None:
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
    """The conditions of a list of `{table, col, lo, hi}` or `{table, col,
    ne}` (column positions, integer codes as strings), per table."""
    out: dict[str, list[Inferred]] = {}
    for n in needs:
        schema = schemas.get(n["table"])
        if schema is None or n["col"] >= len(schema):
            continue
        col = list(schema)[n["col"]]
        have = out.setdefault(n["table"], [])
        if "ne" in n:
            c = _ne_condition(col, schema[col], int(n["ne"]))
            new = [] if c is None else [c]
        else:
            lo, hi = (None if n[k] is None else int(n[k]) for k in ("lo", "hi"))
            new = _bound_conditions(col, schema[col], lo, hi)
        have += [c for c in new if c not in have]
    return out


def _hint(
    bound: dict | None,
    schemas: Mapping[str, ibis.Schema],
    assumable: Container[str],
) -> str | None:
    """What a report suggests for one overflow, from what the inference
    found (`SubstraitLean/Infer.lean`)."""
    if bound is None:
        return None
    if bound["why"] is not None:
        return f"no bound on an input column rules it out: it comes from {bound['why']}"
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
    if isinstance(cond, Unique):
        return f"unique({', '.join(cond.cols)})"
    if isinstance(cond, References):
        return f"references({cond.col}, {cond.table}.{cond.other})"
    if isinstance(cond, ArrivesWithin):
        return f"arrives_within({cond.col}, {show_duration(cond.lateness)})"
    if isinstance(cond, MaxRows):
        return f"max_rows({cond.n})"
    if isinstance(cond, Approx):
        return f"approx({label(cond.cond)}, rel={cond.rel:g})"
    if isinstance(cond, str):
        return cond
    if isinstance(cond, Deferred):
        return repr(cond)
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
        conds = [requires] if isinstance(requires, (str, *TableCondition)) else list(requires)
        if len(inputs) != 1:
            raise error(
                f"requires: a list of conditions needs exactly one input {kind}, and there "
                f"are {len(inputs)} ({', '.join(inputs) or 'none'}); key them by {kind}, "
                "as requires={name: [...]}"
            )
        return {inputs[0]: conds}
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
    return dict(requires)


def verify(
    transform: Transform,
    *,
    requires: Mapping[str, Sequence[Condition]] | Sequence[Condition] | None = None,
    ensures: Sequence[Condition] = (),
    tables: Mapping[str, ibis.Schema | ir.Table] | None = None,
    counterexamples: int = 200,
    params: Mapping[ir.Scalar, Any] | None = None,
    infer: bool = True,
    semantics: Semantics = "reference",
) -> Report:
    """Try to prove `ensures` about `transform` (an Ibis table expression or a
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
            `ibis.schema` accepts, or Ibis tables. Needed for SQL transforms;
            an Ibis expression's own tables are found from it.
        counterexamples: How many small inputs to try per unproved
            postcondition when searching for one that breaks it. Default 200;
            0 skips the search.
        params: Values for the `ibis.param`s of an Ibis transform, as Ibis's
            `execute(params=...)` takes them. The report is about the
            transform with these values (`bind_params`); an unbound parameter
            is refused.
        infer: Whether to infer the bounds on input columns that rule out
            integer overflow (`infer_bounds`) and assume them with
            `requires`. They are listed in `Report.inferred`. An integer
            `SUM` that may leave 64 bits is assumed to fit and checked on the
            data while the job runs (`Report.assumed`). With False, each
            overflow, `SUM`s included, is an error, and its `Issue.hint`
            suggests a bound. Default True.
        semantics: What the SQL `verify` lifts means, the transformation
            if it is a SQL string and every SQL condition: `"reference"`
            (the default), sverify's reference semantics, where an
            operation that would create a NaN raises; or `"duckdb"`, what
            DuckDB computes, NaN and ±inf included. An `sv.sql` expression
            inside an Ibis transformation keeps its own `semantics`.

    Returns:
        A `Report` with the status of each postcondition, the possible
        runtime errors, and what is known about each output column.

    Raises:
        ValueError: `requires` names an unknown table, `unique` or
            `references` names an unknown column or table, or the checker
            fails on the request (for example on a plan outside the Lean
            model).
        TypeError: An Ibis condition is given for a SQL transform.

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
    return infer_bounds(
        transform,
        requires=requires_by_input(requires, inputs),
        ensures=ensures,
        tables=tables,
        counterexamples=counterexamples,
        params=bound,
        infer=infer,
        semantics=_checked_semantics(semantics),
    )


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
    transformations) are suggested for those tables' `ensures`."""

    def once(reqs: Mapping[str, Sequence[Condition]], n: int):
        return _verify_once(transform, reqs, ensures, tables, n, params, inputs, semantics)

    if not infer:
        return _confirm_suggestions(once(requires, counterexamples)[0], requires, once)
    # Counterexamples only for the final proof.
    report, raw, schemas = once(requires, 0)
    extra = {
        t: cs for t, cs in _render_needs(raw, schemas).items() if inputs is None or t in inputs
    }
    if extra:
        widened = {t: list(cs) for t, cs in requires.items()}
        _merge(widened, extra)
        report = once(widened, counterexamples)[0]
        report.inferred = {t: list[Condition](cs) for t, cs in extra.items()}
    elif counterexamples and report.unproved:
        report = once(requires, counterexamples)[0]
    report = _confirm_suggestions(report, requires, once)
    # A SUM that may overflow is assumed to fit, and checked on the
    # data while the job runs: the row caps (#219) do not rule it out.
    report.assumed = [i for i in report.issues if _sum(i)]
    report.issues = [i for i in report.issues if not _sum(i)]
    return report


def _confirm_suggestions(report: Report, requires, once) -> Report:
    """`report` with only the suggestions a proof confirms: each unproved
    postcondition's suggested preconditions are added to `requires` (and to
    what was inferred), and kept if the postcondition is then proved."""
    ensures = []
    for c in report.ensures:
        if c.suggested:
            widened = {t: list(cs) for t, cs in requires.items()}
            _merge(widened, report.inferred)
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
    schemas = {
        name: s.schema() if isinstance(s, ir.Table) else ibis.schema(s)
        for name, s in (tables or {}).items()
    }
    if not isinstance(transform, str):
        schemas = {**leaf_tables(transform), **schemas}
    con = connect()
    for name, schema in schemas.items():
        create_table(con, name, schema)

    def plan(query: Transform) -> Any:
        return json.loads(plan_json(con, query, semantics))

    def table_ref(name: str) -> Transform:
        return f"SELECT * FROM {q(name)}" if isinstance(transform, str) else con.table(name)

    req_conds = [
        (t, c) for t, cs in requires.items() for c in cs if not isinstance(c, TableCondition)
    ]
    req_plans = [plan(condition_query(table_ref(t), c, semantics)) for t, c in req_conds]
    ens_plans = []
    for c in ensures:
        if isinstance(c, TableCondition):
            continue
        p = plan(condition_query(transform, c, semantics))
        p["relations"][0]["root"]["names"] = [label(c)]
        ens_plans.append(p)
    transform_plan = plan(transform)
    out_cols: list[str] = transform_plan["relations"][0]["root"]["names"]

    def positions(cols: Sequence[str], names: Sequence[str]) -> list[int]:
        missing = [c for c in cols if c not in names]
        if missing:
            raise ValueError(f"unique() names unknown columns: {missing}")
        return [list(names).index(c) for c in cols]

    keys = {
        t: [positions(c.cols, column_names(schemas[t])) for c in cs if isinstance(c, Unique)]
        for t, cs in requires.items()
    }
    ensures_keys = [positions(c.cols, out_cols) for c in ensures if isinstance(c, Unique)]

    def foreign_key(t: str, c: References) -> list:
        if c.table not in schemas:
            raise ValueError(f"references() names an unknown table: {c.table!r}")
        [col] = positions([c.col], column_names(schemas[t]))
        [other] = positions([c.other], column_names(schemas[c.table]))
        return [col, c.table, other]

    foreign_keys = {
        t: [foreign_key(t, c) for c in cs if isinstance(c, References)]
        for t, cs in requires.items()
    }
    caps = {
        t: min(c.n for c in cs if isinstance(c, MaxRows))
        for t, cs in requires.items()
        if any(isinstance(c, MaxRows) for c in cs)
    }
    contract = {
        "requires": req_plans,
        "ensures": ens_plans,
        "transform": transform_plan,
        "keys": keys,
        "ensures_keys": ensures_keys,
        "references": foreign_keys,
        "max_rows": caps,
    }

    code, stdout, stderr = run_checker(("--contract",), json.dumps(contract))
    if code not in (0, 4):
        raise ValueError(f"substrait-check --contract failed: {stderr.strip()}")
    out = json.loads(stdout)
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
        return search_counterexample(
            schemas,
            req_named,
            keys,
            transform_plan,
            target,
            budget=counterexamples,
            references=foreign_keys,
        )

    checked = []
    for c in ensures:
        if isinstance(c, Unique):
            ok = next(key_results)["proved"]
            value = (
                "a key"
                if ok
                else "not shown to be a key"
                if out["deterministic"]
                else "undetermined: rows may tie in an ORDER BY"
            )
            cols = next(key_iter)
            cex = None if ok else find(cols)
            checked.append(CheckedCondition(label(c), ok, value, cex))
        elif isinstance(c, References):
            checked.append(CheckedCondition(label(c), False, "foreign keys are not proved"))
        elif isinstance(c, ArrivesWithin):
            checked.append(
                CheckedCondition(label(c), False, "lateness is checked on a source's batches")
            )
        elif isinstance(c, MaxRows):
            n = out.get("rows")
            value = "no bound on the rows" if n is None else f"at most {n:,} rows"
            checked.append(CheckedCondition(label(c), n is not None and n <= c.n, value))
        else:
            e = next(rows)
            p = next(ens_iter)
            cex = None if e["proved"] else find(p)
            suggested = _suggested(e.get("suggest"), schemas, assumable)
            checked.append(
                CheckedCondition(e["name"], e["proved"], e["value"], cex, suggested=suggested)
            )
    report = Report(
        semantics=semantics,
        requires={t: [label(c) for c in cs] for t, cs in requires.items()},
        ensures=checked,
        facts={f["name"]: describe(f) for f in out["facts"]},
        deterministic=out["deterministic"],
        issues=[
            Issue(
                i["kind"],
                i["expr"],
                i["error"],
                _hint(i["bound"], schemas, assumable) if i["error"] else None,
                _sum_column(transform, i["expr"]) if i["kind"] == "SUM overflow" else None,
            )
            for i in out["issues"]
        ],
        guard_free=out["guard_free"],
        unchecked=out.get("unchecked"),
        optimized=out["optimized"],
        rewrites=out["rewrites"],
        params=bound,
        bounds=_int_bounds(out["facts"], dtypes),
        rows=out.get("rows"),
    )
    if not isinstance(transform, str) and report.issues:
        report.hints = overflow_hints(transform, requires, report)
    if not isinstance(transform, str):
        report.hints += rounding_hints(transform, ensures, checked, out["facts"], dtypes)
    return report, out["inferred"], schemas


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
    values = getattr(rel, "values", None)
    if isinstance(rel, ops.Aggregate):
        values = {**rel.groups, **rel.metrics}
    if values is not None:
        return _value_origin(values[name]) if name in values else None
    parent = getattr(rel, "parent", None)
    if parent is not None and name in parent.schema:
        return _origin(parent, name)
    return None


def _value_origin(value: Node) -> tuple[str, str] | None:
    """The base table and column a value is, if it is a column passed on
    unchanged."""
    if isinstance(value, ops.Field):
        return _origin(value.rel, value.name)
    return None


#: The bound a SUM hint proposes for an unbounded side of a column.
SUM_BOUND = 1_000_000_000


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
    report = verify(sub, requires=known, counterexamples=0, infer=False)
    lo, hi = report.bounds.get("x", (None, None))
    # A BIGINT's own range bounds nothing: any two of its values may overflow.
    lo = None if lo is None or lo <= -(2**63) else lo
    hi = None if hi is None or hi >= 2**63 - 1 else hi
    where = f"`requires` of {origin[0]}" if origin else f"`requires` (on the columns of {what})"

    def capped(n: int) -> str:
        """The row cap that proves the sum fits (#219)."""
        return (
            f"`sv.max_rows({n:_})` in {where} proves it; without a row cap, the job checks "
            "the sum as it runs"
        )

    if lo is not None and hi is not None:
        largest = max(abs(lo), abs(hi))
        if largest == 0:
            return None
        rows = (2**63 - 1) // largest
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


def _count(count: ir.Scalar) -> int:
    """The value of an Ibis count, fetched through Arrow: Ibis 12 converts
    `execute()`'s scalar through pandas, which warns under pandas 3.1
    (#479)."""
    return int(count.to_pyarrow().as_py())


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
    if isinstance(cond, References):
        other = ibis.get_backend(table).table(cond.table)
        present = table.filter(table[cond.col].notnull())
        missing: Any = present.anti_join(other, [present[cond.col] == other[cond.other]]).count()
        return _count(missing)
    if isinstance(cond, ArrivesWithin):
        # On one snapshot, only the NULLs break it; batches are checked by
        # the pipeline against the watermark.
        nulls: Any = table.filter(table[cond.col].isnull()).count()
        return _count(nulls)
    if isinstance(cond, Unique):
        total: Any = table.count()
        distinct: Any = table.select(*cond.cols).distinct().count()
        return _count(total) - _count(distinct)
    if isinstance(cond, MaxRows):
        rows: Any = table.count()
        return max(0, _count(rows) - cond.n)
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
    key = (id(con.ibis), name)
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
                table, requires={name: list(facts)}, ensures=conds, counterexamples=0, infer=False
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
        if isinstance(c, MaxRows)
        for source in [next((s for n, s in counts if n <= c.n), None)]
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
            raise PreconditionError(f"{n} {what} violate {label(c)}")
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
    `on_unproved="runtime"` and a bound input, the precondition is checked on
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
    """The postconditions `on_unproved="runtime"` checks on the result's data
    because they were not proved: on a bound result when it is built, and in
    an incremental view on every state (`IncrementalView.checked`)."""


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
    state (`on_unproved="runtime"`)."""


def view_contract(expr: ir.Table) -> ViewContract:
    """Collect the base-table preconditions of every contracted
    transformation inside `expr`. Refuses preconditions on derived inputs that
    were checked on data instead of proved: a view could not keep them true
    from base-table changes."""
    prov = _lookup(expr.op())
    if prov is not None:
        requires, unproved = prov.external, prov.unproved_links
    else:
        inner = _abstract(expr)
        requires, unproved = inner.external, inner.unproved_links
    if unproved:
        raise ValueError(
            "cannot maintain incrementally: conditions on derived inputs were "
            f"not proved ({'; '.join(unproved)})"
        )
    return ViewContract(
        {t: list(cs) for t, cs in requires.items()},
        list(prov.guarantees) if prov else [],
        prov,
        list(prov.checked) if prov else [],
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
        on_unproved: Literal["error", "runtime", "warn"],
        check_requires: bool,
        engine: Engine | None,
        infer: bool = True,
        semantics: Semantics = "reference",
    ):
        self.fn, self.ensures = fn, ensures
        self.on_unproved, self.check_requires = on_unproved, check_requires
        self.infer = infer
        self.semantics = _checked_semantics(semantics)
        self.engine = engine
        self.name: str = fn.__name__
        self.signature = inspect.signature(fn)
        self.requires: dict[str, Sequence[Condition]] = requires_by_input(
            requires, list(self.signature.parameters), "parameter", TypeError
        )
        self.last_report: Report | None = None
        """The `Report` of the proof of the postconditions in the last call,
        or None before the first call."""
        self.last_preconditions: list[Discharged] = []
        """How each precondition on a bound input was established, in the
        last call: from metadata (`sverify.io` tables) or on the data."""
        self._cache: dict[tuple, Report] = {}
        functools.update_wrapper(self, fn)

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
        key = (
            tag,
            inputs,
            infer,
            self.semantics,
            ibis.to_sql(body, dialect="duckdb"),
            tuple(sorted((n, str(s)) for n, s in leaf_tables(body).items())),
            tuple(sorted((t, tuple(label(c) for c in cs)) for t, cs in assumptions.items())),
            tuple(label(c) for c in ensures),
        )
        if key not in self._cache:
            self._cache[key] = infer_bounds(
                body,
                requires=assumptions,
                ensures=ensures,
                tables=None,
                counterexamples=200,
                params=[],
                infer=infer,
                inputs=inputs,
                semantics=self.semantics,
            )
        return self._cache[key]

    def _check_on_data(self, table: ir.Table, param: str, conds: Sequence[Condition]) -> bool:
        """Establish preconditions on a bound input, from its metadata where
        possible (`discharge`); False if it is not bound."""
        if not is_bound(table):
            return False
        self.last_preconditions += discharge(
            table, param, conds, self.engine, table_facts(table), f"row(s) of {param}"
        )
        return True

    def _link(self, param: str, value: ir.Table, conds: list[Condition]) -> _Abstraction:
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
            )
            known = list(prov.guarantees)
        else:
            # A plain Ibis expression guarantees nothing by itself, but its
            # obligations may still follow from its operations.
            inner, known = _abstract(value), []
        needed = [c for c in conds if label(c) not in {label(k) for k in known}]
        out = _Abstraction(value, {param: known + needed}, inner.external, inner.unproved_links)
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
        elif not (self.on_unproved == "runtime" and self._check_on_data(value, param, unproved)):
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
                with `"runtime"` when the result is neither bound nor a
                node).
            PostconditionError: With `on_unproved="runtime"`, an unproved
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

    def _build(self, args: Sequence[Any], kwargs: Mapping[str, Any], *, node: bool) -> ir.Table:
        """The result and its proof. A `node` result (`nodes.derive`, on
        placeholder tables) has its runtime-checked postconditions checked
        at every refresh instead of now."""
        inputs = self.signature.bind(*args, **kwargs).arguments
        self.last_preconditions = []
        result = self.fn(*args, **kwargs)
        placeholders: dict[Node, tuple[str, list[Condition]]] = {}
        base: dict[str, list[Condition]] = {}
        bound_inputs: dict[str, tuple[str, ir.Table]] = {}
        # Placeholders of plain expressions (a memtable, a filtered table):
        # their preconditions are checked on the data like a base table's.
        plain: dict[str, tuple[str, ir.Table]] = {}
        external: dict[str, list[Condition]] = {}
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
            link = self._link(param, value, conds)
            _merge(external, link.external)
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
        report = self.last_report = self._verify(
            abstraction.body, assumptions, self.ensures, "ensures", {*base, *plain}, self.infer
        )
        # Inferred bounds on the inputs are preconditions like the rest:
        # checked on the data (or proved from metadata) and passed on,
        # before any check on the output reads them.
        for t, conds in report.inferred.items():
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
        if not report.proved:
            if self.on_unproved == "warn":
                warnings.warn(str(VerificationError(report)), stacklevel=3)
            # Runtime errors cannot be checked on the data beforehand: in
            # "runtime" mode the engine raises them if they happen.
            elif self.on_unproved == "runtime" and (node or is_bound(result)):
                unproved = {c.label for c in report.unproved}
                checked = [c for c in self.ensures if label(c) in unproved]
                report = self.last_report = _marked_checked(report)
                for c in [] if node else checked:
                    if n := violations(result, c, self.engine):
                        raise PostconditionError(f"{n} output row(s) violate {label(c)}")
            else:
                raise VerificationError(report)
        _merge(external, abstraction.external)
        _merge(external, base)
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
    on_unproved: Literal["error", "runtime", "warn"] = "error",
    check_requires: bool = True,
    engine: Engine | None = None,
    infer: bool = True,
    strict: bool | None = None,
    semantics: Semantics = "reference",
) -> Callable[[Callable[..., ir.Table]], ContractedTransform]:
    """Decorate a function from Ibis tables to an Ibis table with a contract.

    `requires` maps parameter names to conditions on that input. On each call
    the postconditions are proved (cached per input schema and expression) and
    the report is kept in `.last_report`; see the module docstring. With
    `on_unproved="runtime"`, unproved postconditions are checked on the output
    data instead: on inputs bound to a connection, when the transform is
    called; on a node, at every refresh, on the rows the batch inserts, before
    its sink commits. The report marks them `checked`. `engine` says where
    those checks on data run (see the module docstring).

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
            `"error"` (the default) raises; `"runtime"` checks a postcondition
            on the output data instead (bound inputs, or a node at every
            refresh) and a precondition on a bound input's data; `"warn"`
            emits a warning and returns the result.
        check_requires: Whether to check preconditions on the data of bound
            inputs at call time. Default True.
        engine: Where checks on data run: `"duckdb"`, `"polars"` or
            `"datafusion"` run each condition's plan as Lean wrote it; None
            (the default) runs them through Ibis on the inputs' connection.
        infer: Whether to infer the bounds on input columns that rule out
            integer overflow, as `verify` does. By default (True) sverify
            infers the bounds it needs (`amount * 2` on BIGINT needs
            `_.amount < 2**62`) and treats them as preconditions: they are
            checked on the data or proved from table metadata, and reported
            as inferred (`Report.inferred`). An integer `SUM` that may leave
            64 bits is assumed to fit and checked on the data while the job
            runs (`Report.assumed`). With False, every such bound must be
            stated in `requires`: an overflow, a `SUM`'s included, fails the
            proof, and the report's hint names the bound to state.
        strict: Deprecated alias of `infer`, with the opposite polarity:
            `strict=True` is `infer=False`.
        semantics: What the contract's SQL conditions mean in its proofs,
            as `verify`'s: `"reference"` (the default) or `"duckdb"`.

    Returns:
        A decorator that turns the function into a `ContractedTransform`.

    Raises:
        TypeError: When decorating, if `requires` names a parameter the
            function does not have. Calls raise `PreconditionError`,
            `CompositionError`, `VerificationError` or `PostconditionError`
            from `sverify.errors` (see `ContractedTransform.__call__`).

    Examples:
        A contract that holds, on a source, and what Lean worked out about
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
        doubled.last_report.proved  # True
        doubled.last_report.facts["doubled"]  # 'an integer ≥ 22'
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
    if strict is not None:
        warnings.warn(
            f"transform(strict={strict}) is deprecated; write infer={not strict}",
            DeprecationWarning,
            stacklevel=2,
        )
        infer = not strict
    return lambda fn: ContractedTransform(
        fn, requires, ensures, on_unproved, check_requires, engine, infer, semantics
    )
