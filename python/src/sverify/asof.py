"""ASOF joins, built from a join, a window and a filter.

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release.

Ibis's `asof_join` compiles to DuckDB's syntax. `asof_join` here is a range
join plus `ROW_NUMBER`, which every engine runs and the checker checks like
any other plan:

1. join each left row with the right rows of the same `by` values whose `on`
   is at or before the left row's, at most `tolerance` earlier;
2. rank them per left row, latest first, and keep the first. A left row is
   a numbered row (`ROW_NUMBER()` ordered by `by` and `on`, an identity only), so rows
   that share their `by` and `on` values, or have a NULL `on`, each keep
   their own match.

The join is a range join, so the pairs of rows it compares are quadratic: each
left row with every right row of its `by` group (`pairs`). The checker reads
the as-of join off the plan (`Rel.asofSite`) and writes the count of those
pairs as a plan of its own (`AsofSite.pairs`); a run evaluates it on the
engine first and refuses more than `max_pairs` (default `MAX_PAIRS`, 10⁸),
naming the exits: `by` columns, fewer rows, a larger cap. So the cap holds
whatever the rows come from: Arrow tables, files or an engine's tables.

No theorem is about ASOF joins: the plan is proved as any plan is. What an
ASOF join promises, stated in `ensures`, is proved for each plan by the
theorems every contract rests on (`docs/proofs.md`): `on_right <= on` and
`on - on_right <= tolerance` (`contract_sound`); `tests/test_asof.py` proves
the two. The plan computes one output row per left row, but sverify does not
prove it, nor `unique(*by, on)` of the output, yet (#1517). The ranking is only
determined when no two right rows tie: without a key on `(*by, on)` on the
right side these guarantees still hold for every pick of the tied rows,
and the report is not `deterministic`.
"""

import weakref
from collections.abc import Sequence
from typing import Any, Literal

import ibis
import ibis.expr.operations as ops
import ibis.expr.types as ir
import pyarrow as pa

from sverify._weighted import _call

ROW = "_asof_row"
RANK = "_asof_rank"

MAX_PAIRS = 10**8
"""The default cap on the pairs of rows the join compares (`asof_join`'s
`max_pairs`): each left row with every right row of its `by` group. DuckDB
compares about 10⁸ pairs in 4 to 7 seconds (homelab, one thread of
`sverify.connect()`), 4·10⁸ in 24 and 1.6·10⁹ in 268; Polars's keyless join is a
cross join of the same size."""


def pairs(left: pa.Table, right: pa.Table, by: Sequence[str]) -> int:
    """The pairs of rows an as-of join compares: each left row with every right
    row of its `by` group (rows with a NULL `by` value never match)."""
    if not by:
        return left.num_rows * right.num_rows
    count = lambda t: t.group_by(list(by)).aggregate([([], "count_all")])  # noqa: E731
    both = count(left).join(count(right), list(by), right_suffix="_right")
    product = _call("multiply", both["count_all"], both["count_all_right"])
    return _call("sum", product).as_py() or 0


_CAPS: weakref.WeakKeyDictionary[Any, int | None] = weakref.WeakKeyDictionary()
"""Each `asof_join` result's `max_pairs`, by its operation."""


def max_pairs_of(expr: ir.Table) -> int | None:
    """The cap on the pairs an expression's as-of joins compare: the smallest
    `max_pairs` of the `asof_join` calls it holds; None without a cap (none
    holds one, or each has `max_pairs=None`)."""
    caps = [c for n in expr.op().find(ops.Node) if (c := _CAPS.get(n)) is not None]
    return min(caps, default=None)


def too_many(n: int, cap: int) -> str:
    """The refusal of an as-of join that compares `n` pairs, over `cap`."""
    return (
        f"asof_join compares {n:,} pairs of rows (each left row with the right rows of its by"
        f" group), over max_pairs={cap:,}: its cost is that number, quadratic in the rows. Add"
        " `by` columns that split the rows into smaller groups, join fewer rows, or raise"
        " `max_pairs` (None: no cap), which is fast on DuckDB with a `tolerance`, whose range join"
        " skips most pairs"
    )


def asof_join(
    left: ir.Table,
    right: ir.Table,
    on: str,
    by: str | Sequence[str] = (),
    tolerance: Any = None,
    *,
    how: Literal["left", "inner"] = "left",
    max_pairs: int | None = MAX_PAIRS,
) -> ir.Table:
    """Match each left row with the latest right row at or before it.

    `on` is the time column of both tables; rows match only when their `by`
    columns are equal and `left.on - tolerance <= right.on <= left.on`.
    The output has one row per left row, whatever its `by` and `on` values
    (an inner join drops the rows without a match). With `how="left"`, left
    rows without a match are kept with NULLs. The output has the left columns,
    then the right ones except `by`, with clashing names suffixed `_right`
    (so `on_right` is the time of the match).

    Args:
        left: The table whose rows are matched; one output row per left row.
        right: The table to take the latest earlier row from. For the result
            to be determined, `requires` must give it a key on `(*by, on)`.
        on: The time column, of the same name in both tables.
        by: Columns that must be equal for rows to match, as one name or a
            sequence. Default: none.
        tolerance: How much earlier than the left row a match may be (an
            Ibis interval, or a number for numeric time columns). Default
            None: no limit. The join computes `on - tolerance`, which
            overflows at the type's smallest value; a contract infers the
            lower bound on the left `on` column that rules it out.
        how: `"left"` (the default) keeps left rows without a match, with
            NULLs; `"inner"` drops them.
        max_pairs: The most pairs of rows (each left row with every right
            row of its `by` group) the join may compare, counted on the
            engine before each run (`Report.run`), whatever the tables are;
            the join is a range join, so its cost is that count, quadratic
            in the rows (an engine's range join with a `tolerance` may skip
            most of them: DuckDB's does). Above it, the run raises
            `UnsupportedError`. `None`: no cap. Default `MAX_PAIRS`, 10⁸,
            which keeps DuckDB's join under about 7 seconds.

    Returns:
        An Ibis table expression, built from a range join and `ROW_NUMBER`.

    """
    by = [by] if isinstance(by, str) else list(by)
    # The number is an identity only, ordered by `by` and `on` so that a left
    # table keyed on them has no tie there and the report can stay deterministic.
    left = left.mutate(**{ROW: ibis.row_number().over(order_by=[left[c] for c in (*by, on)])})
    preds = [left[c] == right[c] for c in by] + [right[on] <= left[on]]
    if tolerance is not None:
        preds.append(right[on] >= left[on] - tolerance)
    joined = left.join(right, preds, how=how)
    # Ibis renames the right side's clashing columns to `<name>_right`.
    latest = ibis.window(group_by=[joined[ROW]], order_by=ibis.desc(joined[f"{on}_right"]))
    ranked = joined.mutate(**{RANK: ibis.row_number().over(latest)})
    first = ranked.filter(ranked[RANK] == 0)
    out = first.drop(ROW, RANK, *[f"{c}_right" for c in by if f"{c}_right" in first.columns])
    _CAPS[out.op()] = max_pairs
    return out
