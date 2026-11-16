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
left row with every right row of its `by` group (`pairs`). `asof_join` refuses
more than `max_pairs` of them (default `MAX_PAIRS`, 10⁸) when it can count
them, and names the exits: `by` columns, fewer rows, a larger cap.

No theorem is about ASOF joins: the plan is proved as any plan is. What an
ASOF join promises, stated in `ensures`, is proved for each plan by the
theorems every contract rests on (`docs/proofs.md`): `on_right <= on` and
`on - on_right <= tolerance` (`contract_sound`), and `unique(*by, on)` of the
output where `requires` gives the left table that key (`Rel.keys_sound`);
`tests/test_asof.py` proves the three. The ranking is only
determined when no two right rows tie: without a key on `(*by, on)` on the
right side these guarantees still hold for every pick of the tied rows,
and the report is not `deterministic`.
"""

from collections.abc import Sequence
from typing import Any, Literal

import ibis
import ibis.expr.operations as ops
import ibis.expr.types as ir
import pyarrow as pa

from sverify._unsupported import Unsupported
from sverify._weighted import _call

ROW = "_asof_row"
RANK = "_asof_rank"

MAX_PAIRS = 10**8
"""The default cap on the pairs of rows the join compares (`asof_join`'s
`max_pairs`): each left row with every right row of its `by` group. DuckDB
compares about 10⁸ pairs in 4 to 7 seconds (homelab, one thread of
`sverify.connect()`), 4·10⁸ in 24 and 1.6·10⁹ in 268; Polars's keyless join is a
cross join of the same size."""


def _held(table: ir.Table) -> pa.Table | None:
    """The rows of a table bound to a `sverify.connect()` connection and held as
    Arrow, else None."""
    from sverify.engine import connection_of

    op = table.op()
    con = connection_of(table)
    if not isinstance(op, ops.DatabaseTable) or con is None or not con.has(op.name):
        return None
    held = con.get(op.name)
    return held if isinstance(held, pa.Table) else None


def pairs(left: pa.Table, right: pa.Table, by: Sequence[str]) -> int:
    """The pairs of rows an as-of join compares: each left row with every right
    row of its `by` group (rows with a NULL `by` value never match)."""
    if not by:
        return left.num_rows * right.num_rows
    count = lambda t: t.group_by(list(by)).aggregate([([], "count_all")])  # noqa: E731
    both = count(left).join(count(right), list(by), right_suffix="_right")
    product = _call("multiply", both["count_all"], both["count_all_right"])
    return _call("sum", product).as_py() or 0


def _check_pairs(left: ir.Table, right: ir.Table, by: Sequence[str], max_pairs: int | None) -> None:
    if max_pairs is None:
        return
    lt, rt = _held(left), _held(right)
    if lt is None or rt is None:
        return
    n = pairs(lt, rt, by)
    if n > max_pairs:
        raise Unsupported(
            f"asof_join compares {n:,} pairs of rows (each of {lt.num_rows:,} left rows with the"
            f" right rows of its by group), over max_pairs={max_pairs:,}: its cost is that number,"
            " quadratic in the rows. Add `by` columns that split the rows into smaller groups,"
            " join fewer rows, or raise `max_pairs` (None: no cap), which is fast on DuckDB with a"
            " `tolerance`, whose range join skips most pairs"
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
            row of its `by` group) the join may compare, counted when both
            tables are bound to a `sverify.connect()` connection and held as
            Arrow tables; the join is a range join, so its cost is that
            count, quadratic in the rows (an engine's range join with a
            `tolerance` may skip most of them: DuckDB's does). Above it,
            `UnsupportedError`. `None`: no cap. Default `MAX_PAIRS`, 10⁸,
            which keeps DuckDB's join under about 7 seconds.

    Returns:
        An Ibis table expression, built from a range join and `ROW_NUMBER`.

    Raises:
        UnsupportedError: The pairs the join compares exceed `max_pairs`.
    """
    by = [by] if isinstance(by, str) else list(by)
    _check_pairs(left, right, by, max_pairs)
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
    return first.drop(ROW, RANK, *[f"{c}_right" for c in by if f"{c}_right" in first.columns])
