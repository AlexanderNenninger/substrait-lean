"""ASOF joins, built from a join, a window and a filter.

Internal: not part of sverify's public API (`docs/stability.md`); it may
change in any release.

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

DuckDB runs a join without a `tolerance`, on integer, date, timestamp or string
columns, as its own `ASOF JOIN` (`duckdb-asof-join`, #1447): it compares no
pairs, so its run takes no count and has no cap. At a tie on the right it may
pick another of the tied rows than the range join does; the report already
says `deterministic` is false there.

The plan is proved as any plan is. What an
ASOF join promises, stated in `ensures`, is proved for each plan by the
theorems every contract rests on (`docs/proofs.md`): `on_right <= on` and
`on - on_right <= tolerance` (`contract_sound`); `tests/test_asof.py` proves
the two. The plan computes one output row per left row. Sverify proves at most
one: a key of the left table is a key of the output (#1992), so
`unique(*by, on)` on the left gives it of the output. A `how="left"` join keeps
every left row: every result has as many rows as the left rows it numbers
(`AsofSite.left_exactly_one`, #1992). The ranking is only
determined when no two right rows tie: without a key on `(*by, on)` on the
right side these guarantees still hold for every pick of the tied rows,
and the report is not `deterministic`.
"""

from collections.abc import Sequence
from typing import Any, Literal

import ibis
import ibis.expr.types as ir

from sverify._asof_cap import _CAPS

ROW = "_asof_row"
RANK = "_asof_rank"

MAX_PAIRS = 10**8
"""The default cap on the pairs of rows the join compares (`asof_join`'s
`max_pairs`): each left row with every right row of its `by` group. DuckDB
runs a join without a `tolerance` as an `ASOF JOIN`, which compares none; its
range join (with a `tolerance`) compares about 10⁸ pairs in 4 to 7 seconds (homelab, one thread of
`sverify.connect()`), 4·10⁸ in 24 and 1.6·10⁹ in 268; Polars's keyless join is a
cross join of the same size."""


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
    rows without a match are kept with NULLs. A key of `left` that `requires`
    states is proved a key of the output. The output has the left columns,
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
            most of them: DuckDB's does). DuckDB's `ASOF JOIN`, which runs a
            join without a `tolerance`, takes no count. Above it, the run raises
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
