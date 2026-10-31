"""ASOF joins on DataFusion, built from operators Lean verifies.

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release.

DataFusion has no ASOF join, and Ibis's `asof_join` compiles to DuckDB's
syntax. `asof_join` here is a range join plus `ROW_NUMBER`, which DataFusion
runs and Lean checks like any other plan:

1. join each left row with the right rows of the same `by` values whose `on`
   is at or before the left row's, at most `tolerance` earlier;
2. rank them per left row, latest first, and keep the first.

Lean then proves what an ASOF join promises: one output row per left row
(`unique(*by, on)`, from `ROW_NUMBER` keys and the join's key analysis),
`on_right <= on` and `on - on_right <= tolerance`. The ranking is only
determined when no two right rows tie, so `requires` must give the right
side a key on `(*by, on)`; without it every postcondition is `undetermined`.
"""

from collections.abc import Sequence
from typing import Any, Literal

import ibis
import ibis.expr.types as ir

RANK = "_asof_rank"


def asof_join(
    left: ir.Table,
    right: ir.Table,
    on: str,
    by: str | Sequence[str] = (),
    tolerance: Any = None,
    *,
    key: Sequence[str] | None = None,
    how: Literal["left", "inner"] = "left",
) -> ir.Table:
    """Match each left row with the latest right row at or before it.

    `on` is the time column of both tables; rows match only when their `by`
    columns are equal and `left.on - tolerance <= right.on <= left.on`.
    `key` identifies left rows (default: `by` and `on`); the left table must
    not repeat it. With `how="left"`, left rows without a match are kept
    with NULLs. The output has the left columns, then the right ones except
    `by`, with clashing names suffixed `_right` (so `on_right` is the time
    of the match).
    """
    by = [by] if isinstance(by, str) else list(by)
    key = list(key) if key is not None else [*by, on]
    preds = [left[c] == right[c] for c in by] + [right[on] <= left[on]]
    if tolerance is not None:
        preds.append(right[on] >= left[on] - tolerance)
    joined = left.join(right, preds, how=how)
    # Ibis renames the right side's clashing columns to `<name>_right`.
    latest = ibis.window(
        group_by=[joined[c] for c in key], order_by=ibis.desc(joined[f"{on}_right"])
    )
    ranked = joined.mutate(**{RANK: ibis.row_number().over(latest)})
    first = ranked.filter(ranked[RANK] == 0)
    return first.drop(RANK, *[f"{c}_right" for c in by if f"{c}_right" in first.columns])
