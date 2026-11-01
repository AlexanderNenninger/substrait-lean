"""Coverage cases: window functions."""

from __future__ import annotations

import ibis

from sverify_dev.coverage_cases._common import (
    FRAME_DOUBLES,
    NO_ROW_ORDER,
    Case,
    R,
    V,
    case,
    t,
)

CASES: list[Case] = [
    case(
        "windows",
        "row_number",
        V,
        lambda: t.mutate(r=ibis.row_number().over(group_by="name", order_by="ts")),
    ),
    case("windows", "lag", V, lambda: t.mutate(p=t.qty.lag().over(group_by="name", order_by="ts"))),
    case(
        "windows", "rank", V, lambda: t.mutate(r=ibis.rank().over(group_by="name", order_by="ts"))
    ),
    case(
        "windows",
        "dense_rank",
        V,
        lambda: t.mutate(r=ibis.dense_rank().over(group_by="name", order_by="ts")),
    ),
    case("windows", "cumsum", V, lambda: t.mutate(c=t.qty.cumsum(order_by="ts"))),
    case("windows", "sum over group", V, lambda: t.mutate(s=t.qty.sum().over(group_by="name"))),
    case(
        "windows",
        "rolling mean (rows)",
        R,
        lambda: t.mutate(
            m=t.amount.mean().over(ibis.window(order_by="ts", preceding=2, following=0))
        ),
    ),
    case(
        "windows",
        "rolling mean (interval)",
        R,
        lambda: t.mutate(
            m=t.amount.mean().over(
                ibis.range_window(order_by="ts", preceding=ibis.interval(minutes=5), following=0)
            )
        ),
    ),
    case("windows", "ntile", V, lambda: t.mutate(q=ibis.ntile(4).over(order_by="ts"))),
    case(
        "windows",
        "first",
        V,
        lambda: t.mutate(f=t.qty.first().over(group_by="name", order_by="ts")),
    ),
    case(
        "windows",
        "percent_rank, cume_dist",
        V,
        lambda: t.mutate(
            p=ibis.percent_rank().over(order_by="qty"), c=ibis.cume_dist().over(order_by="qty")
        ),
    ),
    case(
        "windows",
        "running mean",
        V,
        lambda: t.mutate(m=t.amount.mean().over(ibis.window(order_by="ts", following=0))),
    ),
    case(
        "windows",
        "rolling sum (interval)",
        V,
        lambda: t.mutate(
            s=t.qty.sum().over(
                ibis.range_window(order_by="ts", preceding=ibis.interval(minutes=5), following=0)
            )
        ),
    ),
    case(
        "windows",
        "rolling sum (range)",
        V,
        lambda: t.mutate(
            s=t.id.sum().over(ibis.range_window(order_by="qty", preceding=2, following=0))
        ),
    ),
    case(
        "windows",
        "last, nth",
        V,
        lambda: t.mutate(
            l=t.qty.last().over(group_by="name", order_by="ts"),
            n=t.qty.nth(1).over(group_by="name", order_by="ts"),
        ),
    ),
    case(
        "windows",
        "max, count over frame",
        V,
        lambda: t.mutate(
            b=t.qty.max().over(ibis.window(order_by="ts", preceding=1, following=1)),
            c=t.qty.count().over(ibis.window(order_by="ts", preceding=1, following=1)),
        ),
    ),
    case(
        "windows",
        "min over a sliding frame",
        R,
        lambda: t.mutate(a=t.qty.min().over(ibis.window(order_by="ts", preceding=1, following=1))),
    ),
    case(
        "windows",
        "window sum of an expression",
        R,
        lambda: t.mutate(s=(t.qty * 2).sum().over(group_by="name")),
    ),
]

REFUSED: dict[str, dict[str, str]] = {
    "row_number": NO_ROW_ORDER,
    "lag": NO_ROW_ORDER,
    "rank": NO_ROW_ORDER,
    "dense_rank": NO_ROW_ORDER,
    "cumsum": NO_ROW_ORDER,
    "sum over group": NO_ROW_ORDER,
    "ntile": NO_ROW_ORDER,
    "first": NO_ROW_ORDER,
    "percent_rank, cume_dist": NO_ROW_ORDER,
    "rolling sum (range)": NO_ROW_ORDER,
    "rolling sum (interval)": NO_ROW_ORDER,
    "running mean": FRAME_DOUBLES,
    "last, nth": NO_ROW_ORDER,
    "max, count over frame": NO_ROW_ORDER,
}

TIE_FREE = {
    "row_number",
    "lag",
    "rank",
    "dense_rank",
    "cumsum",
    "ntile",
    "first",
    "percent_rank, cume_dist",
    "rolling sum (range)",
    "rolling sum (interval)",
    "last, nth",
    "max, count over frame",
}

NO_DATAFUSION_SQL = {
    # "frame offsets for RANGE must be …": Ibis writes the bound as a cast.
    "rolling sum (interval)": "refuses Ibis's interval frame",
}
