"""Coverage cases: window functions."""

from __future__ import annotations

import math

import ibis

from sverify_dev.coverage_cases._common import (
    DUCKDB_ONLY,
    NO_ORDER_BY,
    Case,
    V,
    case,
    t,
)

#: The frame of "rolling variance (rows)": the row and the two before it.
ROWS_2 = ibis.window(order_by="ts", preceding=2, following=0)

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
        V,
        lambda: t.mutate(
            m=t.amount.mean().over(ibis.window(order_by="ts", preceding=2, following=0))
        ),
    ),
    case(
        "windows",
        "rolling mean (interval)",
        V,
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
        V,
        lambda: t.mutate(a=t.qty.min().over(ibis.window(order_by="ts", preceding=1, following=1))),
    ),
    case(
        "windows",
        "window sum of an expression",
        V,
        lambda: t.mutate(s=(t.qty * 2).sum().over(group_by="name")),
    ),
    case(
        "windows",
        "window over expressions",
        V,
        lambda: t.mutate(s=t.qty.sum().over(group_by=t.id % 2, order_by=t.id % 5)),
    ),
    case(
        "windows",
        "group_concat over a window",
        V,
        lambda: t.mutate(
            c=t.name.group_concat(sep="|").over(group_by="qty", order_by="id", rows=(0, None))
        ),
    ),
    # `varOf` over a frame (#54, D30).
    case(
        "windows",
        "stddev over group",
        V,
        lambda: t.mutate(s=t.amount.std().over(group_by="name")),
    ),
    case(
        "windows",
        "rolling variance (rows)",
        V,
        lambda: t.mutate(v=t.amount.var(how="pop").over(ROWS_2)),
    ),
]

REFUSED: dict[str, dict[str, str]] = {
    # A window with no ORDER BY has no SQL form on these dialects yet (#271); it
    # surfaced when the row-order refusal, which came first, went.
    "sum over group": NO_ORDER_BY,
    "window sum of an expression": NO_ORDER_BY,
    "group_concat over a window": DUCKDB_ONLY,
    "stddev over group": DUCKDB_ONLY,
    "rolling variance (rows)": DUCKDB_ONLY,
}


# A plan's frame and Ibis's own SQL may sum in another order, so variances
# agree to the last digit only up to rounding (#54).
APPROXIMATE = {"stddev over group", "rolling variance (rows)"}


def _rolling_variance_oracle() -> ibis.Table:
    """DuckDB's `VAR_POP` of one value is 0 even for NaN (upstream/bugs/DD-3.json,
    duckdb-var-pop-one-value); the reference and the plan give NaN for a frame
    with a NaN. Ibis's SQL with that handling written out."""
    nan = t.amount.isnan().cast("int64").sum().over(ROWS_2) > 0
    var = t.amount.var(how="pop").over(ROWS_2)
    return t.mutate(v=ibis.ifelse(nan, ibis.literal(math.nan), var))


# Cases whose Ibis SQL meets a DuckDB bug that the plan's SQL handles: the
# expression whose DuckDB SQL the tests take as the oracle instead.
DUCKDB_ORACLE = {"rolling variance (rows)": _rolling_variance_oracle}
