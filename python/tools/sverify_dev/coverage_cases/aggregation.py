"""Coverage cases: aggregation."""

from __future__ import annotations

from ibis import _

from sverify_dev.coverage_cases._common import (
    NO_LISTS,
    NO_ROW_ORDER,
    Case,
    R,
    V,
    case,
    t,
)

CASES: list[Case] = [
    case("aggregation", "count()", V, lambda: t.aggregate(n=t.count())),
    case("aggregation", "group_by sum", V, lambda: t.group_by("name").aggregate(s=t.qty.sum())),
    case(
        "aggregation",
        "count, max, mean",
        V,
        lambda: t.group_by("name").aggregate(n=t.count(), m=t.qty.max(), a=t.amount.mean()),
    ),
    case("aggregation", "nunique", V, lambda: t.group_by("name").aggregate(n=t.id.nunique())),
    case(
        "aggregation",
        "sum(where=)",
        V,
        lambda: t.group_by("name").aggregate(s=t.qty.sum(where=t.flag)),
    ),
    case(
        "aggregation",
        "having",
        V,
        # Ibis types `having` too narrowly; it accepts deferred conditions.
        lambda: t.group_by("name").having(_.count() > 1).aggregate(n=t.count()),  # pyrefly: ignore
    ),
    case("aggregation", "value_counts", V, lambda: t.name.value_counts()),
    case("aggregation", "distinct", V, lambda: t.select("name").distinct()),
    case("aggregation", "distinct(on=)", R, lambda: t.distinct(on="name", keep="first")),
    case("aggregation", "std", R, lambda: t.aggregate(s=t.amount.std())),
    case("aggregation", "collect", V, lambda: t.group_by("name").aggregate(xs=t.qty.collect())),
    case(
        "aggregation",
        "collect ordered",
        V,
        lambda: t.group_by("name").aggregate(xs=t.qty.collect(order_by="qty")),
    ),
    case(
        "aggregation",
        "collect include_null",
        R,
        lambda: t.group_by("name").aggregate(xs=t.qty.collect(include_null=True)),
    ),
    case("aggregation", "scalar subquery", V, lambda: t.filter(t.qty > t.qty.mean())),
    case(
        "aggregation",
        "unnest",
        V,
        lambda: t.group_by("name").aggregate(xs=t.qty.collect()).unnest("xs"),
    ),
]

REFUSED: dict[str, dict[str, str]] = {
    "count, max, mean": NO_ROW_ORDER,
    "scalar subquery": NO_ROW_ORDER,
    "collect": NO_LISTS,
    "collect ordered": NO_LISTS,
    "unnest": NO_LISTS,
}

DATAFUSION_SQL = {
    "unnest": "Ibis cannot compile TableUnnest for DataFusion",
}

UNORDERED_LISTS = {"collect"}
