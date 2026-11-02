"""Coverage cases: aggregation."""

from __future__ import annotations

from ibis import _

from sverify_dev.coverage_cases._common import (
    DUCKDB_ONLY,
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
    case(
        "aggregation",
        "arithmetic over aggregates",
        V,
        lambda: t.group_by("name").aggregate(
            ratio=t.qty.sum() / t.id.sum(), spread=t.qty.max() - t.qty.min()
        ),
    ),
    case("aggregation", "nunique", V, lambda: t.group_by("name").aggregate(n=t.id.nunique())),
    case(
        "aggregation",
        "first, last ordered",
        V,
        lambda: t.group_by("name").aggregate(
            f=t.qty.first(order_by=t.id), l=t.qty.last(order_by=t.id)
        ),
    ),
    case(
        "aggregation",
        "group_concat ordered",
        V,
        lambda: t.group_by("qty").aggregate(s=t.name.group_concat(", ", order_by=t.id)),
    ),
    case(
        "aggregation",
        "group_concat",
        R,
        lambda: t.group_by("qty").aggregate(s=t.name.group_concat(", ")),
    ),
    case(
        "aggregation",
        "approx_nunique",
        R,
        lambda: t.group_by("name").aggregate(n=t.id.approx_nunique()),
    ),
    case(
        "aggregation",
        "any, all",
        V,
        lambda: t.group_by("name").aggregate(a=(t.qty > 0).any(), b=t.flag.all()),
    ),
    case(
        "aggregation",
        "bit_and, bit_or, bit_xor",
        V,
        lambda: t.group_by("name").aggregate(
            a=t.qty.bit_and(), o=t.qty.bit_or(), x=t.qty.bit_xor()
        ),
    ),
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
    case("aggregation", "distinct(on=)", V, lambda: t.distinct(on="name", keep="first")),
    case("aggregation", "std", V, lambda: t.aggregate(s=t.amount.std())),
    case(
        "aggregation",
        "cov, corr",
        V,
        lambda: t.group_by("name").aggregate(
            c=t.amount.cov(t.qty), r=t.amount.corr(t.qty, how="pop")
        ),
    ),
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
    "cov, corr": DUCKDB_ONLY,
    "first, last ordered": DUCKDB_ONLY,
    "distinct(on=)": DUCKDB_ONLY,
    "group_concat ordered": DUCKDB_ONLY,
    "count, max, mean": NO_ROW_ORDER,
    "scalar subquery": NO_ROW_ORDER,
    "collect": NO_LISTS,
    "collect ordered": NO_LISTS,
    "unnest": NO_LISTS,
}

UNORDERED_LISTS = {"collect"}

APPROXIMATE = {"std", "cov, corr"}

NO_DUCKDB_SQL = {
    # CORR is NULL for fewer than two pairs or a flat side (the SQL standard);
    # DuckDB's own CORR gives NaN there (#54).
    "cov, corr": "DuckDB's CORR gives NaN where the reference gives NULL",
    # Rows tied in the order go in Lean's list order in the written plan; in
    # Ibis's own SQL, in DuckDB's (`Rel.windowsTotal` reports it, #55).
    "first, last ordered": "ties in ORDER BY are the engine's",
    # Without an order, Ibis's own FIRST takes any row's value.
    "distinct(on=)": "FIRST without ORDER BY is any row's value",
    "group_concat ordered": "ties in ORDER BY are the engine's",
}
