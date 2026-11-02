"""Coverage cases: joins and set operations."""

from __future__ import annotations

from sverify_dev.coverage_cases._common import (
    NO_ROW_ORDER,
    Case,
    R,
    V,
    case,
    exists,
    t,
    u,
)

CASES: list[Case] = [
    case("joins", "inner join", V, lambda: t.join(u, "name")),
    case("joins", "non-equi join", V, lambda: t.join(u, t.name < u.name)),
    case("joins", "cross join", V, lambda: t.cross_join(u)),
    case("joins", "left join", V, lambda: t.left_join(u, "name")),
    case("joins", "right join", V, lambda: t.right_join(u, "name")),
    case("joins", "outer join", V, lambda: t.outer_join(u, "name")),
    case("joins", "semi join", V, lambda: t.semi_join(u, "name")),
    case("joins", "anti join", V, lambda: t.anti_join(u, "name")),
    case("joins", "isin subquery", V, lambda: t.filter(t.name.isin(u.name))),
    case("joins", "isin subquery in select", V, lambda: t.select("id", x=t.name.isin(u.name))),
    case(
        "joins",
        "notin subquery",
        V,
        lambda: t.filter(t.name.notin(u.name) | t.flag),
    ),
    case("joins", "scalar subquery in select", V, lambda: t.select("id", n=u.count())),
    case(
        "joins",
        "scalar subquery, one row",
        V,
        lambda: t.select("id", r=u.order_by("name").limit(1).name.as_scalar()),
    ),
    case(
        "joins",
        "scalar subquery, many rows",
        R,
        lambda: t.select("id", r=u.filter(u.region == "eu").name.as_scalar()),
    ),
    case("joins", "exists", V, lambda: t.filter((u.name == t.name).any())),
    case("joins", "not exists", V, lambda: t.filter(~(u.name == t.name).any())),
    case(
        "joins",
        "exists, uncorrelated",
        V,
        lambda: t.select("id", e=exists(u.filter(u.region == "eu"))),
    ),
    case(
        "joins",
        "correlated scalar subquery",
        R,
        lambda: t.filter(u.filter(u.name == t.name).count() > 0),  # pyrefly: ignore
    ),
    case("joins", "union all", V, lambda: t.select("name").union(u.select("name"))),
    case(
        "joins",
        "union distinct",
        V,
        lambda: t.select("name").union(u.select("name"), distinct=True),
    ),
    case("joins", "intersect", V, lambda: t.select("name").intersect(u.select("name"))),
    case("joins", "difference", V, lambda: t.select("name").difference(u.select("name"))),
    case(
        "joins",
        "intersect all",
        V,
        lambda: t.select("name").intersect(u.select("name"), distinct=False),
    ),
    case(
        "joins",
        "difference all",
        V,
        lambda: t.select("name").difference(u.select("name"), distinct=False),
    ),
]

REFUSED: dict[str, dict[str, str]] = {
    "non-equi join": {
        "polars": "lt of String",
        "duckdb": "ordering comparisons of str values",
        "snowflake": "ordering comparisons of str values",
        "spark": "ordering comparisons of str values",
    },
    "scalar subquery, one row": NO_ROW_ORDER,
}

DATAFUSION_SQL = {
    "intersect all": "DataFusion 51 plans INTERSECT ALL as a semi join: every left copy stays",
    "difference all": "DataFusion 51 plans EXCEPT ALL as an anti join: every left copy goes",
    "isin subquery in select": "DataFusion 51 cannot run IN (subquery) outside a filter",
    "exists, uncorrelated": "DataFusion 51 cannot run EXISTS (subquery) outside a filter",
    "notin subquery": "DataFusion 51's NOT IN (subquery) ignores NULLs in the subquery",
}
