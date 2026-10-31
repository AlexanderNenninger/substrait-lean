"""Coverage cases: rows and columns."""

from __future__ import annotations

import ibis
from ibis import _

from sverify.coverage_cases._common import (
    NO_ROW_ORDER,
    Case,
    M,
    R,
    V,
    case,
    sql_query,
    sql_view,
    t,
)

CASES: list[Case] = [
    case("rows", "filter, select", V, lambda: t.filter(t.qty > 1).select("id", "qty")),
    case("rows", "mutate", V, lambda: t.mutate(y=t.qty + 1)),
    case("rows", "drop, rename", V, lambda: t.drop("flag").rename(q="qty")),
    case("rows", "drop_null", V, lambda: t.drop_null(["qty"])),
    case("rows", "isnull", V, lambda: t.filter(t.qty.isnull())),
    case("rows", "between", V, lambda: t.filter(t.qty.between(1, 5))),
    case("rows", "isin", V, lambda: t.filter(t.qty.isin([1, 2, 3]))),
    case("rows", "notin", V, lambda: t.filter(t.qty.notin([1, 2]))),
    case("rows", "ifelse", V, lambda: t.select(x=ibis.ifelse(t.flag, 1, 0))),
    case("rows", "cases", V, lambda: t.select(x=ibis.cases((t.qty > 5, "big"), else_="small"))),
    case("rows", "order_by", V, lambda: t.order_by("qty")),
    case("rows", "limit", V, lambda: t.limit(3)),
    case("rows", "limit with offset", V, lambda: t.limit(3, offset=1)),
    case("rows", "order_by + limit", V, lambda: t.order_by(ibis.desc("qty")).limit(3)),
    case("rows", "sample", R, lambda: t.sample(0.5)),
    case("rows", "order_by expression", V, lambda: t.order_by(t.qty + 1)),
    # Ibis's annotations are narrower than what it accepts.
    case("rows", "limit expression", R, lambda: t.limit(ibis.literal(2) + 1)),  # pyrefly: ignore
    case("rows", "limit count()", R, lambda: t.limit(t.count())),  # pyrefly: ignore
    case("rows", "fill_null table", V, lambda: t.fill_null({"qty": 0, "name": "?"})),  # pyrefly: ignore
    case("rows", "fill_null all", V, lambda: t.select("id", "qty").fill_null(0)),  # pyrefly: ignore
    case("rows", "memtable", V, lambda: t.join(M, t.name == M.name)),
    case("rows", "constant table", V, lambda: ibis.literal(1, "int64").name("one").as_table()),
    case("rows", "alias", V, lambda: t.alias("v").filter(_.qty > 1)),
    case("rows", "sql view", V, lambda: sql_view(t, "SELECT name, qty FROM v WHERE qty > 1")),
    case(
        "rows",
        "sql query",
        V,
        lambda: sql_query(
            "SELECT t.name, region FROM t JOIN u ON t.name = u.name",
            {"name": "string", "region": "string"},
        ),
    ),
]

REFUSED: dict[str, dict[str, str]] = {
    "order_by": NO_ROW_ORDER,
    "order_by expression": NO_ROW_ORDER,
    "limit": NO_ROW_ORDER,
    "limit with offset": NO_ROW_ORDER,
    "order_by + limit": NO_ROW_ORDER,
}

TIE_FREE = {"order_by", "order_by expression"}
