"""Coverage cases: numbers."""

from __future__ import annotations

from decimal import Decimal

import ibis

from sverify_dev.coverage_cases._common import (
    NOT_ON_POLARS,
    Case,
    V,
    case,
    t,
)

CASES: list[Case] = [
    case("numbers", "+, -, *", V, lambda: t.select(x=t.qty * 2 - t.id + 1)),
    case("numbers", "float division", V, lambda: t.select(x=t.qty / 2)),
    case("numbers", "integer division", V, lambda: t.select(x=t.qty // 2)),
    case("numbers", "mod", V, lambda: t.select(x=t.qty % 3)),
    case(
        "numbers",
        "decimal mod",
        V,
        lambda: t.select(
            x=t.qty.cast("decimal(10, 2)") % ibis.literal(Decimal("0.7"), "decimal(3, 1)")
        ),
    ),
    case("numbers", "abs", V, lambda: t.select(x=t.qty.abs())),
    case("numbers", "round", V, lambda: t.select(x=t.amount.round(1))),
    case("numbers", "ceil, floor", V, lambda: t.select(x=t.amount.ceil(), y=t.amount.floor())),
    case("numbers", "power", V, lambda: t.select(x=t.qty**2)),
    case("numbers", "greatest", V, lambda: t.select(x=ibis.greatest(t.qty, 0))),
    case("numbers", "least", V, lambda: t.select(x=ibis.least(t.qty, t.id))),
    case("numbers", "clip", V, lambda: t.select(x=t.qty.clip(0, 10))),
    case("numbers", "cast int → double", V, lambda: t.select(x=t.qty.cast("float64"))),
    case("numbers", "cast int → string", V, lambda: t.select(x=t.qty.cast("string"))),
    case("numbers", "cast boolean → string", V, lambda: t.select(x=t.flag.cast("string"))),
    case("numbers", "cast date → string", V, lambda: t.select(x=t.ts.date().cast("string"))),
    case("numbers", "cast double → int", V, lambda: t.select(x=t.amount.cast("int64"))),
]

REFUSED: dict[str, dict[str, str]] = {
    # The date's text goes through a Date to timestamp cast the engines lack (#271).
    "cast date → string": NOT_ON_POLARS,
    # Snowflake's decimals are not the reference's yet (#27).
    "decimal mod": {"snowflake": "does not compute decimals as the reference does"},
}

NO_DUCKDB_SQL = {
    "cast double → int": "DuckDB's cast of a double to an integer rounds, the plan's truncates",
}
