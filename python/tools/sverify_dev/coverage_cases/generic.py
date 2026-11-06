"""Coverage cases: generic operations (#58): fallible casts, parameters and
nondeterministic functions, each verified or refused with its reason."""

from __future__ import annotations

import ibis

from sverify_dev.coverage_cases._common import (
    DUCKDB_ONLY,
    Case,
    R,
    V,
    case,
    t,
)

CASES: list[Case] = [
    case(
        "generic",
        "try_cast",
        V,
        lambda: t.select(x=t.amount.try_cast("int64"), y=t.qty.try_cast("int8")),
    ),
    # Parsing strings is not modelled.
    case("generic", "try_cast string", V, lambda: t.select(x=t.name.try_cast("int64"))),
    case("generic", "param", R, lambda: t.filter(t.qty > ibis.param(ibis.dtype("int64")))),
    case("generic", "typeof", V, lambda: t.select(x=t.qty.typeof())),
    case("generic", "random", R, lambda: t.select(x=ibis.random())),
    case("generic", "uuid", R, lambda: t.select(x=ibis.uuid())),
    case("generic", "now", R, lambda: t.select(x=ibis.now())),
    case("generic", "today", R, lambda: t.select(x=ibis.today())),
]

REFUSED: dict[str, dict[str, str]] = {
    # DuckDB only until the generated lowerings (#271).
    "try_cast": DUCKDB_ONLY,
    "try_cast string": DUCKDB_ONLY,
}

NO_DUCKDB_SQL = {
    "try_cast": "DuckDB's TRY_CAST of a double to an integer rounds, the plan's truncates",
}
