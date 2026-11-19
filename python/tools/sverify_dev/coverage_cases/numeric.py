"""Coverage cases: elementary functions and bitwise operations
(`core/Sverify/Core/Numeric.lean`)."""

from __future__ import annotations

import ibis

from sverify_dev.coverage_cases._common import (
    Case,
    V,
    case,
    t,
)

CASES: list[Case] = [
    case("math", "sign", V, lambda: t.select(x=t.amount.sign(), y=t.qty.sign())),
    case("math", "sqrt", V, lambda: t.select(x=t.amount.sqrt(), y=t.qty.sqrt())),
    case("math", "exp", V, lambda: t.select(x=t.amount.exp())),
    case("math", "ln", V, lambda: t.select(x=t.amount.ln())),
    case("math", "log10, log2", V, lambda: t.select(x=t.amount.log10(), y=t.amount.log2())),
    case("math", "log(base)", V, lambda: t.select(x=t.amount.log(3), y=t.amount.log(t.qty))),
    case(
        "math",
        "trigonometry",
        V,
        lambda: t.select(
            a=t.amount.sin(),
            b=t.amount.cos(),
            c=t.amount.tan(),
            d=t.amount.cot(),
            e=t.amount.asin(),
            f=t.amount.acos(),
            g=t.amount.atan(),
        ),
    ),
    case("math", "atan2", V, lambda: t.select(x=t.amount.atan2(t.qty))),
    case(
        "math", "degrees, radians", V, lambda: t.select(x=t.amount.degrees(), y=t.amount.radians())
    ),
    case("math", "pi, e", V, lambda: t.select(x=t.amount * ibis.pi + ibis.e)),
    case("math", "isinf", V, lambda: t.filter(t.amount.isinf())),
    case(
        "math",
        "bitwise",
        V,
        lambda: t.select(a=t.qty & 3, b=t.qty | t.id, c=t.qty ^ t.id, d=~t.qty),
    ),
    case("math", "shifts", V, lambda: t.select(a=t.qty << 1, b=t.qty >> t.id)),
    case("math", "logical xor", V, lambda: t.filter(t.flag ^ (t.qty > 0))),
]

#: Snowflake does not document its implementation of these.
LIBM = {"snowflake": "libm"}
REFUSED: dict[str, dict[str, str]] = {
    "sqrt": {"snowflake": "libm"},
    "exp": LIBM,
    "ln": LIBM,
    "log10, log2": LIBM,
    "log(base)": LIBM,
    "trigonometry": LIBM,
    "atan2": {**LIBM, "spark": "StrictMath"},
    "shifts": {"snowflake": "not 64-bit"},
}

#: Polars runs `log10` and `log2` as `ln(x) / ln(b)`, within 2.1 ulp of libm's
#: (the `fp.log` row, polars-ulp-libm), so its result may differ from DuckDB's
#: libm in the last bit: `log10(0.5)` is -0.30102999566398114 on Polars 2.1.0
#: and -0.3010299956639812 on libm, 1 ulp apart. The comparison is to nine
#: significant digits (`test_backends.approximately`), far wider than 2.1 ulp.
#: Spark's functions are Java's (`spark-ulp-libm`), a few ulps from libm's, so `exp`, `ln`,
#: `log(base)` and the trigonometric functions are compared the same way.
APPROXIMATE = {"exp", "ln", "log10, log2", "log(base)", "trigonometry"}

NO_DUCKDB_SQL = {
    "sign": "DuckDB's sign of NaN is 0, the plan's NaN",
    "shifts": "DuckDB raises on a left shift of a negative number",
}
