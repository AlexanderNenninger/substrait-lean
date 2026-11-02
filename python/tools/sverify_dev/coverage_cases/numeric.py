"""Coverage cases: elementary functions and bitwise operations
(`SubstraitLean/Numeric.lean`)."""

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
            h=t.amount.atan2(t.qty),
        ),
    ),
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

#: Spark computes these with Java's `StrictMath`, which may differ from C's
#: libm in the last bit; Snowflake does not document its implementation.
LIBM = {"snowflake": "libm", "spark": "StrictMath"}
REFUSED: dict[str, dict[str, str]] = {
    "sqrt": {"snowflake": "libm"},
    "exp": LIBM,
    "ln": LIBM,
    "log10, log2": LIBM,
    "log(base)": LIBM,
    "trigonometry": LIBM,
    "shifts": {"snowflake": "not 64-bit"},
}
NO_DATAFUSION_SQL: dict[str, str] = {
    # Ibis writes `LOG(x)` and `LOG(2, x)`, which DataFusion computes as
    # `ln x / ln b`, not as libm's `log10` and `log2` (the last bit may differ).
    "log10, log2": "Ibis's LOG(x) and LOG(2, x) are not libm's log10 and log2",
}
