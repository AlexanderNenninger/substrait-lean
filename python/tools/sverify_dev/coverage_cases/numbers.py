"""Coverage cases: numbers."""

from __future__ import annotations

import ibis

from sverify_dev.coverage_cases._common import (
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
    case("numbers", "abs", V, lambda: t.select(x=t.qty.abs())),
    case("numbers", "round", V, lambda: t.select(x=t.amount.round(1))),
    case("numbers", "ceil, floor", V, lambda: t.select(x=t.amount.ceil(), y=t.amount.floor())),
    case("numbers", "power", V, lambda: t.select(x=t.qty**2)),
    case("numbers", "greatest", V, lambda: t.select(x=ibis.greatest(t.qty, 0))),
    case("numbers", "least", V, lambda: t.select(x=ibis.least(t.qty, t.id))),
    case("numbers", "clip", V, lambda: t.select(x=t.qty.clip(0, 10))),
    case("numbers", "cast int → double", V, lambda: t.select(x=t.qty.cast("float64"))),
    case("numbers", "cast int → string", V, lambda: t.select(x=t.qty.cast("string"))),
    case("numbers", "cast double → int", V, lambda: t.select(x=t.amount.cast("int64"))),
]
