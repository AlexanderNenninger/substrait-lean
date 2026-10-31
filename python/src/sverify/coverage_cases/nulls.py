"""Coverage cases: missing values."""

from __future__ import annotations

import ibis

from sverify.coverage_cases._common import (
    Case,
    V,
    case,
    t,
)

CASES: list[Case] = [
    case("nulls", "fill_null", V, lambda: t.select(x=t.qty.fill_null(0))),
    case("nulls", "coalesce", V, lambda: t.select(x=ibis.coalesce(t.qty, t.id))),
    case("nulls", "nullif", V, lambda: t.select(x=t.qty.nullif(0))),
]
