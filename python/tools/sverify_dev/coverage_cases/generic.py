"""Coverage cases: generic operations (#58): fallible casts, parameters and
nondeterministic functions, each refused with its reason."""

from __future__ import annotations

import ibis

from sverify_dev.coverage_cases._common import (
    Case,
    R,
    case,
    t,
)

CASES: list[Case] = [
    case("generic", "try_cast", R, lambda: t.select(x=t.name.try_cast("int64"))),
    case("generic", "param", R, lambda: t.filter(t.qty > ibis.param("int64"))),
    case("generic", "typeof", R, lambda: t.select(x=t.qty.typeof())),
    case("generic", "random", R, lambda: t.select(x=ibis.random())),
    case("generic", "uuid", R, lambda: t.select(x=ibis.uuid())),
    case("generic", "now", R, lambda: t.select(x=ibis.now())),
    case("generic", "today", R, lambda: t.select(x=ibis.today())),
]
