"""Coverage cases: strings."""

from __future__ import annotations

from sverify.coverage_cases._common import (
    Case,
    V,
    case,
    t,
)

CASES: list[Case] = [
    case("strings", "upper", V, lambda: t.select(x=t.name.upper())),
    case("strings", "length", V, lambda: t.select(x=t.name.length())),
    case("strings", "concat", V, lambda: t.select(x=t.name + "!")),
    case("strings", "substr", V, lambda: t.select(x=t.name.substr(0, 2))),
    case("strings", "contains", V, lambda: t.filter(t.name.contains("a"))),
    case("strings", "startswith", V, lambda: t.filter(t.name.startswith("a"))),
    case("strings", "like", V, lambda: t.filter(t.name.like("a%"))),
    case("strings", "re_search", V, lambda: t.filter(t.name.re_search("^a"))),
    case("strings", "strip", V, lambda: t.select(x=t.name.strip())),
]
