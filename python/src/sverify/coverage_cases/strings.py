"""Coverage cases: strings."""

from __future__ import annotations

from typing import cast

import ibis
import ibis.expr.types as ir

from sverify.coverage_cases._common import (
    Case,
    R,
    V,
    case,
    t,
)

SEP = cast(ir.StringValue, ibis.literal(", "))

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
    case("strings", "lpad", V, lambda: t.select(x=t.name.lpad(5, "-"))),
    case("strings", "rpad", V, lambda: t.select(x=t.name.rpad(t.qty))),
    case("strings", "repeat", V, lambda: t.select(x=t.name.repeat(t.qty))),
    case("strings", "reverse", V, lambda: t.select(x=t.name.reverse())),
    case("strings", "right", V, lambda: t.select(x=t.name.right(t.qty))),
    case("strings", "replace", V, lambda: t.select(x=t.name.replace("a", "o"))),
    case("strings", "replace ''", V, lambda: t.select(x=t.name.replace("", "-"))),
    case("strings", "ilike", V, lambda: t.filter(t.name.ilike("A%"))),
    case("strings", "find from", V, lambda: t.select(x=t.name.find("a", t.qty))),
    case("strings", "ascii", V, lambda: t.select(x=t.name.ascii_str())),
    case("strings", "join", V, lambda: t.select(x=SEP.join([t.name, "x", t.name]))),
    case("strings", "levenshtein", V, lambda: t.select(x=t.name.levenshtein("bob"))),
    case("strings", "find_in_set", V, lambda: t.select(x=t.name.find_in_set(["bob", "ada"]))),
    case("strings", "capitalize", V, lambda: t.select(x=t.name.capitalize())),
    case("strings", "slice", V, lambda: t.select(x=t.name[1:3], y=t.name[:2], z=t.name[1:])),
    case("strings", "translate", R, lambda: t.select(x=t.name.translate("ab", "xy"))),
]

#: Rust's `replace` puts the replacement around every character for an empty
#: pattern; the SQL engines return the string unchanged.
_EMPTY_PATTERN = "replace with an empty pattern differs between engines"
REFUSED: dict[str, dict[str, str]] = {
    "replace ''": {"duckdb": _EMPTY_PATTERN, "snowflake": _EMPTY_PATTERN, "spark": _EMPTY_PATTERN},
}
