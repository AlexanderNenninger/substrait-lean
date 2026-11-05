"""Coverage cases: lists."""

from __future__ import annotations

import ibis

from sverify_dev.coverage_cases._common import (
    NO_LISTS,
    Case,
    R,
    V,
    case,
    ls,
    t,
)

CASES: list[Case] = [
    case("lists", "unnest column", V, lambda: ls.unnest("xs")),
    case("lists", "unnest keep_empty", R, lambda: ls.unnest("xs", keep_empty=True)),
    case(
        "lists",
        "list literal",
        V,
        lambda: t.select("id", xs=ibis.literal([1, 2], "array<int64>")),
    ),
    case("lists", "list column", V, lambda: ls.filter(ls.k > 0)),
    # #804: Ibis writes it as the UNNEST of a list of structs; the producer
    # writes the UNION ALL it means.
    case(
        "lists",
        "pivot_longer",
        V,
        lambda: t.select("id", "amount", "qty").pivot_longer(
            ibis.selectors.cols("amount", "qty"), names_to="k", values_to="v"
        ),
    ),
]

REFUSED: dict[str, dict[str, str]] = {
    "unnest column": NO_LISTS,
    "list literal": NO_LISTS,
}
