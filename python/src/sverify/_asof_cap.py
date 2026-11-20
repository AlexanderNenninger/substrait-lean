"""The cap on the pairs an as-of join compares (#1447, ruling 162 A7).

Internal: not part of sverify's public API. `sverify.asof.asof_join` records
each result's `max_pairs` here; `verify` reads the cap off a transform, and
`Report.run` refuses a run whose count (`AsofSite.pairs`, evaluated on the
engine) is over it. It sits low in the layers so that the report can read it.
"""

import weakref
from typing import Any

import ibis.expr.operations as ops
import ibis.expr.types as ir

_CAPS: weakref.WeakKeyDictionary[Any, int | None] = weakref.WeakKeyDictionary()
"""Each `asof_join` result's `max_pairs`, by its operation."""


def max_pairs_of(expr: ir.Table) -> int | None:
    """The cap on the pairs an expression's as-of joins compare: the smallest
    `max_pairs` of the `asof_join` calls it holds; None without a cap (none
    holds one, or each has `max_pairs=None`)."""
    caps = [c for n in expr.op().find(ops.Node) if (c := _CAPS.get(n)) is not None]
    return min(caps, default=None)


def too_many(n: int, cap: int) -> str:
    """The refusal of an as-of join that compares `n` pairs, over `cap`."""
    return (
        f"asof_join compares {n:,} pairs of rows (each left row with the right rows of its by"
        f" group), over max_pairs={cap:,}: its cost is that number, quadratic in the rows. Add"
        " `by` columns that split the rows into smaller groups, join fewer rows, or raise"
        " `max_pairs` (None: no cap), which is fast on DuckDB with a `tolerance`, whose range join"
        " skips most pairs"
    )
