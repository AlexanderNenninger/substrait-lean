"""The one zero-blind comparison of the tests: D31 keeps values raw and leaves
the sign of a zero open at a `MIN`, `MAX`, group key or `DISTINCT` row, and the
engines' writers differ in it, so rows compared across them read `-0.0` as
`0.0`."""

from __future__ import annotations

from collections.abc import Iterable
from typing import Any


def zero(v: Any) -> Any:
    """`v` with `-0.0` as `0.0`, in rows (tuples, lists, dicts) too."""
    if isinstance(v, float):
        return v + 0.0
    if isinstance(v, dict):
        return {k: zero(x) for k, x in v.items()}
    if isinstance(v, tuple | list):
        return type(v)(zero(x) for x in v)
    return v


def one_zero(rows: Iterable[Any]) -> str:
    """The rows' text with `-0.0` as `0.0`."""
    return repr([zero(r) for r in rows])
