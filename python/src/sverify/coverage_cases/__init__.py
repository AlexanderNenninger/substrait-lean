"""The cases of `sverify.coverage`, one module per area of the Ibis API.

Each area module defines `CASES`, the area's cases in README order, and, where
it has any, the area's entries of `REFUSED`, `TIE_FREE`, `NO_DATAFUSION_SQL`,
`DATAFUSION_SQL` and `UNORDERED_LISTS` (`sverify.coverage` says what each
means). This module combines them in `AREAS` order, which is the order of
the README table.

A new case goes at the end of its area's `CASES`; a new area is a new module
added to `AREAS`. Areas live in separate files so that pull requests for
different areas do not touch the same lines.
"""

from __future__ import annotations

from types import ModuleType
from typing import Any

from sverify.coverage_cases import (
    aggregation,
    joins,
    lists,
    nulls,
    numbers,
    rows,
    strings,
    temporal,
    windows,
)
from sverify.coverage_cases._common import Case

AREAS: tuple[ModuleType, ...] = (
    rows,
    joins,
    aggregation,
    lists,
    windows,
    numbers,
    nulls,
    strings,
    temporal,
)


def _merged(name: str) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for area in AREAS:
        part = getattr(area, name, {})
        if clash := out.keys() & part:
            raise ValueError(f"{name}: {sorted(clash)} in two areas")
        out.update(dict.fromkeys(part) if isinstance(part, set) else part)
    return out


CASES: list[Case] = [c for area in AREAS for c in area.CASES]
REFUSED: dict[str, dict[str, str]] = _merged("REFUSED")
TIE_FREE: set[str] = set(_merged("TIE_FREE"))
NO_DATAFUSION_SQL: dict[str, str] = _merged("NO_DATAFUSION_SQL")
DATAFUSION_SQL: dict[str, str] = _merged("DATAFUSION_SQL")
UNORDERED_LISTS: set[str] = set(_merged("UNORDERED_LISTS"))

if len({c.label for c in CASES}) != len(CASES):
    raise ValueError("two coverage cases have the same label")
