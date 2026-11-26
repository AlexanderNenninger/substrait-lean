"""The route of every catalogue query and coverage case is as recorded (#1071, ruling 257 Q1).

`sverify_dev.route_pins` records `Report.route(engine)` for each, by default and with each rerun
required (`route_pins.RERUNS`: multiset, strict sequence, a tolerance on doubles), in
`tests/route_pins.json`: the class, evidence, shims, reason, lenses and rerun evidence, or the
exception a route raises. Moving the route's decision into the checker leaves every line as it is,
or each change is listed in the pull request. Each engine is its own test, in its own CI job (the
Spark one runs under `backend("spark")`); a recorded case and engine that is missing now fails.
Regenerate with `python -m sverify_dev.route_pins --write` and review the diff.
"""

import json

import pytest

from _repo import needs_repo

pytestmark = needs_repo

ENGINES = ["duckdb", "polars", pytest.param("spark", marks=pytest.mark.backend("spark"))]


@pytest.mark.parametrize("engine", ENGINES)
def test_every_route_is_as_pinned(engine: str) -> None:
    from sverify import _engines
    from sverify_dev import route_pins

    assert engine in _engines.SUPPORTED, f"{engine} is not installed: its pins cannot be checked"
    record = json.loads(route_pins.PINS.read_text())
    now = route_pins.pins((engine,))
    assert set(now) == set(record), (
        "a catalogue query or coverage case was added or removed: re-record the pins"
    )
    changed = []
    for ident, per in now.items():
        if "verify" in record[ident] or "verify" in per:
            if record[ident] != per:
                changed.append(f"{ident}: verify")
            continue
        if engine not in record[ident]:
            changed.append(f"{ident} on {engine}: no longer recorded")
        elif record[ident][engine] != per[engine]:
            changed.append(f"{ident} on {engine}")
    assert not changed, "routes changed: " + "; ".join(changed[:20])


def test_epsilon_names_every_double_output_of_every_plan() -> None:
    """#2573: over every catalogue query and coverage case that verifies, the checker's `ε`
    names each double output column (zero where every engine computes it exactly, no bound where
    it cannot bound it), so an unhandled shape never reads as exact."""
    from sverify_dev import route_pins

    missing = []
    for ident, report in route_pins._reports():
        if isinstance(report, str):
            continue
        doubles = {c for c, t in report.output.items() if t.is_floating()}
        if not doubles <= set(report._epsilon or {}):
            missing.append(f"{ident}: {sorted(doubles - set(report._epsilon or {}))}")
    assert not missing, "; ".join(missing)
