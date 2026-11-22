"""The route of every catalogue query and coverage case is as recorded (#1071, ruling 257 Q1).

`sverify_dev.route_pins` records `Report.route(engine)` for each, with and without an exact rerun
required, in `tests/route_pins.json`: the class, evidence, shims, reason, lenses and rerun evidence.
Moving the route's decision into the checker leaves every line as it is, or each change is listed
in the pull request. An engine that is not installed is left out of the comparison. Regenerate with
`python -m sverify_dev.route_pins --write` and review the diff.
"""

import json

import pytest

from _repo import needs_repo

pytestmark = [needs_repo, pytest.mark.slow]


def test_every_route_is_as_pinned() -> None:
    from sverify_dev import route_pins

    record = json.loads(route_pins.PINS.read_text())
    now = route_pins.pins()
    assert set(now) == set(record), (
        "a catalogue query or coverage case was added or removed: re-record the pins"
    )
    changed = []
    for ident, per in now.items():
        for engine, routes in per.items():
            if engine != "verify" and engine not in record[ident]:
                continue  # recorded where the engine was not installed
            if record[ident].get(engine) != routes:
                changed.append(f"{ident} on {engine}")
    assert not changed, "routes changed: " + "; ".join(changed[:20])
