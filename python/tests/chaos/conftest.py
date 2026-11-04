"""The chaos suite: crash injection into pipeline execution (`poe
test-chaos`). Every test here is marked `chaos`, which a run selects only
when its `-m` names it (`tests/conftest.py`), so `poe test`, `poe test-all`
and CI leave the suite out.

Each test appends one record to the run's ledger as soon as it finishes
(`sverify_dev.chaos`): the fault, the setup (from the `scenario` fixture),
and the outcome. A failure whose signature `known.json` lists is reported
as an expected failure, with its issue; a new one fails.
"""

from __future__ import annotations

import os
from typing import Any

import pytest

from _ledger import record
from sverify_dev import chaos


def pytest_configure(config: pytest.Config) -> None:
    # The controller names the run; xdist's workers inherit it.
    if not hasattr(config, "workerinput"):
        os.environ.setdefault("SVERIFY_CHAOS_COMMIT", chaos.commit())
        os.environ.setdefault("SVERIFY_CHAOS_RUN", chaos.run_id())
        os.environ.setdefault("SVERIFY_CHAOS_LEDGER", str(chaos.ledger_path()))


def pytest_report_header(config: pytest.Config) -> str | None:
    if "chaos" in (config.option.markexpr or ""):
        return f"chaos ledger: {os.environ.get('SVERIFY_CHAOS_LEDGER')}"
    return None


@pytest.hookimpl(tryfirst=True)
def pytest_collection_modifyitems(config: pytest.Config, items: list[pytest.Item]) -> None:
    for item in items:
        if "chaos" in item.path.parts:
            item.add_marker("chaos")


@pytest.fixture
def scenario(request: pytest.FixtureRequest) -> dict[str, Any]:
    """What the test sets up and injects, for its ledger record: `fault`
    (point, when, nth, action) and `setup`."""
    out: dict[str, Any] = {}
    request.node._chaos_scenario = out  # noqa: SLF001
    return out


@pytest.hookimpl(hookwrapper=True)
def pytest_runtest_makereport(item: pytest.Item, call: pytest.CallInfo) -> Any:
    outcome = yield
    report = outcome.get_result()
    if call.when != "call" and not (report.failed or report.skipped):
        return
    if call.when == "teardown" or not item.get_closest_marker("chaos"):
        return
    scenario = getattr(item, "_chaos_scenario", {})
    rec = record(item, report, call, scenario)
    chaos.append(chaos.ledger_path(), rec)
    if report.failed and rec["known"] is not None:
        report.outcome = "skipped"
        report.wasxfail = f"#{rec['known']}: {chaos.signature(rec)}"
