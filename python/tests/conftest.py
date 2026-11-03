"""Backends and example counts.

Every test runs under one backend, which is also a marker: `poe test-polars`
(`pytest -m polars`) runs the Polars tests, and CI runs one job per backend.
A test's backend is its `engine` parameter (or `sv_engine`, from sverify's
pytest plugin), else its `backend` mark (on the test or as the module's
`pytestmark`), else `core`: Lean, the producers, and DuckDB as the oracle.
Tests comparing two engines with each other stay in `core`. DataFusion is an
optional extra of `sverify`, but the tests need it (it is in the `dev`
group); `test_without_datafusion.py` blocks it.

`tests/lift_backlog.txt` lists the tests that wait on SQL the lift
(`sverify.sql_lift`) does not read yet: the backlog of M2 (#240). A listed
test that fails because the lift refuses its SQL is an expected failure,
with the refusal as its reason (`pytest -rx`); one that fails otherwise
fails, and one that passes fails too, until its line is removed (strict). A
test that is not listed fails as usual, whatever refuses it.
`SVERIFY_LIFT_BACKLOG=<file> pytest …` writes the tests the lift refuses to
`<file>`, to start or prune the list.

`SVERIFY_EXAMPLES=0.25 poe test` runs every Hypothesis test with a quarter
of its examples, for a quicker local loop. Every `@settings` sets
`max_examples` itself, so a Hypothesis profile would not reach them; this
scales the settings each test carries. Unset (as in CI), the counts stay.
"""

import os
from pathlib import Path
from typing import Any

import pytest
from hypothesis import settings

from sverify.engines import ENGINES

#: Keep in step with the `test-*` poe tasks and the CI matrix.
BACKENDS = ("core", *ENGINES, "snowflake", "spark")

SCALE = float(os.environ.get("SVERIFY_EXAMPLES", "1"))


def pytest_configure(config: pytest.Config) -> None:
    config.addinivalue_line("markers", "backend(name): the backend a test runs under")
    config._lift_refused = []  # type: ignore[attr-defined]
    for name in BACKENDS:
        config.addinivalue_line("markers", f"{name}: set from the test's backend")


def _lift_refusal(exc: BaseException | None) -> str | None:
    """The lift's refusal behind an exception (it, or what it was raised
    from), if that is what it is."""
    from sverify.plan_json import Unsupported

    seen: set[int] = set()
    while exc is not None and id(exc) not in seen:
        seen.add(id(exc))
        tb = exc.__traceback__
        while tb is not None:
            if (
                isinstance(exc, Unsupported)
                and os.path.join("sverify", "sql_lift", "") in tb.tb_frame.f_code.co_filename
            ):
                return str(exc).splitlines()[0]
            tb = tb.tb_next
        exc = exc.__cause__ or exc.__context__
    return None


#: The tests that wait on the lift (`tests/lift_backlog.txt`), by node id.
BACKLOG = {
    line.strip()
    for line in (Path(__file__).parent / "lift_backlog.txt").read_text().splitlines()
    if line.strip() and not line.startswith("#")
}


@pytest.hookimpl(hookwrapper=True)
def pytest_runtest_makereport(item: pytest.Item, call: pytest.CallInfo) -> Any:
    outcome = yield
    report = outcome.get_result()
    listed = item.nodeid in BACKLOG
    if report.failed and call.excinfo is not None:
        reason = _lift_refusal(call.excinfo.value)
        if reason is None:
            return
        if os.environ.get("SVERIFY_LIFT_BACKLOG"):
            item.config._lift_refused.append(item.nodeid)  # type: ignore[attr-defined]
        if listed:
            report.outcome = "skipped"
            report.wasxfail = f"#240, the lift refuses: {reason}"
    elif listed and call.when == "call" and report.passed:
        report.outcome = "failed"
        report.longrepr = (
            f"{item.nodeid} passes: the lift reads its SQL now, so remove it from "
            "tests/lift_backlog.txt"
        )


def pytest_sessionfinish(session: pytest.Session) -> None:
    if path := os.environ.get("SVERIFY_LIFT_BACKLOG"):
        refused = getattr(session.config, "_lift_refused", [])
        with open(path, "a") as f:
            f.writelines(f"{n}\n" for n in refused)


def backend(item: pytest.Item) -> str:
    callspec = getattr(item, "callspec", None)
    for param in ("engine", "sv_engine"):  # `sv_engine`: sverify's pytest plugin
        if callspec is not None and param in callspec.params:
            return callspec.params[param]
    if mark := item.get_closest_marker("backend"):
        return mark.args[0]
    return "core"


def pytest_collection_modifyitems(items: list[pytest.Item]) -> None:
    for item in items:
        name = backend(item)
        if name not in BACKENDS:
            raise pytest.UsageError(f"{item.nodeid}: unknown backend {name!r}")
        item.add_marker(name)
    if SCALE == 1:
        return
    # Parametrized items share one test function: scale each once.
    tests: dict[int, Any] = {}
    for item in items:
        test = getattr(item, "obj", None)
        if hasattr(test, "hypothesis"):
            tests[id(test)] = test
    for test in tests.values():
        given = test._hypothesis_internal_use_settings  # noqa: SLF001
        test._hypothesis_internal_use_settings = settings(  # noqa: SLF001
            given, max_examples=max(1, round(given.max_examples * SCALE))
        )
