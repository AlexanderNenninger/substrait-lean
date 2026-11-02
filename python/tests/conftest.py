"""Backends and example counts.

Every test runs under one backend, which is also a marker: `poe test-polars`
(`pytest -m polars`) runs the Polars tests, and CI runs one job per backend.
A test's backend is its `engine` parameter (or `sv_engine`, from sverify's
pytest plugin), else its `backend` mark (on the test or as the module's
`pytestmark`), else `core`: Lean, the producers, and DataFusion as the
reference. Tests comparing two engines with each other stay
in `core`. DataFusion is an optional extra of `sverify`, but the tests need it
(it is in the `dev` group); `test_without_datafusion.py` blocks it.

Modules marked `lift_backlog` build plans from SQL strings, which go through
sverify's lift (`sverify.sql_lift`). Where the lift refuses the SQL so far,
the test is reported as an expected failure, with the refusal as its reason:
the backlog of M2 (#240), listed by `pytest -rx`. It passes again once the
lift reads the SQL. Any other failure still fails.

`SVERIFY_EXAMPLES=0.25 poe test` runs every Hypothesis test with a quarter
of its examples, for a quicker local loop. Every `@settings` sets
`max_examples` itself, so a Hypothesis profile would not reach them; this
scales the settings each test carries. Unset (as in CI), the counts stay.
"""

import os
from typing import Any

import pytest
from hypothesis import settings

from sverify.engines import ENGINES

#: Keep in step with the `test-*` poe tasks and the CI matrix.
BACKENDS = ("core", *ENGINES, "snowflake", "spark")

SCALE = float(os.environ.get("SVERIFY_EXAMPLES", "1"))


def pytest_configure(config: pytest.Config) -> None:
    config.addinivalue_line("markers", "backend(name): the backend a test runs under")
    config.addinivalue_line(
        "markers", "lift_backlog: the lift refusing the test's SQL is an expected failure (#240)"
    )
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
            if isinstance(exc, Unsupported) and tb.tb_frame.f_code.co_filename.endswith(
                os.path.join("sverify", "sql_lift.py")
            ):
                return str(exc).splitlines()[0]
            tb = tb.tb_next
        exc = exc.__cause__ or exc.__context__
    return None


@pytest.hookimpl(hookwrapper=True)
def pytest_runtest_makereport(item: pytest.Item, call: pytest.CallInfo) -> Any:
    outcome = yield
    report = outcome.get_result()
    if not report.failed or call.excinfo is None or not item.get_closest_marker("lift_backlog"):
        return
    if reason := _lift_refusal(call.excinfo.value):
        report.outcome = "skipped"
        report.wasxfail = f"#240, the lift refuses: {reason}"


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
