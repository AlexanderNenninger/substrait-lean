"""Backends and example counts.

Every test runs under one backend, which is also a marker: `poe test-polars`
(`pytest -m polars`) runs the Polars tests, and CI runs one job per backend.
A test's backend is its `engine` parameter, else its `backend` mark (on the
test or as the module's `pytestmark`), else `core`: Lean, and DataFusion as
the producer and reference. Tests comparing two engines with each other stay
in `core`.

`SVERIFY_EXAMPLES=0.25 poe test` runs every Hypothesis test with a quarter
of its examples, for a quicker local loop. Every `@settings` sets
`max_examples` itself, so a Hypothesis profile would not reach them; this
scales the settings each test carries. Unset (as in CI), the counts stay.
"""

import os
from typing import Any

import pytest
from hypothesis import settings

import sverify as sv

#: Keep in step with the `test-*` poe tasks and the CI matrix.
BACKENDS = ("core", *sv.ENGINES, "snowflake", "spark")

SCALE = float(os.environ.get("SVERIFY_EXAMPLES", "1"))


def pytest_configure(config: pytest.Config) -> None:
    config.addinivalue_line("markers", "backend(name): the backend a test runs under")
    for name in BACKENDS:
        config.addinivalue_line("markers", f"{name}: set from the test's backend")


def backend(item: pytest.Item) -> str:
    callspec = getattr(item, "callspec", None)
    if callspec is not None and "engine" in callspec.params:
        return callspec.params["engine"]
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
