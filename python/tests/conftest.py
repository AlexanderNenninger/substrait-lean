"""`SVERIFY_EXAMPLES=0.25 poe test` runs every Hypothesis test with a quarter
of its examples, for a quicker local loop. Every `@settings` sets
`max_examples` itself, so a Hypothesis profile would not reach them; this
scales the settings each test carries. Unset (as in CI), the counts stay."""

import os
from typing import Any

import pytest
from hypothesis import settings

SCALE = float(os.environ.get("SVERIFY_EXAMPLES", "1"))


def pytest_collection_modifyitems(items: list[pytest.Item]) -> None:
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
