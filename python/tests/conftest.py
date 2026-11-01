"""Backends and example counts.

Every test runs under one backend, which is also a marker: `poe test-polars`
(`pytest -m polars`) runs the Polars tests, and CI runs one job per backend.
A test's backend is its `engine` parameter (or `sv_engine`, from sverify's
pytest plugin), else its `backend` mark (on the test or as the module's
`pytestmark`), else `core`: Lean, the producers, and DataFusion as the
reference. Tests comparing two engines with each other stay
in `core`. DataFusion is an optional extra of `sverify`, but the tests need it
(it is in the `dev` group); `test_without_datafusion.py` blocks it.

`SVERIFY_EXAMPLES=0.25 poe test` runs every Hypothesis test with a quarter
of its examples, for a quicker local loop. Every `@settings` sets
`max_examples` itself, so a Hypothesis profile would not reach them; this
scales the settings each test carries. Unset (as in CI), the counts stay.

`SVERIFY_COMPARE_SQL=<file>` compares the SQL producers on every SQL string
the tests compile with DataFusion's (`substrait_json`): each is compiled with
Isthmus too, and a JSON line per query records whether each plan verifies and
whether both give the same rows on DuckDB. The tests' own outcome does not
change; `scripts/compare_sql_producers.py` summarises the file.
"""

import fcntl
import json
import os
from typing import Any

import pytest
from hypothesis import settings

from sverify.engines import ENGINES

#: Keep in step with the `test-*` poe tasks and the CI matrix.
BACKENDS = ("core", *ENGINES, "snowflake", "spark")

SCALE = float(os.environ.get("SVERIFY_EXAMPLES", "1"))


def _compare_sql_producers(path: str) -> None:
    """Wrap `sverify.engine.substrait_json` before the test modules import it."""
    from sverify import engine
    from sverify.testing import canonical

    datafusion_json = engine.substrait_json

    def status(con: Any, plan: str | None) -> tuple[str, list[str] | None]:
        if plan is None:
            return "refused", None
        code, out, err = engine.run_checker((), plan)
        if code != 0:
            return "rejected", None
        try:
            out = engine.run_plan(con, engine.written_plan(plan), "duckdb")
            # Positional: `SELECT *` over a join may repeat column names.
            rows = canonical(zip(*(c.to_pylist() for c in out.columns), strict=True))
        except Exception:  # noqa: BLE001 - recorded, not raised
            return "verified", None
        return "verified", rows

    def compared(con: Any, sql: str) -> str:
        plan = datafusion_json(con, sql)
        try:
            try:
                other: str | None = engine.isthmus_json(con, sql)
            except engine.SqlError:
                other = None
            (df, df_rows), (ist, ist_rows) = status(con, plan), status(con, other)
            record: dict[str, object] = {"sql": sql, "datafusion": df, "isthmus": ist}
            if df_rows is not None and ist_rows is not None:
                record["same_rows"] = df_rows == ist_rows
            with open(path, "a") as f:
                fcntl.flock(f, fcntl.LOCK_EX)
                f.write(json.dumps(record) + "\n")
        except Exception:  # noqa: BLE001, S110 - never fail the test itself
            pass
        return plan

    engine.substrait_json = compared


if path := os.environ.get("SVERIFY_COMPARE_SQL"):
    _compare_sql_producers(path)


def pytest_configure(config: pytest.Config) -> None:
    config.addinivalue_line("markers", "backend(name): the backend a test runs under")
    for name in BACKENDS:
        config.addinivalue_line("markers", f"{name}: set from the test's backend")


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
