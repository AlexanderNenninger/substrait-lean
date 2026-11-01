"""sverify's pytest plugin: fixtures for testing transforms and contracts.

Installing sverify registers it (the `pytest11` entry point `sverify`);
`pytest -p no:sverify` turns it off.

* `sv_engine` runs a test once per installed engine
  (`sverify.testing.installed_engines`), or per engine of
  `--sv-engines=duckdb,polars` (which may name `spark`).
* `sv_source` is `sverify.testing.source`: rows as an in-memory source.

The assertions are in `sverify.testing`. sverify itself is imported only
when a test uses a fixture, so the plugin costs nothing in a test run that
does not use it.
"""

from __future__ import annotations

from collections.abc import Callable
from typing import Any

import pytest


def pytest_addoption(parser: pytest.Parser) -> None:
    group = parser.getgroup("sverify")
    group.addoption(
        "--sv-engines",
        default=None,
        metavar="NAMES",
        help="comma-separated engines for the sv_engine fixture "
        "(duckdb, polars, datafusion, spark); default: every installed engine",
    )


def _engines(config: pytest.Config) -> list[str]:
    names = config.getoption("--sv-engines")
    if names:
        return [n.strip() for n in names.split(",") if n.strip()]
    from sverify.testing import installed_engines

    return list(installed_engines())


def pytest_generate_tests(metafunc: pytest.Metafunc) -> None:
    if "sv_engine" in metafunc.fixturenames:
        engines = _engines(metafunc.config)
        metafunc.parametrize("sv_engine", engines, ids=engines, indirect=True)


@pytest.fixture
def sv_engine(request: pytest.FixtureRequest) -> str:
    """The engine this run of the test uses: one of the installed engines,
    or of `--sv-engines`. Pass it as `engine=` to `Node.refresh` or
    `sverify.testing.assert_contract`."""
    return request.param


@pytest.fixture
def sv_source() -> Callable[..., Any]:
    """`sverify.testing.source`: `sv_source(rows, schema, name="orders")` is
    an in-memory source (`sverify.io.StaticSource`) holding `rows`."""
    from sverify.testing import source

    return source
