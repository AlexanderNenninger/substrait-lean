"""Memory limits (#783, ruling 190): one error, `MemoryLimitError`, for the
checker's cap during a proof and DuckDB's `memory_limit` during a run or a
refresh; the CLI exits 4 with code `memory` for both."""

from __future__ import annotations

import pytest

from sverify import _duckdb
from sverify._checker import CheckerMemoryError
from sverify.cli._common import BUDGET
from sverify.cli._main import _classify
from sverify.errors import MemoryLimitError


def test_the_checkers_cap_is_a_memory_limit_error():
    e = CheckerMemoryError("substrait-check used 5000 MB", 100)
    assert isinstance(e, MemoryLimitError) and isinstance(e, MemoryError)
    assert (e.stage, e.limit, e.setting) == ("proof", "100 MB", "SVERIFY_CHECKER_MEMORY_MB")
    assert e.code == "memory_limit"
    assert _classify(e) == (BUDGET, "memory")


def test_duckdb_out_of_memory_becomes_a_memory_limit_error():
    duckdb = pytest.importorskip("duckdb")
    db = duckdb.connect(config={"memory_limit": "10MB", "temp_directory": ""})
    with pytest.raises(duckdb.Error) as raised:
        db.execute("SELECT list(range) FROM range(20000000)").fetchall()
    e = _duckdb.memory_limit_error(raised.value, "refresh", db)
    assert isinstance(e, MemoryLimitError)
    assert (e.stage, e.setting) == ("refresh", "SVERIFY_MEMORY_LIMIT")
    assert "MiB" in e.limit or "MB" in e.limit
    assert "nothing was committed" in str(e)
    assert _classify(e) == (BUDGET, "memory")
    # Any other error stays as it is.
    assert _duckdb.memory_limit_error(ValueError("x"), "run", db) is None
