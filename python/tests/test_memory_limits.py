"""Memory limits (#783, ruling 190): one error, `MemoryLimitError`, for the
checker's cap during a proof and DuckDB's `memory_limit` during a run or a
refresh; the CLI exits 4 with code `memory` for both."""

from __future__ import annotations

import pytest

from sverify import _duckdb
from sverify._checker import CheckerMemoryError
from sverify.cli import ExitCode
from sverify.cli._main import _classify
from sverify.errors import MemoryLimitError


def test_the_checkers_cap_is_a_memory_limit_error():
    e = CheckerMemoryError("substrait-check used 5000 MB", 100)
    assert isinstance(e, MemoryLimitError) and isinstance(e, MemoryError)
    assert (e.stage, e.limit, e.setting) == ("proof", "100 MB", "SVERIFY_CHECKER_MEMORY_MB")
    assert e.code == "memory_limit"
    assert _classify(e) == (ExitCode.BUDGET, "memory")


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
    assert _classify(e) == (ExitCode.BUDGET, "memory")
    # Any other error stays as it is.
    assert _duckdb.memory_limit_error(ValueError("x"), "run", db) is None


FAKE_CHECKER = """\
import sys, time
if "--version" in sys.argv:
    print("substrait-check protocol PROTOCOL")
    sys.exit(0)
sys.stdin.buffer.readline()
grow = bytearray(400 << 20)
for i in range(0, len(grow), 4096):
    grow[i] = 1
time.sleep(30)
"""

PIPELINE = """\
import pyarrow as pa
import sverify as sv
from sverify.io import StaticSource

@sv.transform()
def ids(orders):
    return orders.select("id")

out = StaticSource(pa.table({"id": [1, 2]}), name="orders").pipe(ids)
"""


def test_the_cli_exits_4_on_the_checkers_memory_cap(tmp_path):
    """In a process of its own, with a checker that grows past its cap: the
    watchdog stops it and `sverify check` exits 4 with code `memory`."""
    import json
    import os
    import subprocess
    import sys

    from sverify import _checker

    if _checker._RSS is None:
        pytest.skip("no way to read a process's memory here")
    fake = tmp_path / "substrait-check"
    script = FAKE_CHECKER.replace("PROTOCOL", str(_checker.PROTOCOL))
    fake.write_text(f"#!{sys.executable}\n{script}")
    fake.chmod(0o755)
    path = tmp_path / "p.py"
    path.write_text(PIPELINE)
    env = {
        **os.environ,
        "SVERIFY_CHECKER": str(fake),
        "SVERIFY_CHECKER_MEMORY_MB": "50",
        "SVERIFY_TIMEOUT": "0",
    }
    argv = [sys.executable, "-m", "sverify.cli", "check", str(path), "--format", "json"]
    done = subprocess.run(argv, capture_output=True, text=True, env=env, timeout=60)
    assert done.returncode == ExitCode.BUDGET, done.stdout + done.stderr
    error = json.loads(done.stdout)["error"]
    assert (error["code"], error["type"]) == ("memory", "CheckerMemoryError")
    assert "SVERIFY_CHECKER_MEMORY_MB" in error["message"]
