"""The checker's memory cap (#1074): a request that takes `substrait-check`
past `SVERIFY_CHECKER_MEMORY_MB` fails alone, and the next one gets a new
process."""

import stat
import sys
from pathlib import Path

import pytest

from sverify import _checker
from sverify._checker import PROTOCOL, CheckerMemoryError, _Checker

pytestmark = pytest.mark.skipif(_checker._RSS is None, reason="no memory reading here")

# A `--serve` stand-in: `grow` holds 300 MB until killed; anything else
# answers at once.
FAKE = f"""#!{sys.executable}
import sys, time
if sys.argv[1:] == ["--version"]:
    print("substrait-check protocol {PROTOCOL}")
    sys.exit(0)
held = []
while line := sys.stdin.buffer.readline():
    flag, n = line.split()
    body = sys.stdin.buffer.read(int(n))
    if body == b"grow":
        held.append(b"x" * (300 << 20))
        time.sleep(30)
    sys.stdout.buffer.write(b"0 2 0\\nok")
    sys.stdout.buffer.flush()
"""


def test_a_runaway_request_fails_alone(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    path = tmp_path / "substrait-check"
    path.write_text(FAKE)
    path.chmod(path.stat().st_mode | stat.S_IEXEC)
    monkeypatch.setenv("SVERIFY_CHECKER", str(path))
    monkeypatch.setenv("SVERIFY_CHECKER_MEMORY_MB", "100")
    checker = _Checker()
    try:
        assert checker.ask((), "small") == (0, "ok", "")
        first = checker.proc
        with pytest.raises(CheckerMemoryError, match="over its cap of 100 MB"):
            checker.ask((), "grow")
        assert checker.proc is None
        assert checker.ask((), "small") == (0, "ok", "")
        assert checker.proc is not first
    finally:
        checker.close()


def test_the_memory_reading_sees_a_process() -> None:
    """`/proc/<pid>/statm` on Linux, `proc_pid_rusage` on macOS: this
    process's own reading is between 1 MB and 64 GB."""
    import os

    assert _checker._RSS is not None
    rss = _checker._RSS(os.getpid())
    assert rss is not None and 1 << 20 < rss < 64 << 30
