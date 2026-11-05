"""Time and memory budgets of a CLI call (#744, #783).

The time budget bounds proof, planning and checking only: an alarm raises
`BudgetExceeded` in the main thread, which stops the checker between
requests and is never caught by user code that catches `Exception`. A
watchdog thread ends the process if the main thread does not get back to
Python in time (a long native call). The memory budget is DuckDB's
`memory_limit` with a spill directory (`sverify._duckdb.limits`).
"""

from __future__ import annotations

import os
import re
import signal
import sys
import threading
import time
from collections.abc import Callable, Iterator
from contextlib import contextmanager

#: The default time budget of every command, in seconds (#744).
DEFAULT_TIMEOUT = 30.0
#: How long the main thread may take to stop after the alarm before the
#: watchdog ends the process.
GRACE = 10.0


class BudgetExceeded(BaseException):  # noqa: N818 - a BaseException, like KeyboardInterrupt
    """The call ran out of its time or memory budget. A `BaseException`, so
    that a pipeline's `except Exception` does not swallow it."""

    def __init__(self, what: str, limit: str):
        super().__init__(f"{what} budget exceeded ({limit})")
        self.what, self.limit = what, limit


def timeout_from(arg: float | None) -> float:
    """The time budget: `--timeout`, else `SVERIFY_TIMEOUT`, else 30 s; 0
    (or less) turns it off."""
    if arg is not None:
        return arg
    env = os.environ.get("SVERIFY_TIMEOUT", "").strip()
    if env:
        try:
            return float(env)
        except ValueError as e:
            raise ValueError(f"SVERIFY_TIMEOUT={env!r} is not a number of seconds") from e
    return DEFAULT_TIMEOUT


_SIZE = re.compile(r"\s*\d+(\.\d+)?\s*(B|KB|KIB|MB|MIB|GB|GIB|TB|TIB)?\s*", re.IGNORECASE)


def memory_limit_from(arg: str | None) -> str | None:
    """The memory budget, as DuckDB reads it (`"2GB"`): `--memory-limit`,
    else `SVERIFY_MEMORY_LIMIT`; None if neither is set. It is put in
    `SVERIFY_MEMORY_LIMIT`, which the process's DuckDB database reads when
    it opens."""
    limit = arg if arg is not None else os.environ.get("SVERIFY_MEMORY_LIMIT", "").strip() or None
    if limit is None:
        return None
    if not _SIZE.fullmatch(limit):
        raise ValueError(f"memory limit {limit!r}: give a size such as 512MB or 2GB")
    from sverify._hooks import set_memory_limit

    set_memory_limit(limit)
    return limit


def is_out_of_memory(e: BaseException) -> bool:
    """Whether `e`, or an exception it was raised from, is DuckDB running
    out of its `memory_limit`."""
    seen: set[int] = set()
    cur: BaseException | None = e
    while cur is not None and id(cur) not in seen:
        seen.add(id(cur))
        if type(cur).__name__ == "OutOfMemoryException" or "Out of Memory Error" in str(cur):
            return True
        cur = cur.__cause__ or cur.__context__
    return False


class Budget:
    """A time budget for the stages it is `armed` over."""

    def __init__(self, seconds: float, on_hard_stop: Callable[[], None]):
        self.seconds = seconds
        self.on_hard_stop = on_hard_stop
        self.start = time.monotonic()
        self._deadline: float | None = None
        self._watchdog: threading.Timer | None = None
        self.exceeded = False

    @property
    def elapsed(self) -> float:
        return time.monotonic() - self.start

    @contextmanager
    def armed(self) -> Iterator[None]:
        """Within the block, the budget runs: past it, `BudgetExceeded` is
        raised in the main thread."""
        if self.seconds <= 0 or threading.current_thread() is not threading.main_thread():
            yield
            return
        left = self.seconds - self.elapsed
        if left <= 0:
            self._exceed()
        use_alarm = hasattr(signal, "SIGALRM")
        previous: object = None
        if use_alarm:
            previous = signal.signal(signal.SIGALRM, self._alarm)
            signal.setitimer(signal.ITIMER_REAL, left)
        self._watchdog = threading.Timer(left + (GRACE if use_alarm else 0), self._hard_stop)
        self._watchdog.daemon = True
        self._watchdog.start()
        try:
            yield
        finally:
            self.disarm()
            if use_alarm:
                signal.signal(signal.SIGALRM, previous)  # type: ignore[arg-type]

    def disarm(self) -> None:
        """Stop the budget: what runs after it is not bounded."""
        if hasattr(signal, "SIGALRM"):
            signal.setitimer(signal.ITIMER_REAL, 0)
        if self._watchdog is not None:
            self._watchdog.cancel()
            self._watchdog = None

    def _alarm(self, signum: int, frame: object) -> None:
        self._exceed()

    def _exceed(self) -> None:
        self.exceeded = True
        raise BudgetExceeded("time", f"{self.seconds:g} s")

    def _hard_stop(self) -> None:
        self.exceeded = True
        try:
            self.on_hard_stop()
        finally:
            sys.stdout.flush()
            sys.stderr.flush()
            os._exit(4)  # the budget's exit code (`_main.BUDGET`)
