"""What the chaos tests record: how a scenario ended, as one ledger line
(`sverify_dev.chaos`).

A check that fails raises `Violation`, which names the outcome and the
invariant; any other exception after the fault means the job is `stuck`.
`record` turns a failed test's report into the ledger's record.
"""

from __future__ import annotations

import os
import time
import traceback
from collections import Counter
from types import TracebackType
from typing import Any


class Violation(AssertionError):
    """An invariant that does not hold after a fault.

    Attributes:
        outcome: `wrong-result`, `double-applied`, `lost-change`, `stuck` or
            `unclear-error`.
        invariant: What should hold, such as `sink paid = recompute`.
    """

    def __init__(self, outcome: str, invariant: str, detail: str = ""):
        super().__init__(f"{outcome}: {invariant}" + (f"\n{detail}" if detail else ""))
        self.outcome, self.invariant = outcome, invariant


def bag_outcome(got: Counter, want: Counter) -> str:
    """How a table differs from what it should hold: rows twice
    (`double-applied`), rows missing (`lost-change`), or else
    `wrong-result`."""
    extra, missing = got - want, want - got
    if extra and not missing and all(k in want for k in extra):
        return "double-applied"
    if missing and not extra:
        return "lost-change"
    return "wrong-result"


def where(tb: TracebackType | None) -> str | None:
    """The innermost frame of sverify's own code in `tb`, as
    `path:function` relative to the package."""
    found = None
    for frame, _ in traceback.walk_tb(tb):
        path = frame.f_code.co_filename
        if f"{os.sep}sverify{os.sep}" in path and "sverify_dev" not in path:
            rel = path.rsplit(f"{os.sep}sverify{os.sep}", 1)[1]
            found = f"sverify/{rel}:{frame.f_code.co_qualname}"
    return found


def classify(exc: BaseException) -> tuple[str, str, str | None]:
    """The outcome, invariant and where of the exception a test ended with."""
    if isinstance(exc, Violation):
        return exc.outcome, exc.invariant, exc.invariant
    return "stuck", "a refresh after the fault succeeds", where(exc.__traceback__)


def record(item: Any, report: Any, call: Any, scenario: dict[str, Any]) -> dict[str, Any]:
    from sverify_dev import chaos

    out: dict[str, Any] = {
        "run": os.environ.get("SVERIFY_CHAOS_RUN", "?"),
        "commit": os.environ.get("SVERIFY_CHAOS_COMMIT", "?"),
        "time": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "worker": os.environ.get("PYTEST_XDIST_WORKER", "main"),
        "test": item.nodeid,
        "family": item.path.stem.removeprefix("test_chaos_"),
        "duration": round(call.duration, 2),
        "fault": scenario.get("fault"),
        "setup": scenario.get("setup"),
        "invariant": None,
        "where": None,
        "error": None,
    }
    exc = call.excinfo.value if call.excinfo is not None else None
    if exc is None:
        out["outcome"] = "stuck"
    else:
        out["outcome"], out["invariant"], out["where"] = classify(exc)
        text = "".join(traceback.format_exception(exc))
        out["error"] = "\n".join(text.splitlines()[-25:])
    out["known"] = chaos.known_issue(out, chaos.load_known())
    return out
