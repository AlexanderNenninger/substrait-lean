"""What the command's modules share: the exit codes, `UsageError` and how a
target names a node (#730: below `_main` and `_contract`)."""

from __future__ import annotations

from enum import IntEnum
from pathlib import Path


class ExitCode(IntEnum):
    """The exit code of `sverify check`, `refresh` and `explain`, and the
    `exit` of their JSON, from the best to the worst: the worst of several
    runs is their `max` (#2458).

    Attributes:
        PROVED: 0, every node proved; a refresh committed every row.
        NOT_PROVED: 1, a node is not proved.
        USAGE: 2, a flag, a missing file or a node the file lacks.
        UNSUPPORTED: 3, a construct outside sverify's model.
        REFUSED: 4, no route takes the proved node to the engine.
        BUDGET: 5, the time or memory budget was exceeded.
        QUARANTINED: 6, a refresh committed with rows quarantined.
        HELD: 7, a refresh held a node.
        ERROR: 8, the file raised outside a run-time check, I/O or a crash.
    """

    PROVED = 0
    NOT_PROVED = 1
    USAGE = 2
    UNSUPPORTED = 3
    REFUSED = 4
    BUDGET = 5
    QUARANTINED = 6
    HELD = 7
    ERROR = 8

    @property
    def status(self) -> str:
        """The code in words, the JSON's `status`, such as `"not_proved"`."""
        return _STATUS[self]

    @property
    def meaning(self) -> str:
        """The code's line in `sverify --help`."""
        return _MEANING[self]


_STATUS = {
    ExitCode.PROVED: "proved",
    ExitCode.NOT_PROVED: "not_proved",
    ExitCode.USAGE: "usage",
    ExitCode.UNSUPPORTED: "unsupported",
    ExitCode.REFUSED: "refused",
    ExitCode.BUDGET: "budget_exceeded",
    ExitCode.QUARANTINED: "quarantined",
    ExitCode.HELD: "held",
    ExitCode.ERROR: "error",
}
_MEANING = {
    ExitCode.PROVED: "proved; a refresh committed every row",
    ExitCode.NOT_PROVED: "not proved",
    ExitCode.USAGE: "usage error: a flag, a missing file, a node the file lacks",
    ExitCode.UNSUPPORTED: "unsupported: a construct outside sverify's model",
    ExitCode.REFUSED: "refused: no route takes the proved node to the engine",
    ExitCode.BUDGET: "time or memory budget exceeded",
    ExitCode.QUARANTINED: "a refresh committed with rows quarantined",
    ExitCode.HELD: "a refresh held a node: a condition failed, or a run-time check fired",
    ExitCode.ERROR: "error: the file raised outside a run-time check, I/O, a crash",
}


class UsageError(Exception):
    """The command line asks for something that is not there."""


def split_target(target: str) -> tuple[Path, str | None]:
    """`file.py:node` as the file and the node; `file.py` as the file and
    None. A Windows drive's colon is part of the path."""
    head, sep, tail = target.rpartition(":")
    if sep and tail and "/" not in tail and "\\" not in tail and head:
        return Path(head), tail
    return Path(target), None
