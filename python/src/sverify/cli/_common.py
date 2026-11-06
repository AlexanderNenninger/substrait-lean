"""What the command's modules share: the exit codes, `UsageError` and how a
target names a node (#730: below `_main` and `_contract`)."""

from __future__ import annotations

from pathlib import Path

#: The exit codes (API review I1).
OK, NOT_PROVED, USAGE, UNSUPPORTED, BUDGET, QUARANTINED, ERROR = 0, 1, 2, 3, 4, 5, 6


class UsageError(Exception):
    """The command line asks for something that is not there."""


def split_target(target: str) -> tuple[Path, str | None]:
    """`file.py:node` as the file and the node; `file.py` as the file and
    None. A Windows drive's colon is part of the path."""
    head, sep, tail = target.rpartition(":")
    if sep and tail and "/" not in tail and "\\" not in tail and head:
        return Path(head), tail
    return Path(target), None
