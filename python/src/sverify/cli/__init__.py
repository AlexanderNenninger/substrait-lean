"""The `sverify` command: check, fix and run a pipeline's file from a shell,
a CI job or an agent (#744).

    sverify check pipelines/orders.py            # prove every transform and node
    sverify check pipelines/orders.py:paid       # one node (or transform)
    sverify check path/to/dbt_project            # a dbt project, through sverify-dbt
    sverify suggest pipelines/orders.py --apply  # write needed preconditions into requires=
    sverify refresh pipelines/orders.py:paid     # run a node, report what changed
    sverify explain may-be-false                 # what a [code] of check's output means
    sverify explain pipelines/orders.py:paid     # a node's full report

`check` imports the file without running it: every contracted transform it
applies is proved, a node's on its sources' schemas, and a proof that fails
is reported instead of raised. A `refresh()` in the file must sit under
`if __name__ == "__main__":`; while sverify checks, it raises. The output
starts with the contract in plain words: what the output guarantees, what
each refresh checks on the data, and what is not proved, each problem with
a code that `explain` expands.

Every command takes `--json`, which prints one JSON document for tools,
marked `"format": "provisional"` until the versioned report format (#736)
replaces it; `--timeout` (default 30 s, `SVERIFY_TIMEOUT`; 0 turns it off),
which bounds proof, planning and checking, never a refresh moving data; and
`--memory-limit` (`SVERIFY_MEMORY_LIMIT`, such as `2GB`), DuckDB's
`memory_limit`, past which it spills to a temporary directory
(`SVERIFY_SPILL_DIRECTORY`). A breach of either stops the call before any
sink commits.

Exit codes: 0 proved (or every unproved postcondition checked on the data),
1 not proved, 2 refused (`sverify.errors.Unsupported`), 3 budget exceeded
(time or memory), 4 error. A `refresh` that completed exits 5 when rows of
a node's sources are set aside (`on_violation="quarantine"`), and 6 when a
node held its batch (`on_violation="hold"`), with `Refresh.alert()`'s
text after the summary and `"outcome"` and `"alert"` in the JSON (#184).

* `main` runs the command with given arguments and returns its exit code.
* `discover` imports a file the way `check` does and returns a `Discovery`:
  each application of a contracted transform as a `Checked`, with its
  `sverify.Report`.
* `summary` is the plain-language contract of a report, as `check` prints it.
"""

from __future__ import annotations

from pathlib import Path

from sverify.cli._discover import Checked, Discovery, load
from sverify.cli._main import main
from sverify.cli._text import summary


def discover(path: str | Path) -> Discovery:
    """Import the Python file at `path` without running its pipelines, and
    prove every contracted transform it applies, as `sverify check` does.

    A transform applied to sources or nodes is proved on their schemas; one
    that is not proved, or whose precondition does not follow from the
    transform feeding it, is recorded instead of raising. A `refresh()`
    that runs at import raises (put it under `if __name__ == "__main__":`).

    Args:
        path: The file.

    Returns:
        A `Discovery`: the applications (`checked`), with their reports and
        the file's variables that hold their nodes; the transforms it
        never applies (`unchecked`); and what stopped the import, if
        anything (`error`).

    Raises:
        FileNotFoundError: There is no file at `path`.
    """
    return load(path)


__all__ = ["Checked", "Discovery", "discover", "main", "summary"]
