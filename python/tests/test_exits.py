"""#1205: the `raise` sites of a refusal that name no exit do not grow.

`sverify_dev.exits` finds each refusal in `src/sverify` and says whether its
message names an exit (an issue, a link, what to write or run), only hints at
what is accepted, or names nothing. `exits_baseline.json` holds the count of
the last kind per file; it only goes down. A new refusal with no exit, or an
old one that loses its exit, fails here; one that gains an exit asks for the
baseline to be lowered:

    python -m sverify_dev.exits --write-baseline
"""

import json

import pytest
from _repo import needs_repo

pytestmark = needs_repo

exits = pytest.importorskip("sverify_dev.exits")


def test_no_new_refusal_without_an_exit():
    base = json.loads(exits.BASELINE.read_text())
    now = exits.unnamed_by_file()
    risen = {f: (base.get(f, 0), n) for f, n in now.items() if n > base.get(f, 0)}
    assert not risen, (
        "a refusal that names no exit (and no hint) is new, as (baseline, now) per file: "
        f"{risen}. Say what the user can do (an issue, an argument, a rewrite); "
        "`python -m sverify_dev.exits --sites` lists them."
    )


def test_baseline_is_lowered_with_the_count():
    base = json.loads(exits.BASELINE.read_text())
    now = exits.unnamed_by_file()
    assert now == base, (
        f"refusals without an exit: {sum(now.values())} now, {sum(base.values())} in the "
        "baseline; lower it with `python -m sverify_dev.exits --write-baseline`"
    )
