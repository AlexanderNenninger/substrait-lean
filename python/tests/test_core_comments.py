"""The core holds no engine's workaround, and its comments say so (#1445).

A comment in `core/` says what its definition computes. DataFusion and
Snowflake are named nowhere there, and no comment gives a path into
`engines/` or `characterization/`: a fact is named by its id.
"""

import re

import pytest

from _repo import ROOT, needs_repo

pytestmark = needs_repo

FILES = sorted((ROOT / "core").rglob("*.lean"))
BANNED = re.compile(r"datafusion|snowflake|engines/|characterization/", re.IGNORECASE)


def test_core_sources_are_found():
    assert len(FILES) > 20


@pytest.mark.parametrize("path", FILES, ids=lambda p: p.name)
def test_core_names_no_removed_engine_and_no_engine_path(path):
    hits = [
        f"{path.name}:{n}: {line.strip()}"
        for n, line in enumerate(path.read_text().splitlines(), 1)
        if BANNED.search(line)
    ]
    assert not hits, "\n".join(hits)
