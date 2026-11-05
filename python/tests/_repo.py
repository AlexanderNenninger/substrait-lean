"""Whether the tests run inside the repository.

The Wheels workflow runs a copy of `python/tests` against the installed
wheel, without the Lean sources, the characterization facts or the docs.
Tests that read those files carry `needs_repo` and skip there.
"""

from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]

needs_repo = pytest.mark.skipif(
    not (ROOT / "lakefile.lean").is_file(), reason="the repository is not here"
)
