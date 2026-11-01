"""The package ships a copy of the repository's LICENSE (license files must
sit under `python/`); the two stay equal."""

from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]


@pytest.mark.skipif(not (ROOT / "LICENSE").is_file(), reason="not in the repository")
def test_package_license_is_the_repository_license():
    assert (ROOT / "python" / "LICENSE").read_bytes() == (ROOT / "LICENSE").read_bytes()
