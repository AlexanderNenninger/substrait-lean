"""`scripts/pin_readme_links.py` pins the PyPI page's links to a release's tag
and unpins them for main."""

import importlib.util
import sys
from pathlib import Path

import pytest

from _repo import needs_repo

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "python" / "scripts" / "pin_readme_links.py"

pytestmark = needs_repo


@pytest.fixture(scope="module")
def script():
    spec = importlib.util.spec_from_file_location("pin_readme_links", SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules["pin_readme_links"] = module
    spec.loader.exec_module(module)
    return module


def test_pin_and_unpin_round_trip(script):
    text = (ROOT / "python" / "README.md").read_text()
    pinned = script.pin(text, "0.9.0")
    assert "blob/main/" not in pinned and "tree/main/" not in pinned
    assert "blob/v0.9.0/docs/" in pinned
    assert script.pin(pinned, "0.9.0", unpin=True) == text


def test_other_links_stay(script):
    repo = script.REPO
    text = f"[a](https://example.org/blob/main/x) [b]({repo}/issues/1) [c]({repo}/blob/main/d.md)"
    assert script.pin(text, "1.0.0") == (
        f"[a](https://example.org/blob/main/x) [b]({repo}/issues/1) [c]({repo}/blob/v1.0.0/d.md)"
    )
