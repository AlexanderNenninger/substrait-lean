"""`scripts/docs_version_label.py` names the release on a tag's site and the
development version on main's."""

import importlib.util
import sys
from pathlib import Path

import pytest

from _repo import ROOT, needs_repo

SCRIPT = ROOT / "python" / "scripts" / "docs_version_label.py"

pytestmark = needs_repo


@pytest.fixture(scope="module")
def script():
    spec = importlib.util.spec_from_file_location("docs_version_label", SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules["docs_version_label"] = module
    spec.loader.exec_module(module)
    return module


PAGE = (
    '<span class="navbar-title">sverify '
    '<span class="version-badge" title="x">vnightly</span></span>'
)


def test_a_release_shows_its_version(script, tmp_path: Path):
    (tmp_path / "index.html").write_text(PAGE)
    assert script.relabel(tmp_path, "0.9.0", release=True) == 1
    text = (tmp_path / "index.html").read_text()
    assert ">v0.9.0</span>" in text and "nightly" not in text


def test_main_says_it_is_the_development_version(script, tmp_path: Path):
    (tmp_path / "a").mkdir()
    (tmp_path / "a" / "x.html").write_text(PAGE)
    assert script.relabel(tmp_path, "0.9.0.dev0", release=False) == 1
    text = (tmp_path / "a" / "x.html").read_text()
    assert "0.9.0.dev0 (development)" in text and "built from main" in text


def test_the_version_is_pyprojects(script):
    assert script.version() in (ROOT / "python" / "pyproject.toml").read_text()


def test_the_logo_tooltip_is_relabelled(script, tmp_path: Path):
    (tmp_path / "index.html").write_text(
        '<a data-tippy-content="<code>vnightly</code><br>Released 2026-11-03">'
    )
    assert script.relabel(tmp_path, "0.9.0.dev0", release=False) == 1
    text = (tmp_path / "index.html").read_text()
    assert "<code>0.9.0.dev0 (development)</code><br>Development version" in text
    assert "Released" not in text
