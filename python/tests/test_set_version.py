"""`scripts/set_version.py` and the places that carry sverify's version (#1606)."""

from __future__ import annotations

import importlib.util
import re
import shutil
from pathlib import Path

import pytest

from _repo import needs_repo

REPO = Path(__file__).resolve().parents[2]
SCRIPT = REPO / "python" / "scripts" / "set_version.py"


def _script():
    spec = importlib.util.spec_from_file_location("set_version", SCRIPT)
    assert spec is not None and spec.loader is not None
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def _versions(root: Path) -> set[str]:
    """Every version string and `sverify…==` pin of the packages' pyprojects."""
    found = set()
    for name in _script().PINS:
        text = (root / name).read_text()
        own = re.search(r'(?m)^version = "([^"]*)"', text)
        assert own is not None
        found.add(own[1])
        found |= set(re.findall(r'"sverify(?:-\w+)?(?:\[\w+\])?==([^"]*)"', text))
    return found


@needs_repo
def test_the_packages_carry_one_version():
    assert len(_versions(REPO)) == 1


@needs_repo
@pytest.mark.parametrize("version", ["0.9.0", "0.10.0.dev0", "1.0.0rc1"])
def test_set_version_moves_every_place_at_once(tmp_path, version):
    mod = _script()
    for name in mod.PINS:
        (tmp_path / name).parent.mkdir(parents=True, exist_ok=True)
        shutil.copy(REPO / name, tmp_path / name)
    mod.set_version(version, tmp_path)
    assert _versions(tmp_path) == {version}


@needs_repo
def test_set_version_refuses_what_is_no_version(tmp_path):
    with pytest.raises(SystemExit):
        _script().set_version("main", tmp_path)


@needs_repo
def test_a_missing_version_line_raises_even_under_python_O():
    with pytest.raises(ValueError, match="no version line"):
        _script().rewrite("name = 'x'\n", "1.0.0", [])
