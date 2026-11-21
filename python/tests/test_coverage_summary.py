"""`scripts/coverage_summary.py`, the report of CI's coverage job (#750)."""

import importlib.util
import json
from pathlib import Path

import pytest

from _repo import needs_repo

pytestmark = needs_repo


@pytest.fixture(scope="module")
def mod():
    path = Path(__file__).parent.parent / "scripts" / "coverage_summary.py"
    spec = importlib.util.spec_from_file_location("coverage_summary", path)
    assert spec is not None and spec.loader is not None
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def _file(stmts, missing, branches=0, missed_branches=0):
    return {
        "summary": {
            "num_statements": stmts,
            "missing_lines": missing,
            "num_branches": branches,
            "missing_branches": missed_branches,
        }
    }


DATA = {
    "files": {
        "src/sverify/a.py": _file(100, 10, 20, 10),
        "src/sverify/b.py": _file(100, 30),
        "src/sverify_dev/tool.py": _file(1000, 900),  # not counted
    }
}


def test_numbers_and_ranking(mod):
    text, ok = mod.summarise(DATA, target=90, top=1)
    assert "lines: 80.0 % (160 of 200 statements)" in text
    # (160 + 10) / (200 + 20)
    assert "lines and branches: 77.3 %" in text
    assert "`src/sverify/b.py` | 30 |" in text
    assert "a.py" not in text and "tool.py" not in text
    assert not ok


def test_meets_target(mod):
    _, ok = mod.summarise(DATA, target=75, top=2)
    assert ok


def test_main_warns_and_exits_zero(mod, tmp_path, capsys):
    f = tmp_path / "c.json"
    f.write_text(json.dumps(DATA))
    assert mod.main([str(f), "--target", "90"]) == 0
    captured = capsys.readouterr()
    assert "::warning::" in captured.err
    assert "Coverage of `sverify`" in captured.out


def test_a_named_package_is_reported_alone(mod):
    data = {"files": {**DATA["files"], "src/sverify_dbt/c.py": _file(50, 5)}}
    text, ok = mod.summarise(data, target=90, top=3, package="sverify_dbt")
    assert "Coverage of `sverify_dbt`" in text and "90.0 % (45 of 50 statements)" in text
    assert ok
    assert "sverify/a.py" not in text
