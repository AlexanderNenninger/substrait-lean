"""The Lean build budget (`scripts/lean_timings.py`, docs/build-performance.md)."""

import importlib.util
import json

import pytest

from _repo import ROOT, needs_repo

pytestmark = needs_repo


@pytest.fixture(scope="module")
def timings():
    spec = importlib.util.spec_from_file_location(
        "lean_timings", ROOT / "scripts" / "lean_timings.py"
    )
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _record(module, imports=(), cpu=1.0, rss=500, start=0.0):
    return {
        "module": module,
        "imports": list(imports),
        "cpu_s": cpu,
        "wall_s": cpu,
        "rss_mb": rss,
        "start": start,
        "end": start + cpu,
    }


def _write(path, records):
    path.write_text("".join(json.dumps(r) + "\n" for r in records))
    return path


def test_critical_path_is_the_longest_import_chain(timings, tmp_path):
    log = _write(
        tmp_path / "t.jsonl",
        [
            _record("A", cpu=10),
            _record("B", ["A"], cpu=1),
            _record("C", ["A"], cpu=5),
            _record("D", ["B", "C"], cpu=2),
        ],
    )
    length, chain = timings.critical_path(timings.load([log]), "wall_s")
    assert (length, chain) == (17, ["A", "C", "D"])


def test_check_reports_the_module_over_its_ceiling(timings, tmp_path, capsys):
    budget = tmp_path / "b.json"
    budget.write_text(
        json.dumps(
            {
                "default": {"cpu_s": 60, "rss_mb": 3072},
                "modules": {"A": {"cpu_s": 20, "rss_mb": 1536}},
            }
        )
    )
    ok = _write(tmp_path / "ok.jsonl", [_record("A", cpu=19), _record("New", cpu=59)])
    assert timings.check([ok], budget) == []
    slow = _write(tmp_path / "slow.jsonl", [_record("A", cpu=21), _record("New", rss=4000)])
    assert timings.check([slow], budget) == [("A", "cpu_s", 21, 20), ("New", "rss_mb", 4000, 3072)]
    out = capsys.readouterr().out
    assert "A: cpu_s 21 over its ceiling 20" in out
    assert "New: rss_mb 4000 over its ceiling 3072" in out


def test_the_budget_names_existing_modules(timings):
    """A renamed or deleted module leaves no stale ceiling behind."""
    budget = json.loads(timings.BUDGET.read_text())
    for module in budget["modules"]:
        path = module.replace(".", "/") + ".lean"
        engines = ("engines/duckdb", "engines/polars", "engines/spark", "engines/substrait")
        packages = ("core", "analysis", "frontend", "engines", *engines)
        roots = (ROOT, *(ROOT / d for d in packages))
        assert any((root / path).is_file() for root in roots), module
