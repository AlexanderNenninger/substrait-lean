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


def _budget(path, modules, default=None):
    path.write_text(
        json.dumps({"default": default or {"cpu_cal": 6.0, "rss_mb": 3072}, "modules": modules})
    )
    return path


def test_check_reports_the_module_over_its_ceiling(timings, tmp_path, capsys):
    budget = _budget(tmp_path / "b.json", {"A": {"cpu_cal": 2.0, "rss_mb": 1536}})
    cal = {"calibration": 10.0}
    ok = _write(tmp_path / "ok.jsonl", [cal, _record("A", cpu=19), _record("New", cpu=59)])
    assert timings.check([ok], budget) == []
    slow = _write(tmp_path / "slow.jsonl", [cal, _record("A", cpu=21), _record("New", rss=4000)])
    assert timings.check([slow], budget) == [
        ("A", "cpu_cal", 2.1, 2.0),
        ("New", "rss_mb", 4000, 3072),
    ]
    out = capsys.readouterr().out
    assert "A: cpu_cal 2.1 over its ceiling 2.0" in out
    assert "New: rss_mb 4000 over its ceiling 3072" in out


def test_a_slower_runner_moves_the_calibration_with_the_modules(timings, tmp_path):
    """The same build on a runner half as fast: the same ratios, no warning;
    one module 30 % slower on it still warns (#1865)."""
    fast = _write(tmp_path / "fast.jsonl", [{"calibration": 8.0}, _record("Gen", cpu=240)])
    timings.write_budget([fast], budget := tmp_path / "b.json")
    assert json.loads(budget.read_text())["modules"]["Gen"]["cpu_cal"] == 45.0
    slow = _write(tmp_path / "slow.jsonl", [{"calibration": 16.0}, _record("Gen", cpu=480)])
    assert timings.check([slow], budget) == []
    slower = _write(
        tmp_path / "slower.jsonl", [{"calibration": 16.0}, _record("Gen", cpu=480 * 1.3)]
    )
    assert timings.check([slower], budget) == []  # within the 1.5x margin ...
    worse = _write(tmp_path / "worse.jsonl", [{"calibration": 16.0}, _record("Gen", cpu=480 * 1.6)])
    assert [o[:2] for o in timings.check([worse], budget)] == [("Gen", "cpu_cal")]


def test_the_ceiling_covers_the_runner_where_a_module_is_relatively_slowest(timings, tmp_path):
    a = _write(tmp_path / "a.jsonl", [{"calibration": 10.0}, _record("Gen", cpu=300, rss=900)])
    b = _write(tmp_path / "b.jsonl", [{"calibration": 20.0}, _record("Gen", cpu=800, rss=1200)])
    assert timings.peaks([a, b]) == {"Gen": {"cpu_cal": 40.0, "rss_mb": 1200}}


def test_without_a_calibration_only_memory_is_checked(timings, tmp_path, capsys):
    budget = _budget(tmp_path / "b.json", {"A": {"cpu_cal": 2.0, "rss_mb": 1536}})
    log = _write(tmp_path / "t.jsonl", [_record("A", cpu=500, rss=2000)])
    assert timings.check([log], budget) == [("A", "rss_mb", 2000, 1536)]
    assert "no calibration" in capsys.readouterr().out
    with pytest.raises(SystemExit, match="no calibration"):
        timings.write_budget([log], tmp_path / "w.json")


def test_the_budget_names_existing_modules(timings):
    """A renamed or deleted module leaves no stale ceiling behind."""
    budget = json.loads(timings.BUDGET.read_text())
    for module in budget["modules"]:
        path = module.replace(".", "/") + ".lean"
        engines = ("engines/duckdb", "engines/polars", "engines/spark", "engines/substrait")
        packages = ("core", "analysis", "frontend", "engines", *engines)
        roots = (ROOT, *(ROOT / d for d in packages))
        assert any((root / path).is_file() for root in roots), module
