"""The manual scripts in `python/scripts` that no test or workflow runs still
import: a rename in `sverify` or `sverify_dev` would otherwise break them
unnoticed. Importing runs no `main()`."""

import importlib.util
import queue
import sys
from pathlib import Path

import pytest

SCRIPTS = Path(__file__).resolve().parents[1] / "scripts"
MANUAL = ["bench_optimizations"]

#: The Wheels workflow runs these tests with only `python/tests` copied out.
pytestmark = pytest.mark.skipif(not SCRIPTS.is_dir(), reason="the repository is not here")


@pytest.mark.parametrize("name", MANUAL)
def test_script_imports(name, monkeypatch):
    spec = importlib.util.spec_from_file_location(name, SCRIPTS / f"{name}.py")
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    monkeypatch.setitem(sys.modules, name, module)
    spec.loader.exec_module(module)


def load(name, monkeypatch):
    spec = importlib.util.spec_from_file_location(name, SCRIPTS / f"{name}.py")
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    monkeypatch.setitem(sys.modules, name, module)
    spec.loader.exec_module(module)
    return module


@pytest.mark.parametrize("fmt", ["delta", "iceberg"])
def test_bench_io_runs(fmt, tmp_path, monkeypatch):
    """`bench_io.py` drives pipeline internals (`Sink._attach`, `_commit`):
    run its phases on a small table."""
    pytest.importorskip("deltalake")
    pytest.importorskip("pyiceberg")
    bench = load("bench_io", monkeypatch)
    for view in bench.VIEWS:
        root = tmp_path / view
        root.mkdir()
        bench.setup(fmt, root, 1000)
        out = queue.Queue()
        bench.measure(fmt, view, root, 1000, out)
        phases = [name for name, _, _ in out.get()]
        assert phases == ["start", "read", "full", "sink", "incremental", "merge"]
