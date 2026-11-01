"""The manual scripts in `python/scripts` that no test or workflow runs still
import: a rename in `sverify` or `sverify_dev` would otherwise break them
unnoticed. Importing runs no `main()`."""

import importlib.util
import sys
from pathlib import Path

import pytest

SCRIPTS = Path(__file__).resolve().parents[1] / "scripts"
MANUAL = ["bench_optimizations", "capture_fixtures", "isthmus_catalogue"]

#: The Wheels workflow runs these tests with only `python/tests` copied out.
pytestmark = pytest.mark.skipif(not SCRIPTS.is_dir(), reason="the repository is not here")


@pytest.mark.parametrize("name", MANUAL)
def test_script_imports(name, monkeypatch):
    spec = importlib.util.spec_from_file_location(name, SCRIPTS / f"{name}.py")
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    monkeypatch.setitem(sys.modules, name, module)
    spec.loader.exec_module(module)
