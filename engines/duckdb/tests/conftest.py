"""DuckDB's tests run in sverify's test session (`python/pyproject.toml`'s
`testpaths`), with its hooks and fixtures (`python/tests/_suite.py`), and
reuse its test modules."""

import sys
from pathlib import Path

#: sverify's tests, beside this package in the repository (and in the copy
#: `python/scripts/wheel_tests.sh` runs).
_SUITE = Path(__file__).resolve().parents[3] / "python" / "tests"
if str(_SUITE) not in sys.path:
    sys.path.insert(0, str(_SUITE))

pytest_plugins = ["_suite"]
