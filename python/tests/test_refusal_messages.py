"""Refusal messages speak of the reference semantics and the engine the user
runs (#410): none of the frontends' or the shared writers' refusals, nor the
Lean parser's, gives DataFusion's behaviour as the reason. DataFusion is no
longer a frontend, and a DuckDB user can't act on it."""

import ast
import re
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
SRC = ROOT / "python" / "src" / "sverify"

# The installed wheel's tests run from a copy of `tests`, without the sources.
pytestmark = pytest.mark.skipif(not SRC.is_dir(), reason="the repository is not here")

#: The frontends and the writers shared by every engine.
PYTHON = [
    *sorted((SRC / "ibis_substrait").glob("*.py")),
    *sorted((SRC / "sql_lift").glob("*.py")),
    *sorted((SRC / "sql" / "core").glob("*.py")),
    SRC / "sql" / "duckdb.py",
]


def _refusals(path: Path) -> list[tuple[int, str]]:
    """The text of each `raise Unsupported(...)` in `path`."""
    found = []
    for node in ast.walk(ast.parse(path.read_text())):
        if not (isinstance(node, ast.Raise) and isinstance(node.exc, ast.Call)):
            continue
        func = node.exc.func
        if getattr(func, "id", getattr(func, "attr", None)) != "Unsupported":
            continue
        text = "".join(
            n.value
            for arg in node.exc.args
            for n in ast.walk(arg)
            if isinstance(n, ast.Constant) and isinstance(n.value, str)
        )
        found.append((node.lineno, text))
    return found


@pytest.mark.parametrize("path", PYTHON, ids=lambda p: str(p.relative_to(SRC)))
def test_no_python_refusal_cites_datafusion(path):
    bad = [(line, text) for line, text in _refusals(path) if "datafusion" in text.lower()]
    assert not bad, bad


def test_the_scan_finds_refusals():
    assert any(_refusals(p) for p in PYTHON)


def test_no_lean_parser_refusal_cites_datafusion():
    text = (ROOT / "SubstraitLean" / "Parse.lean").read_text()
    # A `throw` and the string literal after it, which may continue over
    # lines with a trailing backslash.
    throws = re.findall(r'throw s?!?"((?:[^"\\]|\\.)*)"', text)
    assert throws
    bad = [t for t in throws if "datafusion" in t.lower()]
    assert not bad, bad
