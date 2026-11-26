"""Refusal messages speak of the reference semantics and the engine the user
runs (#410): none of the frontends' or the shared writers' refusals, nor the
Lean parser's, gives DataFusion's behaviour as the reason. DataFusion is no
longer a frontend, and a DuckDB user can't act on it."""

import ast
import re
from pathlib import Path

import pytest

from _repo import needs_repo

ROOT = Path(__file__).resolve().parents[2]
SRC = ROOT / "python" / "src" / "sverify"

# The installed wheel's tests run from a copy of `tests`, without the sources.
pytestmark = needs_repo

#: The frontends and the writers shared by every engine.
PYTHON = [
    *sorted((SRC / "ibis_substrait").glob("*.py")),
    *sorted((SRC / "sql_lift").glob("*.py")),
    *sorted((SRC / "sql" / "core").glob("*.py")),
    ROOT / "engines" / "duckdb" / "src" / "sverify_duckdb" / "dialect.py",
]


def _refusals(path: Path) -> list[tuple[int, str]]:
    """The text of each `raise Unsupported(...)` in `path`."""
    found = []
    for node in ast.walk(ast.parse(path.read_text(encoding="utf-8"))):
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


@pytest.mark.parametrize("path", PYTHON, ids=lambda p: p.relative_to(ROOT).as_posix())
def test_no_python_refusal_cites_datafusion(path):
    bad = [(line, text) for line, text in _refusals(path) if "datafusion" in text.lower()]
    assert not bad, bad


def test_the_scan_finds_refusals():
    assert any(_refusals(p) for p in PYTHON)


def test_no_lean_parser_refusal_cites_datafusion():
    text = (ROOT / "frontend" / "Sverify" / "Frontend" / "Parse.lean").read_text()
    # A `throw` and the string literal after it, which may continue over
    # lines with a trailing backslash.
    throws = re.findall(r'throw s?!?"((?:[^"\\]|\\.)*)"', text, re.S)
    assert throws
    bad = [t for t in throws if "datafusion" in t.lower()]
    assert not bad, bad


#: Words that mark a message as saying what to do instead.
_FIX = re.compile(
    r"\b(use|write|pass|rewrite|cast|instead|take|select|replace|set|add|drop|remove|spell|give"
    r"|change|move|put|try|call|apply|provide|specify|choose|wrap|compute|alias|rename|declare"
    r"|list|filter|unpivot|split|keep|match|read|check|install|build|run|fix)\b"
    r"|see #|\(#\d+|Ibis|engine=",
    re.I,
)

#: The frontends and the SQL writer, whose refusals reach the user.
REFUSERS = [
    *sorted((SRC / "ibis_substrait").glob("*.py")),
    *sorted((SRC / "sql_lift").glob("*.py")),
    *sorted((SRC / "sql" / "core").glob("*.py")),
    # The engines' own refusals. Polars's `Unsupported` ends every message with
    # the exit to DuckDB itself, so its translator is not scanned.
    *sorted((ROOT / "engines" / "spark" / "src" / "sverify_spark").glob("*.py")),
    ROOT / "engines" / "polars" / "src" / "sverify_polars" / "scan.py",
    *sorted((ROOT / "engines" / "duckdb" / "src" / "sverify_duckdb").glob("*.py")),
]


def _without_a_fix(path: Path) -> list[tuple[int, str]]:
    """The plain `raise Unsupported(...)` of `path` whose text names no fix. A
    message that ends in a shared exit (`DUCKDB_ONLY`) has one."""
    bad = []
    for node in ast.walk(ast.parse(path.read_text(encoding="utf-8"))):
        if not (isinstance(node, ast.Raise) and isinstance(node.exc, ast.Call)):
            continue
        call = node.exc
        if getattr(call.func, "id", None) != "Unsupported" or len(call.args) != 1:
            continue
        parts = list(ast.walk(call.args[0]))
        if any(isinstance(n, ast.BinOp) and isinstance(n.right, ast.Name) for n in parts) or any(
            isinstance(n, ast.Name) and n.id == "DUCKDB_ONLY" for n in parts
        ):
            continue
        text = "".join(
            n.value for n in parts if isinstance(n, ast.Constant) and isinstance(n.value, str)
        )
        if text and not _FIX.search(text):
            bad.append((node.lineno, text))
    return bad


@pytest.mark.parametrize("path", REFUSERS, ids=lambda p: p.relative_to(ROOT).as_posix())
def test_a_refusal_says_what_to_do_instead(path):
    """A frontend or the writer raises `ProducerUnsupported`, `SqlUnsupported` or
    `WriterUnsupported`, which end with a fix, or a plain `Unsupported` whose
    own text names one (#176)."""
    bad = _without_a_fix(path)
    assert not bad, bad
