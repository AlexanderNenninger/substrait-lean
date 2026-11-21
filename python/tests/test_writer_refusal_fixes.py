"""A refusal of the SQL writer says what to do instead (#176): it raises
`WriterUnsupported`, which ends with a hint, or a plain `Unsupported` whose
text names one (an engine to run it on, a rewrite, an issue)."""

import ast
import re
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
SRC = ROOT / "python" / "src" / "sverify"

pytestmark = pytest.mark.skipif(not SRC.is_dir(), reason="the repository is not here")

_FIX = re.compile(
    r"\b(use|write|pass|rewrite|cast|instead|take|select|replace|set|add|drop|remove|spell|give"
    r"|change|move|put|try|call|apply|provide|specify|choose|wrap|compute|alias|rename|declare"
    r"|list|filter|unpivot|split|keep|match|read|check|install|build|run|fix)\b|see #|\(#\d+|Ibis"
    r"|engine=",
    re.I,
)

WRITERS = sorted((SRC / "sql" / "core").glob("*.py"))


@pytest.mark.parametrize("path", WRITERS, ids=lambda p: p.name)
def test_a_writer_refusal_says_what_to_do_instead(path):
    bad = []
    for node in ast.walk(ast.parse(path.read_text())):
        if not (isinstance(node, ast.Raise) and isinstance(node.exc, ast.Call)):
            continue
        call = node.exc
        if getattr(call.func, "id", None) != "Unsupported" or len(call.args) != 1:
            continue
        parts = list(ast.walk(call.args[0]))
        if any(isinstance(n, ast.Name) for n in parts):
            continue  # a shared exit such as DUCKDB_ONLY
        text = "".join(
            n.value for n in parts if isinstance(n, ast.Constant) and isinstance(n.value, str)
        )
        if text and not _FIX.search(text):
            bad.append((node.lineno, text))
    assert not bad, bad
