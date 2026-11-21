"""sverify-dbt reaches into sverify through its public API only (#891 1.9)."""

from __future__ import annotations

import ast
import importlib
from pathlib import Path

SRC = Path(__file__).parent.parent / "src" / "sverify_dbt"
PUBLIC = (
    "sverify",
    "sverify.io",
    "sverify.engines",
    "sverify.types",
    "sverify.testing",
    "sverify.errors",
    "sverify.cli",
    "sverify.odcs",
    "sverify.openlineage",
)
#: What it still takes from outside the public API, each recorded in
#: API-NOTES.md ("sverify-dbt reads sverify's finding codes and budgets from
#: `sverify.cli`") until sverify exports it. The list only shrinks.
PRIVATE = {
    ("sverify._duckdb", "memory_limit_error"),
    ("sverify.cli", "_limits"),
    ("sverify.cli", "_explain"),
    ("ibis.backends.sql.datatypes", "DuckDBType"),
}


def _used() -> set[tuple[str, str]]:
    """The (module, name) pairs sverify-dbt takes from `sverify` and `ibis`:
    `from m import n`, and `sv.n` for `import sverify as sv`."""
    out: set[tuple[str, str]] = set()
    for path in SRC.glob("*.py"):
        for node in ast.walk(ast.parse(path.read_text())):
            if isinstance(node, ast.ImportFrom) and node.module:
                if node.module.split(".")[0] in ("sverify", "ibis"):
                    out |= {(node.module, a.name) for a in node.names}
            elif (
                isinstance(node, ast.Attribute)
                and isinstance(node.value, ast.Name)
                and node.value.id == "sv"
            ):
                out.add(("sverify", node.attr))
    return out


def test_imports_are_public_or_recorded() -> None:
    private = {
        (m, n) for m, n in _used() if m not in PUBLIC or n not in importlib.import_module(m).__all__
    }
    assert private <= PRIVATE, f"sverify-dbt takes non-public names: {sorted(private - PRIVATE)}"


def test_recorded_names_are_still_used() -> None:
    assert _used() >= PRIVATE, f"drop from PRIVATE: {sorted(PRIVATE - _used())}"


def test_sverify_names_exist() -> None:
    for m, n in _used():
        if m in PUBLIC:
            assert hasattr(importlib.import_module(m), n), (m, n)
