"""Without DuckDB (#1288, #1485 item 16): every module imports, `verify`
proves a plan, and what runs on DuckDB names the extra to install."""

from __future__ import annotations

import subprocess
import sys
import textwrap


def run(code: str) -> str:
    """`code` in a Python where `import duckdb` fails."""
    prelude = (
        "import sys, warnings; warnings.simplefilter('ignore'); sys.modules['duckdb'] = None\n"
    )
    done = subprocess.run(
        [sys.executable, "-c", prelude + textwrap.dedent(code)],
        capture_output=True,
        text=True,
    )
    assert done.returncode == 0, done.stdout + done.stderr
    return done.stdout.strip()


def test_every_module_imports_without_duckdb() -> None:
    out = run(
        """
        import importlib, pkgutil, sverify, sverify_duckdb
        bad = []
        for pkg in (sverify, sverify_duckdb):
            for m in pkgutil.walk_packages(pkg.__path__, pkg.__name__ + "."):
                if m.name.startswith(("sverify.skills", "sverify.ibis_substrait")):
                    continue
                if "__main__" in m.name:
                    continue
                try:
                    importlib.import_module(m.name)
                except ImportError as e:
                    # An optional package of another extra is not this test's concern.
                    if "duckdb" in str(e):
                        bad.append(f"{m.name}: {e}")
        print(bad)
        """
    )
    assert out == "[]"


def test_verify_proves_a_plan_without_duckdb() -> None:
    out = run(
        """
        import ibis, sverify as sv
        from ibis import _
        t = ibis.table({"k": "int64"}, name="t")
        r = sv.verify(t.select(y=t.k + 1), requires={"t": [_.k.between(0, 9)]},
                      ensures=[_.y >= 1], counterexamples=0)
        sql = sv.verify("SELECT k + 1 AS y FROM t", tables={"t": {"k": "int64"}},
                        requires={"t": [_.k.between(0, 9)]}, ensures=["y >= 1"],
                        counterexamples=0)
        print(r.verdict, sql.verdict, "duckdb" in {m for m, v in sys.modules.items() if v})
        """
    )
    assert out == "proved proved False"


def test_running_on_duckdb_names_the_extra() -> None:
    out = run(
        """
        import sverify as sv
        try:
            sv.connect("duckdb")
        except ImportError as e:
            print(e)
        """
    )
    assert "sverify[duckdb]" in out


def test_an_engine_that_is_installed_is_not_told_to_install_it() -> None:
    """`connect("spark")` with PySpark present is not the DuckDB message: the
    hint names an extra only where a module of the engine is missing."""
    import pytest

    pytest.importorskip("pyspark")
    out = run(
        """
        import sverify as sv
        try:
            sv.connect("spark")
        except Exception as e:
            print(type(e).__name__, e)
        """
    )
    assert "sverify[spark]" not in out
