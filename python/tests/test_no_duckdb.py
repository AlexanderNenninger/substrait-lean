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
        print(r.verdict, sql.verdict, "SELECT" in r.to_sql("duckdb").upper(),
              "duckdb" in {m for m, v in sys.modules.items() if v})
        """
    )
    assert out == "proved proved True False"


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


def test_a_polars_connection_needs_no_duckdb() -> None:
    """`connect("polars")` holds Arrow tables: `put`, `table`, `verify` and `run`
    work with no DuckDB, and an Ibis expression on the connection refuses to
    execute, naming the engine to run on (#1764)."""
    import pytest

    pytest.importorskip("polars")
    out = run(
        """
        import pyarrow as pa, sverify as sv
        from ibis import _
        con = sv.connect("polars")
        con.put("t", pa.table({"k": pa.array([1, 2, 3], pa.int64())}))
        t = con.table("t")
        report = sv.verify(t.select(y=t.k + 1), requires={"t": [_.k.between(0, 9)]},
                           ensures=[_.y >= 1], counterexamples=0)
        rows = report.run(con, "polars").to_pylist()
        try:
            t.execute()
        except NotImplementedError as e:
            refused = "polars" in str(e)
        print(report.verdict, rows, refused, "duckdb" in {m for m, v in sys.modules.items() if v})
        """
    )
    assert out == "proved [{'y': 2}, {'y': 3}, {'y': 4}] True False"


def test_a_scan_with_dates_out_of_range_is_refused_on_a_polars_connection() -> None:
    """D32: a date outside 0001-9999 in a file reaches no run. A connection
    without DuckDB has no view to check the rows over, so the files' statistics
    must show the range, and a file whose statistics do not is refused."""
    import pytest

    pytest.importorskip("polars")
    out = run(
        """
        import datetime, tempfile, os
        import pyarrow as pa, pyarrow.parquet as pq, sverify as sv
        from sverify._scan import Scan
        schema = pa.schema([("d", pa.date32())])
        d = tempfile.mkdtemp()
        good, bad = os.path.join(d, "good.parquet"), os.path.join(d, "bad.parquet")
        pq.write_table(pa.table({"d": pa.array([datetime.date(2020, 1, 1)], pa.date32())}), good)
        pq.write_table(pa.table({"d": pa.array([3_000_000], pa.int32()).cast(pa.date32())}), bad)
        con = sv.connect("polars")
        con.put("good", Scan((good,), schema))
        try:
            con.put("bad", Scan((bad,), schema))
        except Exception as e:
            print(type(e).__name__, "0001" in str(e) or "9999" in str(e), con.has("bad"))
        """
    )
    assert out.endswith("True False"), out


def test_a_bound_polars_table_refuses_every_ibis_execution_path() -> None:
    import pytest

    pytest.importorskip("polars")
    out = run(
        """
        import ibis, pyarrow as pa, sverify as sv
        con = sv.connect("polars")
        con.put("t", pa.table({"k": pa.array([1], pa.int64())}))
        t = con.table("t")
        for call in (lambda: ibis.to_sql(t), lambda: t.compile(), lambda: t.to_pyarrow()):
            try:
                call()
            except NotImplementedError as e:
                print("polars" in str(e))
        """
    )
    assert out.split() == ["True"] * 3, out
