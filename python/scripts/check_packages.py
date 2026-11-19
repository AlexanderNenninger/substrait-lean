"""Check that sverify's distributions work together, as published (#1189).

The Wheels workflow installs each combination users install, from the run's
own wheels and with no source tree, one environment each, and runs this in
it:

    python scripts/check_packages.py base         # sverify alone: no DuckDB, no engine
    python scripts/check_packages.py duckdb       # sverify[duckdb]
    python scripts/check_packages.py polars       # sverify[polars]: Polars, no DuckDB
    python scripts/check_packages.py spark        # sverify[spark] (brings DuckDB)
    python scripts/check_packages.py spark-light  # sverify[duckdb] and sverify-spark, no PySpark
    python scripts/check_packages.py dbt          # sverify and sverify-dbt

Each checks the engines sverify finds (`sverify.profiles`), that every
installed sverify distribution is at sverify's version, a `verify` of a small
plan, and a run of it on each installed engine against DuckDB's rows. The
base install verifies and writes SQL with no DuckDB, and a run names the
extra; the light Spark install writes Spark SQL and refuses a run, naming
the extra.
"""

from __future__ import annotations

import argparse
import importlib.util
from importlib.metadata import PackageNotFoundError, version

#: The distributions released at sverify's version.
DISTRIBUTIONS = ("sverify-duckdb", "sverify-polars", "sverify-spark", "sverify-dbt")


def pinned() -> list[str]:
    """The installed sverify distributions, each at sverify's version."""
    ours = version("sverify")
    found = []
    for d in DISTRIBUTIONS:
        try:
            v = version(d)
        except PackageNotFoundError:
            continue
        assert v == ours, f"{d} is at {v}, sverify at {ours}"
        found.append(d)
    return found


def report_and_tables():
    """A small proved plan, and a connection holding its table."""
    import ibis
    import pyarrow as pa

    import sverify as sv

    con = sv.connect()
    con.put("t", pa.table({"a": [1, 5, 7]}))
    t = ibis.table({"a": "int64"}, name="t")
    report = sv.verify(
        t.filter(t.a > 2),
        tables={"t": t},
        requires={"t": [sv.unique("a")]},
        ensures=[sv.unique("a")],
    )
    assert report.verdict == "proved", report
    return report, con


def rows(table) -> list[int]:
    return sorted(r["a"] for r in table.to_pylist())


def check(engines: set[str], absent: tuple[str, ...] = ()) -> None:
    """The engines sverify finds include `engines`; none of `absent` is
    installed; a run on each of `engines` gives DuckDB's rows."""
    from sverify import profiles

    found = set(profiles.plugins())
    assert engines <= found, f"engines found: {sorted(found)}, expected {sorted(engines)}"
    missing = [m for m in absent if importlib.util.find_spec(m) is not None]
    assert not missing, f"installed, though this install should not have them: {missing}"
    report, con = report_and_tables()
    expected = rows(report.run(con, engine="duckdb"))
    assert expected == [5, 7], expected
    for e in sorted(engines - {"duckdb"}):
        got = rows(report.run(con, engine=e))
        assert got == expected, f"{e} gives {got}, DuckDB {expected}"
    print(f"engines {sorted(found)}; ran on {sorted(engines)}; pinned {pinned()}")


def base() -> None:
    """sverify alone: no engine runs plans and DuckDB is not installed, a
    plan verifies and is written as SQL, and a run names the extra."""
    from sverify import profiles

    assert importlib.util.find_spec("duckdb") is None, "duckdb is installed in the base"
    import ibis

    import sverify as sv

    t = ibis.table({"a": "int64"}, name="t")
    report = sv.verify(
        t.filter(t.a > 2), requires={"t": [sv.unique("a")]}, ensures=[sv.unique("a")]
    )
    assert report.verdict == "proved", report
    assert "SELECT" in report.to_sql("duckdb").upper()
    assert not [e for e, p in profiles.plugins().items() if p.local]
    try:
        sv.connect()
    except ValueError as e:
        assert "sverify[duckdb]" in str(e), e
    else:
        raise AssertionError("a connection without an engine did not refuse")
    print(f"engines {sorted(profiles.plugins())}; verified and wrote SQL; pinned {pinned()}")


def polars_only() -> None:
    """sverify[polars]: no DuckDB; a connection on Polars holds a table, a
    plan verifies, runs on Polars and refuses a batch that breaks a
    precondition."""
    import ibis
    import pyarrow as pa

    import sverify as sv
    from sverify import profiles

    assert importlib.util.find_spec("duckdb") is None, "duckdb is installed with sverify[polars]"
    assert importlib.util.find_spec("pyspark") is None
    found = {e for e, p in profiles.plugins().items() if p.local}
    assert found == {"polars"}, found
    con = sv.connect()
    assert con.engine == "polars"
    con.put("t", pa.table({"a": [1, 5, 7]}))
    t = ibis.table({"a": "int64"}, name="t")
    report = sv.verify(
        t.filter(t.a > 2), requires={"t": [sv.unique("a")]}, ensures=[sv.unique("a")]
    )
    assert report.verdict == "proved", report
    assert rows(report.run(con)) == [5, 7]
    con.put("t", pa.table({"a": [5, 5]}))
    try:
        report.run(con)
    except sv.errors.PreconditionError:
        pass
    else:
        raise AssertionError("a batch with a duplicate key was not refused")
    print(f"engines {sorted(profiles.plugins())}; ran on Polars; pinned {pinned()}")


def spark_light() -> None:
    """sverify-spark without PySpark: it writes Spark SQL, and a run on Spark
    names the extra that brings PySpark."""
    check({"duckdb"}, absent=("pyspark",))
    from sverify import profiles

    assert "spark" in profiles.plugins()
    report, con = report_and_tables()
    sql = report.to_sql("spark")
    assert "SELECT" in sql.upper(), sql
    try:
        report.run(con, engine="spark")
    except ImportError as e:
        assert "sverify[spark]" in str(e), e
    else:
        raise AssertionError("a run on Spark without PySpark did not refuse")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "combination", choices=["base", "duckdb", "polars", "spark", "spark-light", "dbt"]
    )
    which = parser.parse_args().combination
    if which == "base":
        base()
    elif which == "duckdb":
        check({"duckdb"}, absent=("polars", "pyspark", "sverify_polars", "sverify_spark"))
    elif which == "polars":
        polars_only()
    elif which == "spark":
        check({"duckdb", "spark"}, absent=("polars",))
    elif which == "spark-light":
        spark_light()
    else:
        check({"duckdb"}, absent=("polars", "pyspark"))
        assert "sverify-dbt" in pinned()


if __name__ == "__main__":
    main()
