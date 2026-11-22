"""Check that sverify's distributions work together, as published (#1189).

The Wheels workflow installs each combination users install, from the run's
own wheels and with no source tree, one environment each, and runs this in
it:

    python scripts/check_packages.py base         # sverify alone: no DuckDB, no engine
    python scripts/check_packages.py duckdb       # sverify[duckdb]
    python scripts/check_packages.py polars       # sverify[polars] (brings DuckDB)
    python scripts/check_packages.py spark        # sverify[spark] (brings DuckDB)
    python scripts/check_packages.py spark-light  # sverify[duckdb] and sverify-spark, no PySpark
    python scripts/check_packages.py dbt          # sverify and sverify-dbt
    python scripts/check_packages.py delta        # sverify[delta], and each other
                                                  # extra in EXTRAS alone (#183)

Each checks the engines sverify finds (`sverify.profiles`), that every
installed sverify distribution is at sverify's version, a `verify` of a small
plan, and a run of it on each installed engine against DuckDB's rows. The
base install verifies and writes SQL with no DuckDB, and a run names the
extra; the light Spark install writes Spark SQL and refuses a run, naming
the extra.
"""

from __future__ import annotations

import argparse
import importlib
import importlib.util
import sys
from collections.abc import Callable
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


def report_and_tables(engine: str | None = None):
    """A small proved plan, and a connection (on `engine`) holding its table."""
    import ibis
    import pyarrow as pa

    import sverify as sv

    con = sv.connect(engine)
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


def check(engines: set[str], absent: tuple[str, ...] = (), local: str = "duckdb") -> None:
    """The engines sverify finds include `engines`; none of `absent` is
    installed; a run on each of `engines` gives the rows of `local`, the
    engine of the connection."""
    from sverify import profiles

    found = set(profiles.plugins())
    assert engines <= found, f"engines found: {sorted(found)}, expected {sorted(engines)}"
    missing = [m for m in absent if importlib.util.find_spec(m) is not None]
    assert not missing, f"installed, though this install should not have them: {missing}"
    report, con = report_and_tables(local)
    expected = rows(report.run(con, engine=local))
    assert expected == [5, 7], expected
    for e in sorted(engines - {local}):
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


def _delta(tmp: str) -> None:
    import pyarrow as pa
    from deltalake import write_deltalake

    from sverify.io import DeltaSource

    write_deltalake(f"{tmp}/t", pa.table({"a": [1, 2]}))
    assert DeltaSource(f"{tmp}/t").schema().names == ["a"]


def _iceberg(tmp: str) -> None:
    import pyarrow as pa
    from pyiceberg.catalog.sql import SqlCatalog

    from sverify.io import IcebergSource

    catalog = SqlCatalog("c", uri=f"sqlite:///{tmp}/c.db", warehouse=f"file://{tmp}")
    catalog.create_namespace("n")
    catalog.create_table("n.t", schema=pa.schema([("a", pa.int64())]))
    assert IcebergSource(catalog, "n.t").schema().names == ["a"]


def _flight(tmp: str) -> None:
    import sverify.io.flight  # noqa: F401 - its import needs pyarrow.flight


def _testing(tmp: str) -> None:
    import pyarrow as pa
    from ibis import _

    import sverify as sv
    from sverify.io import StaticSource
    from sverify.testing import cases

    @sv.transform(requires={"t": [_.a > 0]})
    def kept(t):
        return t

    node = StaticSource(pa.table({"a": [1]}), name="t").pipe(kept)
    # `cases` checks the preconditions on an engine, which the extra leaves to
    # the user (`sverify[testing,duckdb]`); alone, it names the engine's extra.
    try:
        cases(node, max_rows=3).example()
    except ValueError as e:
        assert "sverify[duckdb]" in str(e), e
    else:
        raise AssertionError("cases() drew an example with no engine installed")


def _odcs(tmp: str) -> None:
    from sverify import odcs

    path = f"{tmp}/c.odcs.yaml"
    with open(path, "w", encoding="utf-8") as f:
        f.write(
            "apiVersion: v3.2.0\nkind: DataContract\nid: c\nversion: '1'\nstatus: active\n"
            "schema:\n  - name: t\n    properties:\n      - name: a\n        required: true\n"
        )
    assert odcs.read(path).conditions("t")


def _openlineage(tmp: str) -> None:
    from sverify.openlineage import Lineage

    Lineage()  # without a target it configures the OpenLineage client


def _secrets(*modules: str) -> Callable[[str], None]:
    """A secrets backend reads its service through `modules`, imported on
    first use (`sverify.io._secrets`); a lookup would need credentials."""

    def check(tmp: str) -> None:
        for m in modules:
            importlib.import_module(m)

    return check


#: The extras of I/O formats and tools, each checked alone (#183).
EXTRAS: dict[str, Callable[[str], None]] = {
    "delta": _delta,
    "iceberg": _iceberg,
    "flight": _flight,
    "testing": _testing,
    "odcs": _odcs,
    "openlineage": _openlineage,
    "secrets-aws": _secrets("boto3"),
    "secrets-gcp": _secrets("google.cloud.secretmanager"),
    "secrets-azure": _secrets("azure.identity", "azure.keyvault.secrets"),
    "secrets-keychain": _secrets("keyring"),
}


def extra(name: str) -> None:
    """sverify[`name`] alone: no engine runs plans, and its call works."""
    import tempfile

    from sverify import profiles

    assert not [e for e, p in profiles.plugins().items() if p.local], "an engine is installed"
    with tempfile.TemporaryDirectory() as tmp:
        EXTRAS[name](tmp)
    print(f"sverify[{name}]: works alone; pinned {pinned()}")


def main() -> None:
    if sys.argv[1:] == ["--list-extras"]:  # for the workflow's loop, before sverify is installed
        print(" ".join(EXTRAS))
        return
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "combination",
        choices=["base", "duckdb", "polars", "spark", "spark-light", "dbt", *EXTRAS],
    )
    which = parser.parse_args().combination
    if which == "base":
        base()
    elif which == "duckdb":
        check({"duckdb"}, absent=("polars", "pyspark", "sverify_polars", "sverify_spark"))
    elif which == "polars":
        # Polars alone: its connection holds Arrow tables and DuckDB is not installed.
        check({"polars"}, absent=("pyspark", "duckdb"), local="polars")
    elif which == "spark":
        check({"duckdb", "spark"}, absent=("polars",))
    elif which == "spark-light":
        spark_light()
    elif which in EXTRAS:
        extra(which)
    else:
        check({"duckdb"}, absent=("polars", "pyspark"))
        assert "sverify-dbt" in pinned()


if __name__ == "__main__":
    main()
