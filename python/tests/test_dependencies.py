"""The dependencies sverify installs work together (#442)."""

from __future__ import annotations

from importlib import metadata

import ibis
import pyarrow as pa
import pytest
import sqlglot
from packaging.requirements import Requirement
from packaging.version import Version


@pytest.mark.skipif(
    Version(sqlglot.__version__) >= Version("30.18"),
    reason="development runs SQLGlot 30.22 for fakesnow; the wheel's tests run the pinned one",
)
def test_ibis_duckdb_creates_tables():
    # SQLGlot 30.18 and later write Ibis 12's `DROP VIEW IF EXISTS` without
    # the view's name, and DuckDB rejects it.
    con = ibis.duckdb.connect()
    t = con.create_table("x", pa.table({"a": [1]}))
    assert t.to_pyarrow().to_pydict() == {"a": [1]}


def test_sqlglot_is_pinned_below_the_break():
    try:
        requires = metadata.requires("sverify") or []
    except metadata.PackageNotFoundError:
        pytest.skip("sverify is not installed")
    (sqlglot,) = [r for r in map(Requirement, requires) if r.name == "sqlglot" and not r.marker]
    assert "30.17.0" in sqlglot.specifier
    assert "30.18.0" not in sqlglot.specifier
