"""Where the reference reads a DuckDB SQL text differently from DuckDB (#1484, D54).

`Report.dialect_differences` lists each construct the lift read with a value
the reference gives and DuckDB does not. The table is keyed by the `Profile`
fields in which the two profiles differ and the reference does not raise.
"""

import dataclasses
from pathlib import Path

import ibis
import pytest

import sverify as sv
from _repo import needs_repo
from sverify import _dialect
from sverify.report import Report
from sverify.sql_lift import lift
from sverify.sql_lift._base import DUCKDB, REFERENCE

SCHEMA = {"t": ibis.schema({"x": "float64", "d": "decimal(10,2)", "y": "float64"})}


def _found(sql: str, semantics: str = "reference") -> list[str]:
    return [d.key for d in lift(sql, SCHEMA, semantics).differences]


def test_the_table_has_a_row_for_each_silent_difference() -> None:
    """A `Profile` field in which the reference gives a value (not a raise)
    and DuckDB another has a row; a field that joins with no row fails."""
    keys = {
        f.name
        for f in dataclasses.fields(REFERENCE)
        if f.name != "name"
        and getattr(REFERENCE, f.name) != getattr(DUCKDB, f.name)
        and getattr(REFERENCE, f.name) != "ERROR"
    }
    assert keys == set(_dialect.TABLE)


@pytest.mark.parametrize(
    ("sql", "key"),
    [
        ("SELECT CAST(x AS BIGINT) AS a FROM t", "float_to_int"),
        ("SELECT CAST(d AS BIGINT) AS a FROM t", "decimal_to_int"),
        ("SELECT corr(x, y) AS c FROM t", "corr_degenerate"),
    ],
)
def test_the_lift_records_each_construct(sql: str, key: str) -> None:
    assert _found(sql) == [key]


def test_a_construct_is_listed_once() -> None:
    assert _found("SELECT CAST(x AS BIGINT) AS a, CAST(x AS BIGINT) AS b FROM t") == [
        "float_to_int"
    ]


@pytest.mark.parametrize(
    "sql",
    [
        "SELECT CAST(round(x) AS BIGINT) AS a FROM t",
        "SELECT CAST(floor(x) AS BIGINT) AS a FROM t",
        "SELECT CAST(ceil(x) AS BIGINT) AS a FROM t",
        "SELECT CAST(round(CAST(d AS DOUBLE)) AS BIGINT) AS a FROM t",
        "SELECT CAST(x AS DOUBLE) AS a FROM t",
    ],
)
def test_the_spellings_mean_the_same_and_are_not_listed(sql: str) -> None:
    assert _found(sql) == []
    assert _found(sql, "duckdb") == []


def test_under_duckdb_semantics_nothing_is_listed() -> None:
    assert _found("SELECT corr(x, y) AS c FROM t", "duckdb") == []


def test_the_report_lists_the_difference_and_keeps_the_verdict() -> None:
    r = sv.verify(
        "SELECT CAST(x AS BIGINT) AS y FROM t WHERE x > 0 AND x < 100",
        tables={"t": {"x": "DOUBLE"}},
        counterexamples=0,
    )
    assert r.verdict == sv.Verdict.PROVED
    (d,) = r.dialect_differences
    assert (d.key, d.where) == ("float_to_int", "the query")
    assert "1.5" in d.example and "round(x)" in d.spellings
    assert any(n.startswith("dialect: ") for n in r.notes)
    assert Report.from_json(r.to_json()).dialect_differences == r.dialect_differences


def test_a_condition_names_where_it_is() -> None:
    r = sv.verify(
        "SELECT x FROM t WHERE x > 0 AND x < 100",
        tables={"t": {"x": "DOUBLE"}},
        ensures=["CAST(x AS BIGINT) >= 0"],
        counterexamples=0,
    )
    assert [d.where for d in r.dialect_differences] == [
        "the ensures condition CAST(x AS BIGINT) >= 0"
    ]


def test_an_ibis_transformation_lists_nothing() -> None:
    t = ibis.table({"x": "float64"}, name="t")
    r = sv.verify(t.select(y=t.x.cast("int64")), counterexamples=0)
    assert r.dialect_differences == ()


@needs_repo
def test_the_docs_name_each_key() -> None:
    text = (Path(__file__).parent.parent.parent / "docs" / "reference-semantics.md").read_text()
    section = text.split("## DuckDB SQL under the reference", 1)[1].split("\n## ", 1)[0]
    for key in _dialect.TABLE:
        assert f"`{key}`" in section, key
