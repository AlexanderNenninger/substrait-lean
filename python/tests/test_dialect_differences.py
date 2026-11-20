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
from sverify._unsupported import UnsupportedError
from sverify.report import Report
from sverify.sql_lift import lift
from sverify.sql_lift._base import DUCKDB, REFERENCE

SCHEMA = {"t": ibis.schema({"x": "float64", "d": "decimal(10,2)", "y": "float64"})}


def _found(sql: str, semantics: str = "reference") -> list[str]:
    return [d.key for d in lift(sql, SCHEMA, semantics).differences]


def test_each_silent_difference_is_refused_or_listed() -> None:
    """A `Profile` field in which the reference gives a value (not a raise)
    and DuckDB another is refused by the lift or has a row; a field that joins
    with neither fails."""
    keys = {
        f.name
        for f in dataclasses.fields(REFERENCE)
        if f.name != "name"
        and getattr(REFERENCE, f.name) != getattr(DUCKDB, f.name)
        and getattr(REFERENCE, f.name) != "ERROR"
    }
    assert keys == set(_dialect.TABLE) | set(_dialect.REFUSED)
    assert not set(_dialect.TABLE) & set(_dialect.REFUSED)


@pytest.mark.parametrize(
    ("sql", "spelling"),
    [
        ("SELECT CAST(x AS BIGINT) AS a FROM t", "CAST(round(x) AS BIGINT)"),
        ("SELECT CAST(2.7 AS BIGINT) AS a FROM t", "#322"),
        ("SELECT CAST(d AS BIGINT) AS a FROM t", "#322"),
    ],
)
def test_the_rounding_cast_is_refused_with_its_spellings(sql: str, spelling: str) -> None:
    with pytest.raises(UnsupportedError) as e:
        lift(sql, SCHEMA, "reference")
    assert spelling in str(e.value)
    assert "round(CAST(d AS DOUBLE))" not in str(e.value)


@pytest.mark.parametrize(
    "sql",
    [
        "SELECT CAST(round(x, 2) AS BIGINT) AS a FROM t",
        "SELECT CAST((round(x, 2)) AS BIGINT) AS a FROM t",
    ],
)
def test_a_round_with_digits_is_not_integral_and_is_refused(sql: str) -> None:
    """`round(2.567, 2)` is 2.57, which DuckDB's cast rounds to 3 and the plan truncates to 2."""
    with pytest.raises(UnsupportedError, match="DuckDB's cast"):
        lift(sql, SCHEMA, "reference")


def test_a_parenthesised_round_lifts() -> None:
    assert _found("SELECT CAST((round(x)) AS BIGINT) AS a FROM t") == []


def test_the_where_of_each_plan_is_named(monkeypatch: pytest.MonkeyPatch) -> None:
    """`where` is the query, or the requires or ensures condition the lift read."""
    from sverify import contracts
    from sverify._dialect import difference

    real = contracts.plan_and_differences

    def stub(schemas, query, semantics):
        text, _ = real(schemas, query, semantics)
        return text, (difference("corr_degenerate", "corr(x, y)"),)

    monkeypatch.setattr(contracts, "plan_and_differences", stub)
    r = sv.verify(
        "SELECT x FROM t WHERE x > 0",
        tables={"t": {"x": "DOUBLE"}},
        requires=["x < 10"],
        ensures=["x < 100"],
        counterexamples=0,
    )
    assert sorted(d.where for d in r.dialect_differences) == [
        "the ensures condition x < 100",
        "the query",
        "the requires condition x < 10",
    ]


def test_the_corr_construct_is_listed() -> None:
    assert _found("SELECT corr(x, y) AS c FROM t") == ["corr_degenerate"]


LISTS = {"t": ibis.schema({"l": "array<int64>", "x": "int64"})}


def _found_lists(sql: str, semantics: str = "reference") -> list[str]:
    return [d.key for d in lift(sql, LISTS, semantics).differences]


@pytest.mark.parametrize(
    "sql", ["SELECT list_contains(l, x) AS c FROM t", "SELECT list_has(l, NULL) AS c FROM t"]
)
def test_a_list_contains_with_a_needle_that_may_be_null_is_listed(sql: str) -> None:
    assert _found_lists(sql) == ["list_contains_null_needle"]
    assert _found_lists(sql, "duckdb") == []


def test_a_literal_needle_is_not_listed() -> None:
    assert _found_lists("SELECT list_contains(l, 5) AS c FROM t") == []


def test_the_report_lists_a_list_contains() -> None:
    r = sv.verify(
        "SELECT list_contains(l, x) AS c FROM t",
        tables={"t": {"l": "BIGINT[]", "x": "BIGINT"}},
        counterexamples=0,
    )
    (d,) = r.dialect_differences
    assert (d.key, d.where) == ("list_contains_null_needle", "the query")
    assert "FALSE" in d.dialect and "NULL" in d.here
    assert Report.from_json(r.to_json()).dialect_differences == r.dialect_differences


def test_a_construct_is_listed_once() -> None:
    assert _found("SELECT corr(x, y) AS a, corr(x, y) AS b FROM t") == ["corr_degenerate"]


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
def test_the_spellings_lift_and_are_not_listed(sql: str) -> None:
    assert _found(sql) == []
    assert _found(sql, "duckdb") == []


def test_under_duckdb_semantics_nothing_is_listed() -> None:
    assert _found("SELECT corr(x, y) AS c FROM t", "duckdb") == []


def test_the_report_lists_the_difference_and_keeps_the_verdict() -> None:
    r = sv.verify(
        "SELECT corr(x, y) AS c FROM t",
        tables={"t": {"x": "DOUBLE", "y": "DOUBLE"}},
        requires=["x > 0 AND x < 100 AND y > 0 AND y < 100"],
        counterexamples=0,
    )
    (d,) = r.dialect_differences
    assert (d.key, d.where) == ("corr_degenerate", "the query")
    assert "NaN" in d.dialect
    assert any(n.startswith("dialect: ") for n in r.notes)
    assert Report.from_json(r.to_json()).dialect_differences == r.dialect_differences


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
