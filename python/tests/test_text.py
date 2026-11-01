"""String functions, and the regular expressions that certainly compile.

* Lean's semantics of `substring`, `strpos`, `starts_with`, `ends_with`,
  `LIKE`, `btrim`/`ltrim`/`rtrim`, `||` and `character_length` agrees with
  DataFusion (`SubstraitLean/Text.lean`), and so do Polars and DuckDB, which
  run the plan Lean writes (also `UPPER`, `LOWER` and regular expressions,
  black boxes in Lean, where DuckDB raises on non-ASCII text instead, #70).
* So do `repeat`, `reverse`, `replace`, `ascii` and `levenshtein` (#49), on
  DataFusion's edge cases: negative counts, empty patterns, combining marks.
  `ILIKE`, a black box, agrees on ASCII text, and Polars, with the `regex`
  crate's case folding, agrees on all text.
* Every pattern `Text.simpleRegex` accepts compiles in DataFusion: this tests
  the trusted part of the "invalid regular expression" check.
* Contracts see through the black boxes as far as they can.
"""

import json
import subprocess
from typing import cast

import ibis
import ibis.expr.types as ir
import pyarrow as pa
import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st
from ibis import _

import sverify as sv
from sverify.engine import (
    connect,
    create_table,
    put_table,
    run_plan,
    run_sql,
    substrait_json,
    to_sql,
    written_plan,
)
from sverify.sql import Unsupported
from sverify.testing import canonical, inline_tables, lean_values

R = ibis.schema({"s": "string", "t": "string", "a": "int64"})

QUERIES = [
    "SELECT substring(s, a, 2) AS x, substring(s, a) AS y, substring(s, a, 0) AS z FROM r",
    "SELECT strpos(s, t) AS p, starts_with(s, t) AS b, ends_with(s, t) AS e FROM r",
    "SELECT s LIKE t AS l, s LIKE 'a%' AS m, s LIKE '_\\%%' AS n FROM r",
    "SELECT btrim(s, t) AS b, ltrim(s, t) AS l, rtrim(s, t) AS r, btrim(s) AS w FROM r",
    "SELECT s || t AS c, character_length(s) AS n FROM r",
]

text = st.one_of(st.none(), st.text(alphabet='ab %_\\é,"', max_size=6))


@pytest.mark.parametrize("sql", QUERIES)
@settings(
    max_examples=40, deadline=None, suppress_health_check=[HealthCheck.function_scoped_fixture]
)
@given(rows=st.lists(st.tuples(text, text, st.one_of(st.none(), st.integers(-3, 8))), max_size=6))
def test_string_semantics_match_datafusion(sql, rows):
    con = connect()
    create_table(con, "r", R, rows)
    expected = [tuple(x.values()) for x in run_sql(con, sql).to_pylist()]
    plan = inline_tables(json.loads(substrait_json(con, sql)), {"r": rows})
    assert canonical(lean_values(json.dumps(plan))) == canonical(expected)


#: Black boxes in Lean: only the engines are compared.
BLACK_BOXES = [
    "SELECT upper(s) AS u, lower(t) AS l FROM r",
    "SELECT array_length(regexp_match(s, '^a')) AS x, array_length(regexp_match(s, '(a)(b|%)'))"
    " AS y, array_length(regexp_match(t, 'é.')) AS z FROM r",
]


@pytest.mark.parametrize("engine", ["polars", "duckdb"])
@pytest.mark.parametrize("sql", QUERIES + BLACK_BOXES)
@settings(
    max_examples=40, deadline=None, suppress_health_check=[HealthCheck.function_scoped_fixture]
)
@given(rows=st.lists(st.tuples(text, text, st.one_of(st.none(), st.integers(-3, 8))), max_size=6))
def test_engines_match_datafusion(engine, sql, rows):
    con = connect()
    create_table(con, "r", R, rows)
    expected = canonical(tuple(x.values()) for x in run_sql(con, sql).to_pylist())
    plan = written_plan(substrait_json(con, sql))
    non_ascii = any(not v.isascii() for r in rows for v in r[:2] if isinstance(v, str))
    if engine == "duckdb" and sql == BLACK_BOXES[0] and non_ascii:
        with pytest.raises(Exception, match="non-ASCII text differs between engines"):
            run_plan(con, plan, engine)
        return
    got = run_plan(con, plan, engine)
    assert canonical(tuple(x.values()) for x in got.to_pylist()) == expected


@pytest.mark.parametrize(
    ("sql", "message"),
    [
        ("SELECT upper(s) AS u FROM r", "UPPER of non-ASCII text"),
        ("SELECT lower(s) AS u FROM r", "LOWER of non-ASCII text"),
        ("SELECT array_length(regexp_match(t, 'a')) AS m FROM r", "regular expressions"),
    ],
)
def test_lean_refuses_rows_it_does_not_evaluate(sql, message):
    """Lean's evaluator maps ASCII case only and evaluates no regular
    expressions; `substrait-check` refuses such rows instead of printing
    placeholders (`''`, NULL) that no engine gives (#70)."""
    con = connect()
    rows = [("Straße", "abc", 1)]
    create_table(con, "r", R, rows)
    plan = inline_tables(json.loads(substrait_json(con, sql)), {"r": rows})
    with pytest.raises(subprocess.CalledProcessError) as e:
        lean_values(json.dumps(plan))
    assert f"rows not evaluated: {message}" in e.value.stderr
    if "regexp" not in sql:
        ascii_rows = inline_tables(json.loads(substrait_json(con, sql)), {"r": [("abc", "x", 1)]})
        assert lean_values(json.dumps(ascii_rows)) == [("ABC" if "upper" in sql else "abc",)]


#: Edge cases of #49: combining marks, which `reverse` moves (DataFusion
#: reverses characters, not grapheme clusters).
marked = st.one_of(st.none(), st.text(alphabet="ab %\u0301é", max_size=6))
counts = st.one_of(st.none(), st.integers(-2, 3))
#: Engines that compute these as Rust does on ASCII text only raise on others.
ASCII_IN_DUCKDB = (
    "SELECT repeat(s, a) AS r, reverse(s) AS v, ascii(t) AS c, levenshtein(s, t) AS d FROM r"
)
REPLACE = (
    "SELECT replace(s, 'a', 'xy') AS p, replace(s, 'é', '') AS e, replace(s, ' ', '') AS t FROM r"
)
EMPTY_PATTERN = "SELECT replace(s, '', '-') AS q FROM r"


def lean_rows(con, sql: str, rows: list[tuple]) -> list:
    plan = inline_tables(json.loads(substrait_json(con, sql)), {"r": rows})
    return canonical(lean_values(json.dumps(plan)))


@pytest.mark.parametrize("sql", [ASCII_IN_DUCKDB, REPLACE, EMPTY_PATTERN])
@settings(
    max_examples=40, deadline=None, suppress_health_check=[HealthCheck.function_scoped_fixture]
)
@given(rows=st.lists(st.tuples(marked, marked, counts), max_size=6))
def test_repeat_reverse_replace_match_datafusion(sql, rows):
    con = connect()
    create_table(con, "r", R, rows)
    expected = canonical(tuple(x.values()) for x in run_sql(con, sql).to_pylist())
    assert lean_rows(con, sql, rows) == expected
    plan = written_plan(substrait_json(con, sql))
    assert (
        canonical(tuple(x.values()) for x in run_plan(con, plan, "polars").to_pylist()) == expected
    )
    non_ascii = any(not v.isascii() for r in rows for v in r[:2] if isinstance(v, str))
    if sql == EMPTY_PATTERN:
        with pytest.raises(Unsupported, match="empty pattern"):
            run_plan(con, plan, "duckdb")
    elif sql == ASCII_IN_DUCKDB and non_ascii:
        with pytest.raises(Exception, match="non-ASCII text differs between engines"):
            run_plan(con, plan, "duckdb")
    else:
        got = run_plan(con, plan, "duckdb")
        assert canonical(tuple(x.values()) for x in got.to_pylist()) == expected


ILIKE = "SELECT s ILIKE t AS i, s ILIKE 'A%b_' AS j, s NOT ILIKE '%\\%' AS k FROM r"
#: Letters whose case folding is not ASCII's: `'ſ' ILIKE 's'`, `'K' ILIKE 'k'`.
folded = st.one_of(st.none(), st.text(alphabet="aAbB%_\\sſKkÉé", max_size=5))


@settings(
    max_examples=60, deadline=None, suppress_health_check=[HealthCheck.function_scoped_fixture]
)
@given(rows=st.lists(st.tuples(folded, folded, st.none()), max_size=6))
def test_ilike_matches_datafusion(rows):
    con = connect()
    create_table(con, "r", R, rows)
    expected = canonical(tuple(x.values()) for x in run_sql(con, ILIKE).to_pylist())
    plan = written_plan(substrait_json(con, ILIKE))
    assert (
        canonical(tuple(x.values()) for x in run_plan(con, plan, "polars").to_pylist()) == expected
    )
    ascii = all(v.isascii() for r in rows for v in r[:2] if isinstance(v, str))
    if ascii:
        assert lean_rows(con, ILIKE, rows) == expected
    try:
        got = run_plan(con, plan, "duckdb")
    except Exception as e:  # noqa: BLE001 - DuckDB's error type
        assert not ascii and "non-ASCII text differs between engines" in str(e)
    else:
        assert canonical(tuple(x.values()) for x in got.to_pylist()) == expected


def test_repeat_beyond_two_gigabytes_fails_everywhere():
    """`Text.repeatFits`: DataFusion fails on a result of more than 2³¹ - 1
    bytes, and so do the plans Lean writes; `repeat` of a constant string
    by a bounded count is proved not to."""
    con = connect()
    rows = [("é", "", 2**30)]
    create_table(con, "r", R, rows)
    sql = "SELECT repeat(s, a) AS r FROM r"
    with pytest.raises(Exception, match="string size overflow on repeat"):
        run_sql(con, sql)
    plan = written_plan(substrait_json(con, sql))
    with pytest.raises(Exception, match="repeat beyond 2\\^31 - 1 bytes"):
        run_plan(con, plan, "duckdb")
    with pytest.raises(Exception, match="repeat beyond 2\\^31 - 1 bytes"):
        run_plan(con, plan, "polars")
    assert errors(T.select(x=T.name.repeat(T.n))) == ["overflow"]
    assert errors(T.select(x=T.name.lpad(10, "ab"))) == []
    e = cast(ir.StringValue, ibis.literal("é"))
    report = sv.verify(T.select(x=e.repeat(T.n)), requires={"t": [_.n <= 2**30]})
    assert [i.kind for i in report.errors] == ["overflow"]
    report = sv.verify(T.select(x=e.repeat(T.n)), requires={"t": [_.n < 2**30]})
    assert report.errors == []


def test_translate_is_refused():
    """DataFusion translates grapheme clusters, not characters:
    `translate('e\u0301e', 'e', 'x')` is `'e\u0301x'`."""
    with pytest.raises(ValueError, match="grapheme"):
        sv.verify(T.select(x=T.name.translate("e", "x")))


T = ibis.table({"name": "string", "n": "int64"}, name="t")


def errors(expr) -> list[str]:
    return [i.kind for i in sv.verify(expr).errors]


@given(
    pattern=st.text(alphabet="ab.^$*+?|()[]{}\\-,0123dws", max_size=10)
    | st.from_regex(r"\^?[a-c.]*(\[a-c\]|\\d|\(a\|b\))?[*+?]?\$?", fullmatch=True)
)
@settings(max_examples=150, deadline=None)
def test_patterns_said_to_compile_do(pattern):
    if errors(T.filter(T.name.re_search(pattern))):
        return
    con = connect()
    put_table(con, "t", pa.table({"name": ["abc"], "n": [1]}))
    run_sql(con, to_sql(T.filter(T.name.re_search(pattern))))


def test_regex_checks():
    assert errors(T.filter(T.name.re_search(r"^\d{4}-[a-z]+$"))) == []
    assert errors(T.filter(T.name.re_search("(?i)abc"))) == ["invalid regular expression"]
    assert errors(T.filter(T.name.re_search("a("))) == ["invalid regular expression"]


def test_string_contracts():
    report = sv.verify(
        T.filter(T.name.notnull()).select(
            n=T.name.length(), p=T.name.find("a"), u=T.name.upper(), b=T.name.startswith("x")
        ),
        ensures=[_.n >= 0, _.p >= -1, _.u.notnull(), _.b.notnull()],
    )
    assert report.proved, str(report)
    report = sv.verify(
        T.filter(T.name.notnull()).select(
            a=T.name.ascii_str(),
            d=T.name.levenshtein("x"),
            r=T.name.reverse(),
            p=T.name.lpad(4, "-"),
            i=T.name.ilike("a%"),
        ),
        ensures=[_.a >= 0, _.d >= 0, _.r.notnull(), _.p.notnull(), _.i.notnull()],
    )
    assert report.proved, str(report)


def test_negative_substring_length_is_rejected():
    with pytest.raises(ValueError, match="negative substring length"):
        sv.verify("SELECT substring(name, 1, -1) AS x FROM t", tables={"t": T})
