"""String functions, and the regular expressions that certainly compile.

* Lean's semantics of `substring`, `strpos`, `starts_with`, `ends_with`,
  `LIKE`, `btrim`/`ltrim`/`rtrim`, `||` and `character_length` agrees with
  DataFusion (`SubstraitLean/Text.lean`), and so do Polars and DuckDB, which
  run the plan Lean writes (also `UPPER`, `LOWER` and regular expressions,
  black boxes in Lean).
* Every pattern `Text.simpleRegex` accepts compiles in DataFusion: this tests
  the trusted part of the "invalid regular expression" check.
* Contracts see through the black boxes as far as they can.
"""

import json

import ibis
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
    got = run_plan(con, plan, engine)
    assert canonical(tuple(x.values()) for x in got.to_pylist()) == expected


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


def test_negative_substring_length_is_rejected():
    with pytest.raises(ValueError, match="negative substring length"):
        sv.verify("SELECT substring(name, 1, -1) AS x FROM t", tables={"t": T})
