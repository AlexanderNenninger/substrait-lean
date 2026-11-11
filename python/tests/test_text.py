"""String functions, and the regular expressions that certainly compile.

* Lean's semantics of `substring`, `strpos`, `starts_with`, `ends_with`,
  `btrim`/`ltrim`/`rtrim`, `||`, `character_length` and `LIKE` with a
  backslash escape agrees with DuckDB, the oracle (`core/Sverify/Core/Text.lean`);
  Polars and DuckDB, which run the plan Lean writes, give Lean's rows. `UPPER`,
  `LOWER` and regular expressions, black boxes in Lean pinned to Rust's
  strings, agree with DuckDB on the alphabet drawn here (sverify's DuckDB
  lowering raises on non-ASCII case mapping, #70).
* Polars and DuckDB give Lean's rows of `repeat`, `reverse`, `replace`,
  `ascii` and `levenshtein` (#49) on Rust's edge cases: negative counts,
  empty patterns, combining marks. DuckDB's own functions count bytes or
  grapheme clusters there, so only `replace` has DuckDB as its oracle.
  `ILIKE`, a black box, gives Lean's rows on ASCII text; on other text,
  where Polars folds case as the `regex` crate does, no oracle computes
  the reference.
* Every pattern `Text.simpleRegex` accepts compiles in DuckDB and in Polars:
  this tests the trusted part of the "invalid regular expression" check
  (Lean's evaluator of regular expressions: `test_regex.py`).
* Contracts see through the black boxes as far as they can.
"""

import json
import subprocess
from typing import Any, cast

import ibis
import ibis.expr.types as ir
import pyarrow as pa
import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st
from ibis import _

import sverify as sv
from sverify._unsupported import UnsupportedError
from sverify.engine import (
    connect,
    put_table,
    run_plan,
    substrait_json,
    written_plan,
)
from sverify.ibis_substrait import to_substrait_json
from sverify.sql import Unsupported
from sverify.testing import canonical, duckdb_ibis, duckdb_sql, inline_tables, lean_values

R = ibis.schema({"s": "string", "t": "string", "a": "int64"})

QUERIES = [
    "SELECT substring(s, a, 2) AS x, substring(s, a) AS y, substring(s, a, 0) AS z FROM r",
    "SELECT strpos(s, t) AS p, starts_with(s, t) AS b, ends_with(s, t) AS e FROM r",
    "SELECT s LIKE t AS l, s LIKE 'a%' AS m, s LIKE '_\\%%' AS n FROM r",
    "SELECT btrim(s, t) AS b, ltrim(s, t) AS l, rtrim(s, t) AS r, btrim(s) AS w FROM r",
    "SELECT s || t AS c, character_length(s) AS n FROM r",
]

text = st.one_of(st.none(), st.text(alphabet='ab %_\\é,"', max_size=6))

#: The plans of the queries whose text DuckDB's SQL reads otherwise than the
#: model: `btrim` is DuckDB's `trim`; LIKE with a column pattern or a
#: backslash escape, and regular expressions, are written in Ibis.
PLANS: dict[str, Any] = {
    QUERIES[2]: lambda r: r.select(l=r.s.like(r.t), m=r.s.like("a%"), n=r.s.like("_\\%%")),
    QUERIES[3]: "SELECT trim(s, t) AS b, ltrim(s, t) AS l, rtrim(s, t) AS r, trim(s) AS w FROM r",
}


#: DuckDB's SQL for the queries whose oracle text differs from the plan's:
#: DuckDB's LIKE has no escape character unless one is named.
ORACLE_SQL = {
    QUERIES[2]: "SELECT s LIKE t ESCAPE '\\' AS l, s LIKE 'a%' AS m,"
    " s LIKE '_\\%%' ESCAPE '\\' AS n FROM r",
}


def ends_in_escape(pattern: str | None) -> bool:
    """A pattern ending in an unpaired backslash, which DuckDB's `ESCAPE`
    rejects."""
    return pattern is not None and (len(pattern) - len(pattern.rstrip("\\"))) % 2 == 1


def oracle(con, sql: str) -> list[tuple]:
    """DuckDB's rows of `sql`: its own SQL (`ORACLE_SQL`), or Ibis's DuckDB
    SQL for the queries written in Ibis."""
    source = ORACLE_SQL.get(sql) or PLANS.get(sql, sql)
    if callable(source):
        out = duckdb_ibis(con, source(ibis.table(R, name="r")))
    else:
        out = duckdb_sql(con, source)
    return [tuple(x.values()) for x in out.to_pylist()]


def plan_of(con, sql: str) -> str:
    """The plan of a query here: the lift's of its DuckDB SQL, or the Ibis
    producer's where DuckDB's SQL reads it otherwise (`PLANS`)."""
    source = PLANS.get(sql, sql)
    if callable(source):
        return to_substrait_json(source(con.table("r")))
    return substrait_json(con, source, semantics="duckdb")


@pytest.mark.parametrize("sql", QUERIES)
@settings(
    max_examples=40, deadline=None, suppress_health_check=[HealthCheck.function_scoped_fixture]
)
@given(rows=st.lists(st.tuples(text, text, st.one_of(st.none(), st.integers(-3, 8))), max_size=6))
def test_string_semantics_match_the_oracle(sql, rows):
    if sql in ORACLE_SQL:
        rows = [r for r in rows if not ends_in_escape(r[1])]
    con = connect()
    con.create("r", R, rows)
    expected = oracle(con, sql)
    plan = inline_tables(json.loads(plan_of(con, sql)), {"r": rows})
    assert canonical(lean_values(json.dumps(plan))) == canonical(expected)


#: Black boxes in Lean: only the engines are compared.
BLACK_BOXES = [
    "SELECT upper(s) AS u, lower(t) AS l FROM r",
    "regular expressions",
]
PLANS[BLACK_BOXES[1]] = lambda r: r.select(
    x=r.s.re_search("^a"), y=r.s.re_search("(a)(b|%)"), z=r.t.re_search("é.")
)


@pytest.mark.parametrize("engine", ["polars", "duckdb"])
@pytest.mark.parametrize("sql", QUERIES + BLACK_BOXES)
@settings(
    max_examples=40, deadline=None, suppress_health_check=[HealthCheck.function_scoped_fixture]
)
@given(rows=st.lists(st.tuples(text, text, st.one_of(st.none(), st.integers(-3, 8))), max_size=6))
def test_engines_match_the_oracle(engine, sql, rows):
    """The engines give Lean's rows, or DuckDB's for Lean's black boxes."""
    con = connect()
    con.create("r", R, rows)
    expected = canonical(oracle(con, sql)) if sql in BLACK_BOXES else lean_rows(con, sql, rows)
    plan = written_plan(plan_of(con, sql))
    non_ascii = any(not v.isascii() for r in rows for v in r[:2] if isinstance(v, str))
    if engine == "duckdb" and sql == BLACK_BOXES[0] and non_ascii:
        with pytest.raises(Exception, match="non-ASCII text differs between engines"):
            run_plan(con, plan, engine)
        return
    if engine == "polars" and sql == QUERIES[2]:
        # A pattern per row has no exact native form on Polars (#1270).
        with pytest.raises(UnsupportedError, match="LIKE with a pattern"):
            run_plan(con, plan, engine)
        return
    got = run_plan(con, plan, engine)
    assert canonical(tuple(x.values()) for x in got.to_pylist()) == expected


@pytest.mark.parametrize(
    ("sql", "message"),
    [
        ("SELECT upper(s) AS u FROM r", "UPPER of non-ASCII text"),
        ("SELECT lower(s) AS u FROM r", "LOWER of non-ASCII text"),
    ],
)
def test_lean_refuses_rows_it_does_not_evaluate(sql, message):
    """Lean's evaluator maps ASCII case only; `substrait-check` refuses such
    rows instead of printing placeholders (`''`, NULL) that no engine gives
    (#70). Regular expressions: `test_regex.py`."""
    con = connect()
    rows = [("Straße", "abc", 1)]
    con.create("r", R, rows)
    plan = inline_tables(json.loads(plan_of(con, sql)), {"r": rows})
    with pytest.raises(subprocess.CalledProcessError) as e:
        lean_values(json.dumps(plan))
    assert f"rows not evaluated: {message}" in e.value.stderr
    ascii_rows = inline_tables(
        json.loads(substrait_json(con, sql, semantics="duckdb")), {"r": [("abc", "x", 1)]}
    )
    assert lean_values(json.dumps(ascii_rows)) == [("ABC" if "upper" in sql else "abc",)]


#: Edge cases of #49: combining marks, which `reverse` moves (Rust reverses
#: characters, DuckDB grapheme clusters).
marked = st.one_of(st.none(), st.text(alphabet="ab %\u0301é", max_size=6))
counts = st.one_of(st.none(), st.integers(-2, 3))
#: Engines that compute these as Rust does on ASCII text only raise on others.
ASCII_IN_DUCKDB = "SELECT repeat(s, a) AS r, reverse(s) AS v, ascii(t) AS c FROM r"
# DuckDB reverses grapheme clusters, and the lift reads no `ascii` or
# `levenshtein`: in Ibis.
PLANS[ASCII_IN_DUCKDB] = lambda r: r.select(r=r.s.repeat(r.a), v=r.s.reverse(), c=r.t.ascii_str())
#: Polars has no `levenshtein` and refuses it (#1270).
LEVENSHTEIN = "SELECT levenshtein(s, t) AS d FROM r"
PLANS[LEVENSHTEIN] = lambda r: r.select(d=r.s.levenshtein(r.t))
REPLACE = (
    "SELECT replace(s, 'a', 'xy') AS p, replace(s, 'é', '') AS e, replace(s, ' ', '') AS t FROM r"
)
EMPTY_PATTERN = "SELECT replace(s, '', '-') AS q FROM r"


def lean_rows(con, sql: str, rows: list[tuple]) -> list:
    plan = inline_tables(json.loads(plan_of(con, sql)), {"r": rows})
    return canonical(lean_values(json.dumps(plan)))


@pytest.mark.parametrize("sql", [ASCII_IN_DUCKDB, LEVENSHTEIN, REPLACE, EMPTY_PATTERN])
@settings(
    max_examples=40, deadline=None, suppress_health_check=[HealthCheck.function_scoped_fixture]
)
@given(rows=st.lists(st.tuples(marked, marked, counts), max_size=6))
def test_repeat_reverse_replace_match_the_reference(sql, rows):
    """Polars and DuckDB give Lean's rows. DuckDB is the oracle of `replace`
    with a pattern; its own `repeat`, `reverse`, `ascii` and `levenshtein`
    count bytes or grapheme clusters, and its `replace` of an empty pattern
    returns the string unchanged, so there Lean, the reference, stands alone
    (#1138)."""
    con = connect()
    con.create("r", R, rows)
    expected = lean_rows(con, sql, rows)
    if sql == REPLACE:
        assert canonical(oracle(con, sql)) == expected
    plan = written_plan(plan_of(con, sql))
    if sql == LEVENSHTEIN:
        with pytest.raises(UnsupportedError, match="no levenshtein"):
            run_plan(con, plan, "polars")
    else:
        got = run_plan(con, plan, "polars").to_pylist()
        assert canonical(tuple(x.values()) for x in got) == expected
    non_ascii = any(not v.isascii() for r in rows for v in r[:2] if isinstance(v, str))
    if sql == EMPTY_PATTERN:
        with pytest.raises(Unsupported, match="empty pattern"):
            run_plan(con, plan, "duckdb")
    elif sql in (ASCII_IN_DUCKDB, LEVENSHTEIN) and non_ascii:
        with pytest.raises(Exception, match="non-ASCII text differs between engines"):
            run_plan(con, plan, "duckdb")
    else:
        got = run_plan(con, plan, "duckdb")
        assert canonical(tuple(x.values()) for x in got.to_pylist()) == expected


ILIKE = "SELECT s ILIKE t AS i, s ILIKE 'A%b_' AS j, s NOT ILIKE '%\\%' AS k FROM r"
# A column pattern and a backslash escape: in Ibis.
PLANS[ILIKE] = lambda r: r.select(i=r.s.ilike(r.t), j=r.s.ilike("A%b_"), k=~r.s.ilike("%\\%"))
#: Letters whose case folding is not ASCII's: `'ſ' ILIKE 's'`, `'K' ILIKE 'k'`.
folded = st.one_of(st.none(), st.text(alphabet="aAbB%_\\sſKkÉé", max_size=5))


@settings(
    max_examples=30, deadline=None, suppress_health_check=[HealthCheck.function_scoped_fixture]
)
@given(rows=st.lists(st.tuples(folded, folded, st.none()), max_size=6))
def test_ilike_matches_the_reference(rows):
    """On ASCII text Polars and DuckDB give Lean's rows. Lean evaluates no
    case folding beyond ASCII and DuckDB's differs from the `regex` crate's,
    so on other text Polars runs with no oracle (#1138)."""
    con = connect()
    con.create("r", R, rows)
    plan = written_plan(plan_of(con, ILIKE))
    # `s ILIKE t`, a pattern per row, has no exact native form on Polars (#1270).
    with pytest.raises(UnsupportedError, match="ILIKE with a pattern"):
        run_plan(con, plan, "polars")
    ascii = all(v.isascii() for r in rows for v in r[:2] if isinstance(v, str))
    if not ascii:
        return
    expected = lean_rows(con, ILIKE, rows)
    try:
        got = run_plan(con, plan, "duckdb")
    except Exception as e:  # noqa: BLE001 - DuckDB's error type
        assert not ascii and "non-ASCII text differs between engines" in str(e)
    else:
        assert canonical(tuple(x.values()) for x in got.to_pylist()) == expected


def test_repeat_beyond_two_gigabytes_fails_everywhere():
    """`Text.repeatFits`: the plans Lean writes fail on a result of more than
    2³¹ - 1 bytes; `repeat` of a constant string by a bounded count is proved
    not to."""
    con = connect()
    rows = [("é", "", 2**30)]
    con.create("r", R, rows)
    sql = "SELECT repeat(s, a) AS r FROM r"
    plan = written_plan(substrait_json(con, sql, semantics="duckdb"))
    with pytest.raises(Exception, match="repeat beyond 2\\^31 - 1 bytes"):
        run_plan(con, plan, "duckdb")
    with pytest.raises(Exception, match="repeat beyond 2\\^31 - 1 bytes"):
        run_plan(con, plan, "polars")
    assert errors(T.select(x=T.name.repeat(T.n))) == ["overflow"]
    assert errors(T.select(x=T.name.lpad(10, "ab"))) == []
    e = cast(ir.StringValue, ibis.literal("é"))
    report = sv.verify(T.select(x=e.repeat(T.n)), requires={"t": [_.n <= 2**30]}, on_inferred="off")
    assert [i.kind for i in report.errors] == ["overflow"]
    report = sv.verify(T.select(x=e.repeat(T.n)), requires={"t": [_.n < 2**30]}, on_inferred="off")
    assert report.errors == []


def test_translate_is_refused():
    """`translate` is not modelled: engines differ on what a character is
    (DataFusion's translates grapheme clusters: `translate('e\u0301e', 'e',
    'x')` is `'e\u0301x'`)."""
    with pytest.raises(ValueError, match="translate is not modelled yet"):
        sv.verify(T.select(x=T.name.translate("e", "x")))


T = ibis.table({"name": "string", "n": "int64"}, name="t")


def errors(expr) -> list[str]:
    return [i.kind for i in sv.verify(expr, on_inferred="off").errors]


@given(
    pattern=st.text(alphabet="ab.^$*+?|()[]{}\\-,0123dws", max_size=10)
    | st.from_regex(r"\^?[a-c.]*(\[a-c\]|\\d|\(a\|b\))?[*+?]?\$?", fullmatch=True)
)
@settings(max_examples=40, deadline=None)
def test_patterns_said_to_compile_do(pattern):
    if errors(T.filter(T.name.re_search(pattern))):
        return
    con = connect()
    put_table(con, "t", pa.table({"name": ["abc"], "n": [1]}))
    expr = T.filter(T.name.re_search(pattern))
    duckdb_ibis(con, expr)
    run_plan(con, written_plan(to_substrait_json(expr)), "polars")


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
    with pytest.raises(ValueError, match="negative (substring )?length"):
        sv.verify("SELECT substring(name, 1, -1) AS x FROM t", tables={"t": T})
