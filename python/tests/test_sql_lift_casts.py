"""Casts in DuckDB SQL through sverify's own lift (`sverify.sql_lift`):
oracles A and C, the semantics' casts, and the refusals."""

import datetime as dt_
import json

import ibis
import pyarrow as pa
import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

from _sql_lift import SCHEMAS, TABLES
from sverify.engine import run_checker
from sverify.plan_json import Unsupported as Refused
from sverify.sql_lift import lift
from sverify_dev.lift import check

pytestmark = pytest.mark.backend("duckdb")

#: Queries of the subset, each through oracles A and C.
QUERIES = [
    "SELECT id, CAST(qty AS DOUBLE) / 4 AS x, CAST(amount AS INTEGER) AS i,"
    " CAST(qty AS BIGINT) AS b FROM orders",
    # Casts from VARCHAR (#806): DuckDB's rules, black boxes Lean evaluates.
    "SELECT id, TRY_CAST(customer AS BIGINT) AS b, TRY_CAST(customer AS DOUBLE) AS d,"
    " TRY_CAST(customer AS BOOLEAN) AS t, TRY_CAST(customer AS DATE) AS dt,"
    " TRY_CAST(customer AS TIMESTAMP) AS ts, TRY_CAST(customer AS SMALLINT) AS s FROM orders",
    "SELECT id, CAST(CAST(amount AS VARCHAR) || '.5' AS BIGINT) AS b,"
    " CAST(' ' || CAST(qty AS VARCHAR) || 'e1 ' AS DOUBLE) AS d,"
    " CAST('2024-1-' || CAST(amount + 1 AS VARCHAR) AS DATE) AS dt,"
    " CAST('2024-01-05T1' || CAST(amount AS VARCHAR) || ':30:00.25' AS TIMESTAMP) AS ts,"
    " TRY_CAST('12.3 p' AS DOUBLE) AS flagged, TRY_CAST(':' AS DOUBLE) AS missing FROM orders",
]


@pytest.mark.parametrize("query", QUERIES)
def test_oracles_a_and_c(query):
    # A: DuckDB on the SQL, and Lean on the lifted plan. C: DuckDB on the
    # plan Lean writes back.
    result = check(query, TABLES)
    assert result.ok, f"{result.stage}: {result.detail}"


@pytest.mark.parametrize("query", [q for q in QUERIES if isinstance(q, str)])
def test_the_reference_lift_is_checked_too(query):
    plan = json.dumps(lift(query, SCHEMAS, "reference").plan)
    code, out, err = run_checker((), plan)
    assert code == 0, err or out


def test_a_double_cast_to_an_integer_depends_on_the_semantics():
    query = "SELECT CAST(price AS INTEGER) AS i FROM orders"
    with pytest.raises(Refused, match="TIE_TO_EVEN"):
        lift(query, SCHEMAS, "duckdb")
    # The reference truncates (#209 R9), which the plan's cast means.
    assert lift(query, SCHEMAS, "reference").schema == ibis.schema({"i": "int32"})


@pytest.mark.parametrize(
    ("query", "message"),
    [
        ("SELECT '1e38'::DECIMAL(38,0)", "does not fit"),
        ('SELECT 42::TINYINT::"null"', "CAST to"),
        ("SELECT TRY_CAST(id AS INT) FROM orders", "TRY_CAST"),
        ("SELECT CAST(customer AS DECIMAL(10, 2)) AS d FROM orders", "#27"),
        # DuckDB casts an aggregate's argument before its FILTER.
        ("SELECT count(customer::INTEGER) FILTER (WHERE id > 1) AS c FROM orders", "use TRY_CAST"),
        ("SELECT CAST(price AS HUGEINT) FROM orders", "HUGEINT"),
        # Unsigned integers are outside the core (#618): a constant above the
        # signed range is refused, never read as a negative.
        ("SELECT '340282366920938463463374607431768211455'::UHUGEINT", "HUGEINT"),
        ("SELECT 340282366920938463463374607431768211455 AS x", "HUGEINT"),
        ("SELECT 18446744073709551615::UBIGINT", "unsigned"),
        ("SELECT 9223372036854775808::UBIGINT", "unsigned"),
        ("SELECT 4294967295::UINTEGER", "unsigned"),
        ("SELECT CAST(id AS UINTEGER) FROM orders", "unsigned"),
        ("SELECT CAST(NULL AS INT[3]) FROM orders", "fixed-size array"),
        # DuckDB's TIMESTAMP(0) is seconds, TIMESTAMP(1) milliseconds,
        # TIMESTAMP(7) nanoseconds (#626).
        ("SELECT '2020-01-01 01:23:45.123456789'::TIMESTAMP(0)", "precision"),
        ("SELECT '2020-01-01 01:23:45.123456789'::TIMESTAMP(1)", "precision"),
        ("SELECT '2020-01-01 01:23:45.123456789'::TIMESTAMP(7)", "precision"),
    ],
)
def test_refusals_say_what(query, message):
    with pytest.raises(Refused, match=message):
        lift(query, SCHEMAS)


def test_constants_out_of_range_are_cast_not_folded():
    # `200::TINYINT` raises in DuckDB: the plan casts, it doesn't hold an
    # INT8 literal of 200.
    plan = lift("SELECT 200::TINYINT AS x, 100::TINYINT AS y", {}).plan
    exprs = plan["relations"][0]["root"]["input"]["project"]["expressions"]
    assert "cast" in exprs[0] and exprs[1] == {"literal": {"i8": 100}}


def test_a_string_read_as_a_decimal_rounds_as_duckdb():
    # Half away from zero past the scale; DuckDB raises only where the
    # rounded value does not fit.
    query = (
        "SELECT '1.5'::DECIMAL(2,0) AS a, '-2.5'::DECIMAL(2,0) AS b,"
        " '1.25'::DECIMAL(3,1) AS c, '9.4'::DECIMAL(1,0) AS d"
    )
    result = check(query, {})
    assert result.ok, f"{result.stage}: {result.detail}"
    with pytest.raises(Refused, match="does not fit"):
        lift("SELECT '9.99'::DECIMAL(1,0)", {})


@pytest.mark.parametrize("p", [4, 5, 6])
def test_a_microsecond_precision_is_the_models(p):
    # DuckDB reads TIMESTAMP(4) to TIMESTAMP(6) as microseconds.
    plan = lift(f"SELECT '2020-01-01 01:23:45.123456'::TIMESTAMP({p}) AS t", {})
    assert plan.schema == lift("SELECT '2020-01-01 01:23:45.123456'::TIMESTAMP AS t", {}).schema


#: Strings of numbers in the subset Lean evaluates, and strings DuckDB
#: rejects for sure: a character no number has (`VarcharCasts.lean`).
_NUMBERS = st.from_regex(r"\A *[+-]?(\d{1,8}(\.\d{0,5})?|\.\d{1,5})([eE][+-]?\d{1,2})? *\Z")
_NOT_NUMBERS = st.from_regex(r"\A[0-9.]{0,3}[:,%p]{1,2}[0-9]{0,3}\Z")
_BOOLEANS = st.sampled_from(["true", "T", "yes", "Y", "1", "false", "f", "No", "n", "0", " t",
                             "on", "", "tru", "01"])  # fmt: skip


def _date_text(d: dt_.date, short: bool, sep: str) -> str:
    return f"{d.year:04d}{sep}{d.month}{sep}{d.day}" if short else d.isoformat()


_DATES = st.builds(
    _date_text,
    st.dates(dt_.date(1, 1, 1), dt_.date(9999, 12, 31)),
    st.booleans(),
    st.sampled_from(["-", "/", " "]),
)
_BAD_DATES = st.sampled_from(["2024-13-01", "2023-02-29", "2024-04-31", "2024-00-10", "x", ""])
_TIMESTAMPS = st.builds(
    lambda t, sep, digits: (
        t.isoformat(sep=sep, timespec="seconds")
        + ("." + f"{t.microsecond:06d}{t.microsecond % 1000:03d}"[:digits] if digits else "")
    ),
    st.datetimes(dt_.datetime(1, 1, 1), dt_.datetime(9999, 12, 31, 23, 59, 59)),
    st.sampled_from([" ", "T"]),
    st.integers(0, 9),
)


@settings(max_examples=40, deadline=None)
@given(
    vs=st.lists(
        st.one_of(st.none(), _NUMBERS, _NOT_NUMBERS, _BOOLEANS, _DATES, _BAD_DATES, _TIMESTAMPS),
        max_size=10,
    )
)
def test_casts_from_varchar_on_random_strings(vs):
    """`TRY_CAST` of strings to each type through oracles A and C (#806):
    DuckDB on the SQL, Lean's evaluators on the plan, DuckDB on the plan Lean
    writes back."""
    t = pa.table({"s": pa.array(vs, pa.string())})
    query = (
        "SELECT s, TRY_CAST(s AS BIGINT) AS b, TRY_CAST(s AS INTEGER) AS i,"
        " TRY_CAST(s AS DOUBLE) AS d, TRY_CAST(s AS BOOLEAN) AS t, TRY_CAST(s AS DATE) AS dt,"
        " TRY_CAST(s AS TIMESTAMP) AS ts FROM t"
    )
    result = check(query, {"t": t})
    assert result.ok, f"{result.stage}: {result.detail}"


@pytest.mark.parametrize(
    ("value", "kind"),
    [("12.3 p", "BIGINT"), (":", "DOUBLE"), ("maybe", "BOOLEAN"), ("2023-02-29", "DATE"),
     ("2024-01-05 23:60", "TIMESTAMP")],
)  # fmt: skip
def test_a_cast_of_a_bad_string_raises(value, kind):
    """`CAST` raises where `TRY_CAST` is NULL: the plan Lean writes back
    raises on DuckDB, and `verify` reports a domain error (#806)."""
    import sverify as sv
    from sverify.engine import connect, run_plan, written_plan

    sql = f"SELECT CAST(s AS {kind}) AS x FROM t"
    schemas = {"t": ibis.schema({"s": "string"})}
    con = connect()
    con.put("t", pa.table({"s": [value]}))
    with pytest.raises(Exception, match="(?i)conversion|could not convert|invalid"):
        run_plan(con, written_plan(json.dumps(lift(sql, schemas).plan)), "duckdb")
    report = sv.verify(sql, tables=schemas, counterexamples=0, on_inferred="off")
    assert "domain error" in [e.kind for e in report.errors]
    tried = sv.verify(sql.replace("CAST", "TRY_CAST"), tables=schemas, counterexamples=0)
    assert not tried.errors, tried.errors


def test_a_try_cast_to_a_number_proves_nothing_more():
    """`TRY_CAST` may be NULL; `CAST` is not NULL for a string, or raises."""
    import sverify as sv

    schemas = {"t": ibis.schema({"s": "!string"})}
    cast = sv.verify("SELECT CAST(s AS DOUBLE) AS x FROM t", tables=schemas,
                     ensures=["x IS NOT NULL"], counterexamples=0)  # fmt: skip
    assert all(c.proved for c in cast.ensures), cast
    tried = sv.verify("SELECT TRY_CAST(s AS DOUBLE) AS x FROM t", tables=schemas,
                      ensures=["x IS NOT NULL"], counterexamples=0)  # fmt: skip
    assert not any(c.proved for c in tried.ensures), tried
