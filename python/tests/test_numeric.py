"""Integer division, remainder and powers, rounding and casts of doubles, and
runtime errors.

* Lean's semantics of the new functions agrees with DataFusion.
* `sverify` compiles Ibis's integer `//` to exact integer floor division.
* The runtime-error check (`Rel.mayIssues_sound`) reports what it should, and
  whenever DataFusion fails on random data, the check had reported an error:
  this tests the trusted part, the model of when DataFusion evaluates what.
"""

import json
import math

import ibis
import pyarrow as pa
import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st
from ibis import _

import sverify as sv
from sverify.contracts import decode_double
from sverify.engine import connect, create_table, put_table, run_sql, substrait_json, to_sql
from sverify.testing import canonical, inline_tables

R = ibis.schema({"a": "int64", "b": "int64"})
MIN = -(2**63)

INT_QUERIES = [
    "SELECT a, b, a / b AS q, a % b AS m FROM r WHERE b <> 0",
    "SELECT a, CASE WHEN b <> 0 THEN a / b END AS q FROM r",
    "SELECT a / NULLIF(b, 0) AS q, a % NULLIF(b, 0) AS m FROM r",
    "SELECT power(a, 2) AS p, power(b, 3) AS c FROM r",
    "SELECT CAST(a AS VARCHAR) AS s FROM r",
]

small = st.one_of(st.none(), st.integers(-7, 7))


@pytest.mark.parametrize("sql", INT_QUERIES)
@settings(
    max_examples=30, deadline=None, suppress_health_check=[HealthCheck.function_scoped_fixture]
)
@given(rows=st.lists(st.tuples(small, small), max_size=8))
def test_integer_semantics_match_datafusion(sql, rows):
    con = connect()
    create_table(con, "r", R, rows)
    expected = [tuple(x.values()) for x in run_sql(con, sql).to_pylist()]
    plan = inline_tables(json.loads(substrait_json(con, sql)), {"r": rows})
    out = lean_rows_any(json.dumps(plan))
    assert canonical(out) == canonical(expected)


def lean_rows_any(plan_json: str) -> list[tuple]:
    """Like `lean_rows`, but keeps string values (rendered in quotes)."""
    import subprocess

    from sverify.incremental import checker_path

    out = subprocess.run(
        [str(checker_path()), "/dev/stdin"],
        input=plan_json,
        capture_output=True,
        text=True,
        check=True,
    ).stdout
    rows = out.split("rows (")[1].splitlines()[1:]

    def value(x: str):
        if x == "NULL":
            return None
        if x.startswith('"'):
            return json.loads(x)
        if x.endswith("d"):  # a double, printed with six decimals
            return float(x[:-1])
        return int(x)

    return [tuple(value(x) for x in line.strip()[1:-1].split(", ")) for line in rows]


#: Finite doubles where rounding could go wrong: halves, results of -0.0
#: (`CEIL(-0.5)`), the largest doubles a BIGINT holds. (JSON has no -0.0, so it
#: can't be an input here; `FloatCode` checks it in Lean.)
DOUBLES = [0.0, 0.5, -0.5, 1.5, -1.5, 2.5, -2.5, 2.7, -2.7, 1e15 + 0.5, 9.2e18, -9.2e18, 3.0]
F = ibis.schema({"f": "float64"})


@pytest.mark.parametrize(
    "sql",
    [
        "SELECT f, floor(f) AS x, ceil(f) AS y, round(f) AS z FROM r",
        "SELECT f, CAST(f AS BIGINT) AS i FROM r",
    ],
)
def test_rounding_semantics_match_datafusion(sql):
    con = connect()
    rows = [(f,) for f in DOUBLES]
    create_table(con, "r", F, rows)
    expected = [tuple(x.values()) for x in run_sql(con, sql).to_pylist()]
    plan = inline_tables(json.loads(substrait_json(con, sql)), {"r": rows})
    got = lean_rows_any(json.dumps(plan))
    # Doubles come back printed, or as codes when tiny (±0.0); `CAST(... AS
    # BIGINT)` as integers.
    decoded = [
        tuple(
            decode_double(v) if isinstance(e, float) and isinstance(v, int) else v
            for v, e in zip(row, want, strict=True)
        )
        for row, want in zip(got, expected, strict=True)
    ]
    for d, e in zip(decoded, expected, strict=True):
        for x, y in zip(d, e, strict=True):
            assert x == y and math.copysign(1, x) == math.copysign(1, y), (d, e)


@given(
    pairs=st.lists(
        st.tuples(
            st.one_of(st.integers(-10, 10), st.integers(-(2**62), 2**62), st.just(MIN + 1)),
            st.one_of(st.integers(-4, 4), st.integers(1, 2**40)).filter(bool),
        ),
        min_size=1,
        max_size=10,
    )
)
@settings(max_examples=30, deadline=None)
def test_integer_floor_division_is_exact(pairs):
    con = connect()
    t = ibis.table(R, name="r")
    create_table(con, "r", R, pairs)
    got = [r["q"] for r in run_sql(con, to_sql(t.select(q=t.a // t.b))).to_pylist()]
    assert got == [a // b for a, b in pairs]


T = ibis.table({"qty": "int64", "n": "int64", "amount": "float64"}, name="t")


def errors(expr) -> list[str]:
    return [i.kind for i in sv.verify(expr).errors]


@pytest.mark.parametrize(
    ("label", "expr", "kinds"),
    [
        ("constant divisor", T.select(x=T.qty // 2, y=T.qty % 3), []),
        ("column divisor", T.select(x=T.qty // T.n), ["division by zero", "overflow"]),
        ("filter n != 0", T.filter(T.n != 0).select(x=T.qty % T.n), []),
        ("filter n != 0, divide", T.filter(T.n != 0).select(x=T.qty // T.n), ["overflow"]),
        ("filter n > 0", T.filter(T.n > 0).select(x=T.qty // T.n), []),
        ("nullif", T.select(x=T.qty % T.n.nullif(0)), []),
        ("case guard", T.select(x=ibis.cases((T.n > 0, T.qty // T.n), else_=0)), []),
        (
            "guard in an earlier filter",
            T.filter(T.n != 0).filter((T.qty % T.n) > 1),
            ["division by zero"],
        ),
        ("guard in the same AND", T.filter((T.n != 0) & ((T.qty % T.n) > 1)), ["division by zero"]),
        ("unbounded cast", T.select(x=T.amount.round()), ["cast out of range"]),
        (
            "bounded cast",
            T.filter((T.amount >= 0) & (T.amount <= 100)).select(x=T.amount.round()),
            [],
        ),
        ("square", T.select(x=T.qty**2), ["overflow"]),
        ("bounded square", T.filter(T.qty.between(-1000, 1000)).select(x=T.qty**2), []),
    ],
)
def test_runtime_errors_are_reported(label, expr, kinds):
    assert sorted(set(errors(expr))) == sorted(kinds), label


def test_bounded_round_gives_bounded_integers():
    report = sv.verify(
        T.filter((T.amount >= 0) & (T.amount <= 100)).select(x=T.amount.round()),
        ensures=[_.x >= 0, _.x <= 100],
    )
    assert report.proved, str(report)
    assert report.facts["x"] == "an integer in [0, 100]"


def test_contracts_fail_on_possible_errors():
    @sv.transform(ensures=[])
    def ratio(t):
        return t.select(x=t.qty // t.n)

    with pytest.raises(sv.VerificationError, match="division by zero"):
        ratio(T)


def test_wrapping_is_only_a_warning():
    report = sv.verify(T.select(x=T.qty + 1))
    assert report.proved
    assert [i.kind for i in report.warnings] == ["may wrap around"]


#: Pipelines over `t(qty, n)`; small values plus the extremes where division
#: overflows.
PIPELINES = [
    T.select(x=T.qty // T.n),
    T.select(x=T.qty % T.n),
    T.filter(T.n != 0).select(x=T.qty // T.n),
    T.filter(T.n != 0).filter((T.qty // T.n) > 1),
    T.filter((T.n != 0) & ((T.qty % T.n) > 0)),
    T.filter(T.n > 0).select(x=T.qty // T.n, y=T.qty % T.n),
    T.select(x=T.qty // T.n.nullif(0)),
    T.select(x=ibis.cases((T.n != 0, T.qty % T.n), else_=-1)),
    T.select(x=T.qty**T.n),
    T.filter(T.n.between(0, 3) & T.qty.between(-100, 100)).select(x=T.qty**T.n),
    T.mutate(m=T.qty % T.n.nullif(0)).filter(_.m > 0),
]
values = st.one_of(st.integers(-3, 3), st.sampled_from([MIN, 2**63 - 1, -1]), st.none())


@pytest.mark.parametrize("i", range(len(PIPELINES)))
@settings(
    max_examples=25, deadline=None, suppress_health_check=[HealthCheck.function_scoped_fixture]
)
@given(rows=st.lists(st.tuples(values, values), max_size=6))
def test_datafusion_fails_only_where_reported(i, rows):
    expr = PIPELINES[i]
    reported = errors(expr)
    con = connect()
    put_table(
        con,
        "t",
        pa.table(
            {
                "qty": pa.array([q for q, _ in rows], pa.int64()),
                "n": pa.array([n for _, n in rows], pa.int64()),
                "amount": pa.array([1.0 for _ in rows], pa.float64()),
            }
        ),
    )
    try:
        run_sql(con, to_sql(expr))
    except Exception as e:  # noqa: BLE001 - any engine failure counts
        assert reported, f"DataFusion failed ({e}) but no error was reported"
