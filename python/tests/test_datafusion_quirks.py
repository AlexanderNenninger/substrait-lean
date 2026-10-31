"""DataFusion's surprising semantics, pinned (`notebooks/16_datafusion_semantics.py`).

The first half pins what DataFusion does where the Lean model relies on it
(the total order on doubles, truncating division, which operations fail and
which wrap around), so an upgrade that changes one of them fails here.

The second half is the soundness gaps the notebook found: places where
`verify` proves something DataFusion's output contradicts, or claims no
runtime error is possible where DataFusion fails. Each is a strict `xfail`
that asserts the sound outcome, so fixing the gap makes it pass and fails
the run until the marker is removed.
"""

import datetime as dt
import json
import subprocess
from pathlib import Path

import numpy as np
import pyarrow as pa
import pytest

import sverify as sv
from sverify.engine import (
    connect,
    put_table,
    run_plan,
    run_sql,
    run_substrait_json,
    substrait_json,
)
from sverify.incremental import arrow_rows
from sverify.testing import inline_tables, lean_rows, lean_values

pytestmark = pytest.mark.backend("datafusion")

FIXTURES = Path(__file__).resolve().parents[2] / "tests" / "fixtures"


def ints(**cols: list) -> pa.Table:
    return pa.table({k: pa.array(v, pa.int64()) for k, v in cols.items()})


TABLES = {
    "n": ints(x=[1, None, 2]),
    "s": ints(y=[1, None]),
    "f": pa.table({"v": [1.0, float("nan"), 0.0, float("inf"), float("-inf"), None]}),
    "t": ints(a=[5, 0], b=[1, 0]),
    "m": ints(a=[-(2**63), 5]),
    "mx": ints(a=[2**63 - 1]),
    "dm": ints(a=[-7, 7], b=[2, -2]),
    "pn": ints(a=[None, 2]),
    "mixed": pa.table({"a": pa.array([1], pa.int64()), "f": [0.5]}),
    "i32": pa.table({"a": pa.array([2**31 - 1], pa.int32()), "b": pa.array([1], pa.int32())}),
    "u8": pa.table({"a": pa.array([0], pa.uint8()), "b": pa.array([1], pa.uint8())}),
    "str": pa.table({"s": ["b", "B", "a", "", "é", "z"]}),
    "str5": pa.table({"s": ["5", "05"]}),
    "is": pa.table({"a": pa.array([10, 10, -3, None], pa.int64()), "s": ["10", "010", "-3", "x"]}),
    "nanp": pa.table(
        {
            "v": pa.array(
                np.array([0x7FF8000000000001, 0x7FF8000000000000], np.uint64).view(np.float64)
            )
        }
    ),
    "z": pa.table(
        {
            "t": pa.array(
                [dt.datetime(2024, 3, 30, 12, tzinfo=dt.UTC)],
                pa.timestamp("us", tz="Europe/Berlin"),
            )
        }
    ),
}


@pytest.fixture(scope="module")
def con():
    """The tables as the model has them (`put_table`: one zero, one NaN), and
    in DataFusion as they are, so that its own answers show its own order."""
    c = connect()
    for name, t in TABLES.items():
        put_table(c, name, t)
    ctx = c.datafusion
    for name, t in TABLES.items():
        ctx.deregister_table(name)
        ctx.register_record_batches(name, [t.to_batches()])
    return c


def rows(con, sql: str) -> list[tuple]:
    return arrow_rows(con.datafusion.sql(sql).to_arrow_table())


def nan_aware(rows: list[tuple]) -> list[tuple]:
    return [tuple("NaN" if isinstance(v, float) and v != v else v for v in r) for r in rows]


@pytest.mark.parametrize(
    ("sql", "expected"),
    [
        # NULLs: three-valued logic.
        ("SELECT x FROM n WHERE x NOT IN (1, NULL)", []),
        ("SELECT n.x, s.y FROM n JOIN s ON n.x = s.y", [(1, 1)]),
        ("SELECT n.x, s.y FROM n JOIN s ON n.x IS NOT DISTINCT FROM s.y", [(1, 1), (None, None)]),
        ("SELECT x, greatest(x, 0) AS g FROM n ORDER BY x", [(1, 1), (2, 2), (None, 0)]),
        # Doubles: Arrow's total order, NaN = NaN, -0.0 < 0.0.
        (
            "SELECT v, v = v, -v = v, -v < v FROM f WHERE v = 0 OR isnan(v) ORDER BY v",
            [(0.0, True, False, True), ("NaN", True, False, True)],
        ),
        (
            "SELECT w FROM (SELECT v AS w FROM f UNION ALL SELECT -v FROM f) "
            "WHERE w > 1e308 OR w = 0 OR w < -1e308 ORDER BY w",
            # `w = 0` misses -0.0: they are different doubles.
            [("NaN",), (-np.inf,), (-np.inf,), (0.0,), (np.inf,), (np.inf,), ("NaN",)],
        ),
        ("SELECT max(v) AS mx FROM f", [("NaN",)]),
        ("SELECT a.v = b.v FROM nanp a CROSS JOIN nanp b", [(True,), (False,), (False,), (True,)]),
        ("SELECT count(DISTINCT v) FROM nanp", [(2,)]),
        # Integers: truncating division, silent wrap-around of + - *.
        ("SELECT a / b, a % b FROM dm", [(-3, -1), (-3, 1)]),
        ("SELECT a + 1, -a, a * 2 FROM mx", [(-(2**63), -(2**63) + 1, -2)]),
        ("SELECT a % -1 FROM m", [(0,), (0,)]),
        ("SELECT a + b, arrow_typeof(a + b) FROM i32", [(-(2**31), "Int32")]),
        ("SELECT a - b FROM u8", [(255,)]),
        ("SELECT power(a, 0) FROM pn", [(1,), (1,)]),
        ("SELECT s, s = 5 FROM str5", [("5", True), ("05", False)]),
        # Strings: byte order, code points.
        ("SELECT s FROM str ORDER BY s", [("",), ("B",), ("a",), ("b",), ("z",), ("é",)]),
        ("SELECT character_length('é'), upper('ß')", [(2, "SS")]),
        # Time: a day of a zoned timestamp is 23 hours across the DST switch.
        ("SELECT t + INTERVAL '1 day' >= t + INTERVAL '24 hours' FROM z", [(False,)]),
        ("SELECT INTERVAL '1 day' = INTERVAL '24 hours'", [(False,)]),
        # Lazy numeric CASE.
        ("SELECT CASE WHEN b <> 0 THEN a / b END FROM t", [(5,), (None,)]),
        # DataFusion's own bug: NOT IN ignores the subquery's NULL (SQL: no rows).
        ("SELECT x FROM n WHERE x NOT IN (SELECT y FROM s) ORDER BY x", [(2,), (None,)]),
        # INTERSECT ALL and EXCEPT ALL are a semi and an anti join: every
        # left copy stays or goes (SQL: min(m, n) and max(m - n, 0) copies).
        # The Ibis producer writes SQL's meaning (`sverify.coverage.DATAFUSION_SQL`).
        (
            "SELECT * FROM (VALUES (1), (1), (1), (2)) a(x) "
            "INTERSECT ALL SELECT * FROM (VALUES (1), (3)) b(x) ORDER BY x",
            [(1,), (1,), (1,)],
        ),
        (
            "SELECT * FROM (VALUES (1), (1), (2)) a(x) "
            "EXCEPT ALL SELECT * FROM (VALUES (1)) b(x) ORDER BY x",
            [(2,)],
        ),
    ],
)
def test_datafusion_behaviour(con, sql, expected):
    assert nan_aware(rows(con, sql)) == nan_aware(expected)


@pytest.mark.parametrize(
    ("sql", "error"),
    [
        ("SELECT a / b FROM t", "DivideByZero"),
        ("SELECT a % b FROM t", "DivideByZero"),
        ("SELECT a / -1 FROM m", "Overflow"),
        ("SELECT abs(a) FROM m", "overflow"),
        ("SELECT CAST(a AS INT) FROM m", "Can't cast"),
        ("SELECT CAST(v AS BIGINT) FROM f WHERE isnan(v)", "Cast"),
        # The evaluation order Safety.lean models (`AND`, pushed-down filters) …
        ("SELECT a FROM t WHERE b <> 0 AND a / b > 1", "DivideByZero"),
        ("SELECT a FROM (SELECT * FROM t WHERE b <> 0) WHERE a / b > 1", "DivideByZero"),
        # … and where it does not hold: boolean CASE becomes AND; COALESCE is eager.
        ("SELECT CASE WHEN b <> 0 THEN a / b > 1 ELSE false END FROM t", "DivideByZero"),
        ("SELECT coalesce(b, a / b) FROM t", "DivideByZero"),
    ],
)
def test_datafusion_fails(con, sql, error):
    with pytest.raises(Exception, match=error):
        rows(con, sql)


def test_plan_has_coercion_casts(con):
    """`substrait_json` writes the analysed plan, with DataFusion's implicit
    casts explicit (`CAST(a AS DOUBLE) > f`), and leaves the session's
    optimizer settings as they were."""
    passes = rows(con, "SHOW datafusion.optimizer.max_passes")
    plan = substrait_json(con, "SELECT a > f AS gt FROM mixed")
    assert '"cast"' in plan
    assert arrow_rows(run_substrait_json(con, plan)) == [(True,)]
    assert rows(con, "SHOW datafusion.optimizer.max_passes") == passes


def test_distinct_plan_is_not_readable_by_datafusion(con):
    """DataFusion writes DISTINCT as one empty grouping and rejects it; Lean's
    rewrite runs."""
    plan = substrait_json(con, "SELECT DISTINCT x FROM n")
    with pytest.raises(Exception, match="Aggregate requires at least one grouping"):
        run_substrait_json(con, plan)
    assert sorted(arrow_rows(run_substrait_json(con, sv.written_plan(plan))), key=str) == [
        (1,),
        (2,),
        (None,),
    ]


def test_lean_writes_the_current_fetch_fields(con):
    """R2: DataFusion's protobuf no longer has the deprecated
    `FetchRel.offset`/`count`; Lean writes `offsetExpr`/`countExpr`."""
    plan = sv.written_plan(substrait_json(con, "SELECT x FROM n ORDER BY x LIMIT 1"))
    assert '"countExpr"' in plan and '"count":' not in plan
    assert arrow_rows(run_substrait_json(con, plan)) == [(1,)]


def test_lean_writes_virtual_tables_with_their_types(con):
    """A VirtualTable's `baseSchema` used to be placeholder `i64` columns,
    which DataFusion checks the rows against."""
    plan = (FIXTURES / "virtual_left_join.json").read_text()
    rows = arrow_rows(run_substrait_json(con, sv.written_plan(plan)))
    assert sorted(rows, key=str) == sorted(lean_rows(plan), key=str)


def test_integer_sum_fails_instead_of_wrapping(con):
    """DataFusion's integer SUM wraps around past 64 bits, where `Rel.eval`'s
    is exact. The plan Lean writes for DataFusion sums as DECIMAL(38,0) and
    casts back, which fails instead (#24); within range it agrees."""
    twice = "SELECT a FROM mx UNION ALL SELECT a FROM mx"
    over = sv.written_plan(substrait_json(con, f"SELECT sum(a) AS s FROM ({twice})"))
    assert arrow_rows(run_substrait_json(con, over)) == [(-2,)]  # wrapped around
    with pytest.raises(Exception, match="out of range Int64"):
        run_plan(con, over, "datafusion")
    sql = "SELECT b, sum(a) AS s, count(*) AS c FROM dm GROUP BY b"
    within = sv.written_plan(substrait_json(con, sql))
    translated = sorted(arrow_rows(run_plan(con, within, "datafusion")))
    assert (
        translated
        == sorted(arrow_rows(run_substrait_json(con, within)))
        == [(-2, 7, 1), (2, -7, 1)]
    )


@pytest.mark.parametrize(
    "sql, expected",
    [
        (
            "SELECT 'x' AS c FROM s UNION ALL SELECT CAST(NULL AS VARCHAR) FROM s",
            ["x", "x", None, None],
        ),
        (
            "WITH RECURSIVE r AS (SELECT 0 AS d UNION ALL SELECT d + 1 FROM r WHERE d < 2) "
            "SELECT d FROM r",
            [0, 1, 2],
        ),
    ],
)
def test_union_batches_differ_in_nullability(con, sql, expected):
    """A `UNION ALL` gives record batches whose schemas differ in nullability
    (and, for a recursive CTE, in column names), which DataFusion's own
    `to_arrow_table()` fails to concatenate; `run_sql` (`engine.collect`)
    reconciles them, here and for plans (`run_substrait_json`)."""
    with pytest.raises(Exception, match="Schema at index 1 was different"):
        con.datafusion.sql(sql).to_arrow_table()
    expected = sorted([(v,) for v in expected], key=str)
    assert sorted(arrow_rows(run_sql(con, sql)), key=str) == expected
    if "RECURSIVE" not in sql:  # DataFusion's producer has no recursive queries
        plan = substrait_json(con, sql)
        assert sorted(arrow_rows(run_substrait_json(con, plan)), key=str) == expected


def test_not_in_subquery_means_what_sql_means(con):
    """DataFusion keeps rows (`test_datafusion_behaviour`); the checker lifts
    the subquery with SQL's NULL rules, so `s`'s NULL leaves none."""
    plan = substrait_json(con, "SELECT x FROM n WHERE x NOT IN (SELECT y FROM s)")

    def lean(s: list[tuple]) -> list[tuple]:
        rows = {"n": [(1,), (None,), (2,)], "s": s}
        return lean_values(json.dumps(inline_tables(json.loads(plan), rows)))

    assert lean([(1,), (None,)]) == []
    assert lean([(1,)]) == [(2,)]
    assert lean([]) == [(1,), (None,), (2,)]


def test_lean_prints_integers_beyond_64_bits(con):
    """`Rel.eval`'s integers are unbounded: `MAX + 1` is printed as itself (and
    a doubled column as doubles), not as a double's code (#72)."""
    plan = json.loads(substrait_json(con, "SELECT a + 1 AS s, -a AS n FROM mx WHERE a > 0"))
    lean = lean_rows(json.dumps(inline_tables(plan, {"mx": [(2**63 - 1,)]})))
    assert lean == [(2**63, -(2**63) + 1)]
    plan = json.loads(substrait_json(con, "SELECT -a AS n FROM m"))
    assert lean_rows(json.dumps(inline_tables(plan, {"m": [(-(2**63),)]}))) == [(2**63,)]


def verify(sql: str, table: str, schema: dict, requires=(), ensures=()) -> sv.Report:
    return sv.verify(
        sql, requires={table: list(requires)}, ensures=list(ensures), tables={table: schema}
    )


I64 = {"a": "int64", "b": "int64"}


def test_reported_runtime_errors():
    assert [i.kind for i in verify("SELECT a / b AS q FROM t", "t", I64, ["a >= 0"]).errors] == [
        "division by zero"
    ]
    report = verify("SELECT a + 1 AS s FROM t", "t", I64)
    assert report.proved and [i.kind for i in report.warnings] == ["may wrap around"]


gap = pytest.mark.xfail(
    strict=True, reason="soundness gap, see notebooks/16_datafusion_semantics.py"
)


def test_int_vs_double_comparison():
    """F6: `1 > 0.5`; the analysed plan casts the integer to a double."""
    report = verify(
        "SELECT a > f AS gt FROM t",
        "t",
        {"a": "int64", "f": "float64"},
        ["a = 1", "f = 0.5"],
        ["NOT gt"],
    )
    assert not report.ensures[0].proved


def test_int_concat_string():
    """N7: `x || 'a'` is '1a'; the analysed plan casts the integer to text."""
    report = verify("SELECT x || 'a' AS p FROM n", "n", {"x": "int64"}, ensures=["p IS NULL"])
    assert not report.ensures[0].proved


def test_string_order_is_datafusions(con):
    """Strings compare by code point (UTF-8 byte order), as in DataFusion."""
    sql = "SELECT s, s < 'b' AS lt, s >= 'B' AS ge, s > 'é' AS gt FROM str"
    plan = json.loads(substrait_json(con, sql))
    rows_ = [(s,) for s in ["b", "B", "a", "", "é", "z"]]
    assert lean_rows(json.dumps(inline_tables(plan, {"str": rows_}))) == rows(con, sql)


def test_int_compared_with_string_compares_text(con):
    """DataFusion casts the integer to text, so `10 = '010'` is false; the
    analysed plan has the cast."""
    sql = 'SELECT a, s, a = s AS e FROM "is"'
    plan = json.loads(substrait_json(con, sql))
    rows_ = [(10, "10"), (10, "010"), (-3, "-3"), (None, "x")]
    assert lean_rows(json.dumps(inline_tables(plan, {"is": rows_}))) == rows(con, sql)


def test_string_order_comparison():
    """S6: `'z' > 'd'` is true; Lean's `lt` is only defined on integers."""
    report = verify(
        "SELECT s > 'd' AS gt FROM t", "t", {"s": "string"}, ["s = 'z'"], ["gt IS NULL"]
    )
    assert not report.ensures[0].proved


def test_int32_wraps_at_32_bits():
    """I6: DataFusion's INT + INT wraps at 2^31."""
    report = verify(
        "SELECT a + b AS s FROM t",
        "t",
        {"a": "int32", "b": "int32"},
        ["a BETWEEN 0 AND 2147483647", "b BETWEEN 0 AND 2147483647"],
        ["s >= 0"],
    )
    assert not report.ensures[0].proved or report.warnings


def test_int32_wrap_in_lean_and_datafusion(con):
    """`Rel.eval` computes `INT + INT` unbounded, warning that DataFusion wraps;
    `INT + 1` is a `BIGINT` in DataFusion and does not wrap. Lean's written
    plan computes at the same widths."""
    sql = "SELECT a + b AS s, a + 1 AS t FROM i32"
    plan = substrait_json(con, sql)
    assert lean_rows(json.dumps(inline_tables(json.loads(plan), {"i32": [(2**31 - 1, 1)]}))) == [
        (2**31, 2**31)
    ]
    assert arrow_rows(run_substrait_json(con, sv.written_plan(plan))) == rows(con, sql)
    report = verify(sql.replace("i32", "t"), "t", {"a": "int32", "b": "int32"})
    assert ("may wrap around", "WRAP32(($0 + $1))") in [(i.kind, i.expr) for i in report.warnings]
    assert not any(i.expr.startswith("WRAP32(($0 + 1") for i in report.warnings)


def test_uint8_is_refused():
    """I7: 0 - 1 is 255 for UINT8; unsigned integers are not modelled."""
    with pytest.raises(ValueError, match="unsigned"):
        verify("SELECT a - b AS d FROM t", "t", {"a": "uint8", "b": "uint8"})


def test_narrowing_cast_may_fail():
    """I8: `CAST(bigint AS INT)` raises out of range (`UnFn.narrow`), unless
    the input is known to fit."""
    assert [i.kind for i in verify("SELECT CAST(a AS INT) AS x FROM t", "t", I64).errors] == [
        "cast out of range"
    ]
    fits = ["a >= -2147483648", "a <= 2147483647"]
    assert verify("SELECT CAST(a AS INT) AS x FROM t", "t", I64, fits).proved


def test_abs_of_min_fails():
    """I4: `abs(MIN)` raises; it does not wrap."""
    assert verify("SELECT abs(a) AS x FROM t", "t", I64).errors


def test_boolean_case_is_not_lazy():
    """E4: the simplifier turns the CASE into `b <> 0 AND a / b > 1`."""
    sql = "SELECT a FROM t WHERE CASE WHEN b <> 0 THEN a / b > 1 ELSE false END"
    assert verify(sql, "t", I64, ["a >= 0"]).errors


def test_lazy_and_eager_conditionals_that_are_safe():
    """A numeric `CASE` stays lazy; `ABS` is safe above the smallest integer
    and keeps its sign."""
    sql = "SELECT CASE WHEN b <> 0 THEN a / b END AS q FROM t"
    assert verify(sql, "t", I64, ["a >= 0"]).errors == []
    assert verify("SELECT coalesce(b, a / 2) AS c FROM t", "t", I64).errors == []
    report = verify("SELECT abs(a) AS x FROM t", "t", I64, ["a > -10"], ["x >= 0"])
    assert report.proved and report.issues == []


def test_coalesce_is_eager():
    """E5: DataFusion evaluates `a / b` even where b is not NULL."""
    assert verify("SELECT coalesce(b, a / b) AS c FROM t", "t", I64, ["b IS NOT NULL"]).errors


def test_power_of_null_to_zero(con):
    """I9: `power(NULL, 0)` is 1 on DataFusion, NULL in `Rel.eval`."""
    plan = json.loads(substrait_json(con, "SELECT power(a, 0) AS p FROM pn"))
    lean = lean_rows(json.dumps(inline_tables(plan, {"pn": [(None,), (2,)]})))
    assert lean == rows(con, "SELECT power(a, 0) AS p FROM pn")


def test_zoned_timestamp_arithmetic_is_refused(con):
    """T3: a day of a zoned timestamp is 23 hours across the switch to daylight
    saving time in DataFusion; the model would add 86 400 s, so it refuses."""
    sql = "SELECT t + INTERVAL '1 day' >= t + INTERVAL '24 hours' AS ok FROM z"
    plan = json.loads(substrait_json(con, sql))
    with pytest.raises(subprocess.CalledProcessError) as e:
        lean_rows(json.dumps(inline_tables(plan, {"z": [(dt.datetime(2024, 3, 30, 12),)]})))
    assert "time zone" in str(e.value.stderr)


def test_nan_payloads_are_canonical_on_a_connection():
    """F7: DataFusion's order tells NaN payloads apart, the model has one NaN.
    A connection stores every NaN as the same one (`engine.canonical`)."""
    c = connect()
    put_table(c, "nanp", TABLES["nanp"])
    assert rows(c, "SELECT count(DISTINCT v) FROM nanp") == [(1,)]
