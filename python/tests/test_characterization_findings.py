"""The engine behaviour the characterization's facts and upstream bugs record
(`characterization/<engine>/facts/`, `upstream/bugs/`), each pinned by a tiny
query at the engine version the fact names: DuckDB 2.0.0, Polars 2.1.0.

These tests pin the engine, not sverify. When DuckDB or Polars is upgraded and
one fails, the engine changed: re-probe the fact it names
(`python -m sverify_dev.probe --observations`, `python -m
sverify_dev.probe_polars --diff`), and record the new behaviour in a fact that
`supersedes` the old one, or close the upstream bug. Every frame here has a
few rows."""

import ast
import math
import os
import subprocess
import sys
from decimal import Decimal

import duckdb
import polars as pl
import pytest

from sverify_dev.probe_polars import SMALL

duckdb_only = pytest.mark.backend("duckdb")
polars_only = pytest.mark.backend("polars")
ENGINES = ("in-memory", "streaming")


def _polars(code: str, **env: str) -> object:
    """The value of a Python expression over `pl`, in a fresh interpreter with
    `env` set: Polars reads its thread count and morsel size at start-up."""
    run = subprocess.run(
        [sys.executable, "-c", f"import polars as pl; print(repr({code}))"],
        env={**os.environ, **env},
        capture_output=True,
        text=True,
        check=True,
    )
    return ast.literal_eval(run.stdout.strip())


#: One thread: the streaming engine's morsels and their merge order are then
#: the same on every run.
ONE_THREAD = {"POLARS_MAX_THREADS": "1"}


def _duck(sql: str, *setup: str) -> list[tuple]:
    con = duckdb.connect()
    for s in setup:
        con.sql(s)
    return con.sql(sql).fetchall()


# DuckDB


@duckdb_only
def test_dd7_constant_case_when_raises_while_planning():
    """DD-7, duckdb-exec-short-circuit: a constant `WHEN` that raises is folded
    while planning, so it raises on an empty table, where no row reaches it."""
    sql = "SELECT CASE WHEN x > 0 THEN 1 WHEN 1 // 0 = 1 THEN 2 END FROM t"
    with pytest.raises(duckdb.InvalidInputException, match="Division by zero"):
        _duck(sql, "CREATE TABLE t (x INTEGER)")
    with pytest.raises(duckdb.ConversionException, match="Could not convert string 'a'"):
        _duck(sql.replace("1 // 0 = 1", "'a'::INTEGER = 1"), "CREATE TABLE t AS SELECT 1 x")


@duckdb_only
def test_case_else_is_lazy_at_run_time():
    """duckdb-exec-short-circuit: at run time `CASE` evaluates only the branch
    a row takes."""
    assert _duck("SELECT CASE WHEN x > 0 THEN 1 ELSE 1 // 0 END FROM (VALUES (1)) t(x)") == [(1,)]


@duckdb_only
def test_and_in_aggregate_filter_is_eager():
    """duckdb-exec-short-circuit (#604): `AND` in an aggregate's `FILTER`
    evaluates both operands on every row, where a `WHERE` does not."""
    rows = "(VALUES (0), (5)) t(x)"
    cond = "(x <> 0) AND (10 // x > 1)"
    with pytest.raises(duckdb.InvalidInputException, match="Division by zero"):
        _duck(f"SELECT count(*) FILTER (WHERE {cond}) FROM {rows}")
    assert _duck(f"SELECT count(*) FROM {rows} WHERE {cond}") == [(1,)]


@duckdb_only
def test_dd6_float_least_drops_the_zero_sign():
    """DD-6, duckdb-float-signs: `least` on FLOAT decodes the winner from its
    sort key, so `-0.0` comes out as `+0.0`; on DOUBLE it keeps the sign."""
    found = _duck(
        "SELECT signbit(least(-0.0::FLOAT, -0.0::FLOAT)),"
        " signbit(least(-0.0::DOUBLE, -0.0::DOUBLE))"
    )
    assert found == [(False, True)]


@duckdb_only
@pytest.mark.parametrize("ty", ["DOUBLE", "FLOAT"])
@pytest.mark.parametrize("first", ["-0.0", "0.0"])
def test_r14_order_by_keeps_the_zeros_in_input_order(ty, first):
    """duckdb-R14: `ORDER BY` sorts `-0.0` and `0.0` as peers, each sign kept,
    so the input order decides."""
    second = "0.0" if first == "-0.0" else "-0.0"
    values = [first, second, first]
    rows = ", ".join(f"({v}::{ty})" for v in values)
    assert _duck(f"SELECT v::VARCHAR FROM (VALUES {rows}) t(v) ORDER BY v") == [
        (v,) for v in values
    ]


@duckdb_only
def test_r9_double_to_int_rounds_half_to_even_and_decimal_half_away():
    """duckdb-R9: a DOUBLE casts to an integer half to even, a DECIMAL half
    away from zero."""
    found = _duck(
        "SELECT CAST(2.5::DOUBLE AS INTEGER), CAST(3.5::DOUBLE AS INTEGER),"
        " CAST(-2.5::DOUBLE AS INTEGER), CAST(2.5 AS INTEGER), CAST(-2.5 AS INTEGER)"
    )
    assert found == [(2, 4, -2, 3, -3)]


@duckdb_only
def test_sum_and_avg_of_no_rows_are_null():
    """probes.json `sum-empty` (duckdb-sum-double): `sum` and `avg` of no rows
    are NULL for DOUBLE, FLOAT and integers, and so is `sum` of a NULL."""
    found = _duck(
        "SELECT sum(d), avg(d), sum(f), avg(f), sum(i), avg(i),"
        " (SELECT sum(d) FROM (VALUES (NULL::DOUBLE)) n(d))"
        " FROM (SELECT 1.0::DOUBLE AS d, 1.0::FLOAT AS f, 1::TINYINT AS i WHERE false) t"
    )
    assert found == [(None,) * 7]


@duckdb_only
def test_dd8_double_modulus_by_zero_is_nan():
    """DD-8, duckdb-R15-double-modulus: `%` by zero on DOUBLE and FLOAT is NaN,
    from constants and from columns, where on integers it raises."""
    (row,) = _duck(
        "SELECT 1.0::DOUBLE % 0.0::DOUBLE, x % y, 1::FLOAT % 0::FLOAT"
        " FROM (VALUES (1.0::DOUBLE, 0.0::DOUBLE)) t(x, y)"
    )
    assert all(math.isnan(v) for v in row)
    with pytest.raises(duckdb.InvalidInputException, match="Division by zero"):
        _duck("SELECT x % y FROM (VALUES (1, 0)) t(x, y)")


# Polars


PL3 = "pl.LazyFrame({'x': [49.0] * %d}).select(m=pl.col('x') %% 49.0, f=pl.col('x') // 49.0,"
PL3 += " d=pl.col('x') / 49.0).collect(engine=%r).unique().rows()"
RECIPROCAL, IEEE = (49.0, 0.0, 0.9999999999999999), (0.0, 1.0, 1.0)


@polars_only
def test_pl3_scalar_divisor_multiplies_by_the_reciprocal():
    """PL-3, polars-double-scalar-divisor: a literal divisor on a column of
    more than one row is applied as a multiplication by its reciprocal, so
    `49.0 % 49.0` is 49.0; on a column of one row the IEEE kernel gives 0.0."""
    assert _polars(PL3 % (64, "in-memory")) == [RECIPROCAL]
    assert _polars(PL3 % (1, "in-memory")) == [IEEE]
    # On one thread the streaming engine keeps the 64 rows in one morsel.
    assert _polars(PL3 % (64, "streaming"), **ONE_THREAD) == [RECIPROCAL]
    assert _polars(PL3 % (1, "streaming"), **ONE_THREAD) == [IEEE]
    # Several morsels of 64 rows each take the reciprocal too.
    assert _polars(PL3 % (256, "streaming"), **ONE_THREAD, **SMALL) == [RECIPROCAL]
    # On several threads a morsel may hold one row, which takes the IEEE
    # kernel: on Polars 2.1.0 (macOS arm64, 10 threads) every row of a column
    # of 2 or 3, and the last of 64.
    rows = _polars(PL3 % (64, "streaming"))
    assert isinstance(rows, list) and set(rows) <= {RECIPROCAL, IEEE}


@polars_only
def test_pl5_streaming_cov_of_a_decimal_raises():
    """PL-5, polars-cov: `cov` and `corr` of Decimal columns raise on the
    streaming engine and cast to Float64 on the in-memory one."""
    ty = pl.Decimal(10, 2)
    frame = pl.LazyFrame(
        {
            "a": [Decimal("1.10"), Decimal("2.20"), Decimal("3.35")],
            "b": [Decimal("1.00"), Decimal("2.00"), Decimal("4.00")],
        },
        schema={"a": ty, "b": ty},
    )
    q = frame.select(pl.cov("a", "b"), pl.corr("a", "b").alias("c"))
    cov, corr = q.collect(engine="in-memory").row(0)
    assert cov == pytest.approx(1.6916666666666667) and corr == pytest.approx(0.9843241382880894)
    for fn in (pl.cov, pl.corr):
        with pytest.raises(pl.exceptions.InvalidOperationError, match="not supported for dtype"):
            frame.select(fn("a", "b")).collect(engine="streaming")


@polars_only
@pytest.mark.parametrize("mode", ENGINES)
def test_pl6_cse_hoists_a_masked_cast(mode):
    """PL-6, polars-exec-cse-hoist: common-subexpression elimination hoists a
    strict cast two `when/then` branches share out of their mask, so it raises
    on the row the condition excludes; without CSE the branch masks it."""
    q = pl.LazyFrame({"x": ["1", "a"]}).select(
        pl.when(pl.col("x") == "1").then(pl.col("x").cast(pl.Int64) + 1).alias("a"),
        pl.when(pl.col("x") == "1").then(pl.col("x").cast(pl.Int64) + 2).alias("b"),
    )
    with pytest.raises(pl.exceptions.InvalidOperationError, match="conversion from `str`"):
        q.collect(engine=mode, optimizations=pl.QueryOptFlags(comm_subexpr_elim=True))
    off = q.collect(engine=mode, optimizations=pl.QueryOptFlags(comm_subexpr_elim=False))
    assert off.rows() == [(2, 3), (None, None)]


@polars_only
def test_grouped_float_sum_differs_between_engines():
    """polars-sum-float-streaming (probes-streaming.json `s-group-fsum-cancel`):
    a grouped sum of [1e16, 1, 1, -1e16] is 2.0 in memory (Kahan) and 0.0 on
    streaming on one thread, which adds each value in turn. On several
    threads each row may be a morsel of its own, and the partial sums merge
    in the order the threads finish: 0.0, 1.0 or 2.0 from run to run."""
    code = (
        "pl.LazyFrame({'g': [1] * 4, 'x': [1e16, 1.0, 1.0, -1e16]}).group_by('g')"
        ".agg(pl.col('x').sum()).collect(engine=%r).item(0, 'x')"
    )
    assert _polars(code % "in-memory") == 2.0
    assert _polars(code % "streaming", **ONE_THREAD) == 0.0
    q = (
        pl.LazyFrame({"g": [1] * 4, "x": [1e16, 1.0, 1.0, -1e16]})
        .group_by("g")
        .agg(pl.col("x").sum())
    )
    assert {q.collect(engine="streaming").item(0, "x") for _ in range(5)} <= {0.0, 1.0, 2.0}
