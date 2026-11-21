"""ST-4's equality, sort-key and grouping shims on the engines (#741, ruling 241).

The shims rewrite a double comparison, key or sort field with `is_nan`; `to_substrait()`
writes them and `Report.from_substrait` reads the plan back. The table below holds the eight
values that decide every case (a comparison depends only on how the classes of its operands
compare): NULL, NaN, both infinities, both zeros, 1.0 and -1.0. Each test runs the exported
plan on DuckDB and Polars and compares it with the reference's value, under three-valued
logic: a NULL operand makes an equality NULL, whatever the other side is.
"""

from __future__ import annotations

import itertools
import json
import math
from typing import Any

import ibis
import pyarrow as pa
import pytest

import sverify as sv
from sverify.engine import connect, put_table
from sverify.substrait_export import read

INF = math.inf
VALUES: list[float | None] = [None, math.nan, INF, -INF, 0.0, -0.0, 1.0, -1.0]
PAIRS = list(itertools.product(VALUES, VALUES))

ENGINES = ["duckdb", "polars"]


def _is_nan(v: float | None) -> bool:
    return v is not None and v != v


def _same(x: float | None, y: float | None) -> bool | None:
    """The reference's `=` on doubles: NaN equals NaN, the zeros are one, NULL is unknown."""
    if x is None or y is None:
        return None
    return (_is_nan(x) and _is_nan(y)) or x == y


def _con(name: str, table: pa.Table):
    con = connect()
    put_table(con, name, table)
    return con


def _canon(v: Any) -> Any:
    """A comparable key for a value of the result: NaN equal to itself, one zero."""
    if v is None:
        return ("null",)
    if v != v:
        return ("nan",)
    return ("num", v + 0.0)


def _exported(expr: ibis.Table) -> sv.Report:
    report = sv.verify(expr)
    assert report.verdict in (sv.Verdict.PROVED, sv.Verdict.PROVED_WITH_CHECKS), str(report)
    assert "is_nan" in json.dumps(read(report.to_substrait()).plan)  # the shim is in the plan
    return sv.Report.from_substrait(report.to_substrait())


def _ref_pairs() -> tuple[ibis.Table, pa.Table]:
    t = ibis.table({"i": "int64", "a": "float64", "b": "float64"}, name="p")
    data = pa.table(
        {
            "i": pa.array(range(len(PAIRS)), pa.int64()),
            "a": pa.array([a for a, _ in PAIRS], pa.float64()),
            "b": pa.array([b for _, b in PAIRS], pa.float64()),
        }
    )
    return t, data


@pytest.mark.parametrize("engine", ENGINES)
def test_equality_over_the_eight_values(engine: str) -> None:
    """All 64 pairs: `=` and `<>` through the export, NULL when a side is NULL."""
    t, data = _ref_pairs()
    out = _exported(t.select("i", eq=t.a == t.b, ne=t.a != t.b)).run(_con("p", data), engine)
    rows = {r["i"]: (r["eq"], r["ne"]) for r in out.to_pylist()}
    assert len(rows) == len(PAIRS)
    for i, (x, y) in enumerate(PAIRS):
        want = _same(x, y)
        assert rows[i] == (want, None if want is None else not want), (x, y)


@pytest.mark.parametrize("engine", ENGINES)
def test_a_join_on_doubles_matches_like_equality(engine: str) -> None:
    """A join key is an equality: NaN joins NaN, the zeros join, NULL joins nothing."""
    left = ibis.table({"i": "int64", "a": "float64"}, name="l")
    right = ibis.table({"j": "int64", "b": "float64"}, name="r")
    con = connect()
    put_table(
        con,
        "l",
        pa.table({"i": pa.array(range(8), pa.int64()), "a": pa.array(VALUES, pa.float64())}),
    )
    put_table(
        con,
        "r",
        pa.table({"j": pa.array(range(8), pa.int64()), "b": pa.array(VALUES, pa.float64())}),
    )
    expr = left.join(right, left.a == right.b).select("i", "j")
    out = _exported(expr).run(con, engine)
    got = sorted((r["i"], r["j"]) for r in out.to_pylist())
    want = sorted(
        (i, j) for i, x in enumerate(VALUES) for j, y in enumerate(VALUES) if _same(x, y) is True
    )
    assert got == want


@pytest.mark.parametrize("engine", ENGINES)
def test_grouping_over_the_eight_values(engine: str) -> None:
    """NULL, NaN and the zeros are one group each; the key keeps its class."""
    t = ibis.table({"a": "float64", "n": "int64"}, name="g")
    values = VALUES * 2  # every class twice, so a split group shows
    data = pa.table(
        {"a": pa.array(values, pa.float64()), "n": pa.array(range(len(values)), pa.int64())}
    )
    out = _exported(t.group_by("a").aggregate(c=t.n.count())).run(_con("g", data), engine)
    got = {_canon(r["a"]): r["c"] for r in out.to_pylist()}
    assert len(out) == len(got) == 7  # NULL, NaN, -inf, inf, 0, 1, -1
    assert got == {
        ("null",): 2,
        ("nan",): 2,
        ("num", INF): 2,
        ("num", -INF): 2,
        ("num", 0.0): 4,  # +0.0 and -0.0
        ("num", 1.0): 2,
        ("num", -1.0): 2,
    }
    zero = [r["a"] for r in out.to_pylist() if r["a"] == 0.0]
    assert len(zero) == 1


@pytest.mark.parametrize("engine", ENGINES)
def test_sorting_over_the_eight_values(engine: str) -> None:
    """NaN sorts greatest, the zeros tie, NULL keeps the position the reference gives it."""
    t = ibis.table({"i": "int64", "a": "float64"}, name="s")
    data = pa.table({"i": pa.array(range(8), pa.int64()), "a": pa.array(VALUES, pa.float64())})
    expr = t.order_by(["a", "i"]).select("i", "a")
    report = sv.verify(expr)
    assert report.verdict in (sv.Verdict.PROVED, sv.Verdict.PROVED_WITH_CHECKS), str(report)
    want = [r["i"] for r in report.run(_con("s", data), engine).to_pylist()]
    out = sv.Report.from_substrait(report.to_substrait()).run(_con("s", data), engine)
    got = [r["i"] for r in out.to_pylist()]
    assert got == want
    by_class = [_canon(VALUES[i]) for i in got]
    nonnull = [c for c in by_class if c != ("null",)]
    assert nonnull == [
        ("num", -INF),
        ("num", -1.0),
        ("num", 0.0),
        ("num", 0.0),
        ("num", 1.0),
        ("num", INF),
        ("nan",),
    ]
    assert got[-1 if by_class[-1] == ("null",) else 0] == 0  # NULL (i = 0) first or last
