"""Elementary functions of doubles and bitwise operations of integers.

Lean computes `SQRT`, `LN`, `SIN`, … with native floats (C's `libm`) and the
bitwise operations in 64-bit two's complement (`BitOp`). On edge values
(±0, ±inf, NaN, subnormals, arguments outside a function's domain, shift
counts outside 0–63, the extreme integers) Lean's values agree exactly with
DataFusion running Ibis's own SQL (to the six decimals Lean prints), and the
Polars and DuckDB engines running the plan Lean writes back agree with
DataFusion bit for bit.
"""

import itertools
import json
import math
from typing import Any

import ibis
import pyarrow as pa
import pytest

from sverify.contracts import decode_double
from sverify.engine import connect, create_table, run_plan, run_sql, to_sql, written_plan
from sverify.ibis_substrait import to_substrait
from sverify.testing import inline_tables, lean_values

X = ibis.table(
    {"k": "int64", "x": "float64", "y": "float64", "i": "int64", "j": "int64", "b": "boolean"},
    name="x",
)
x = X

inf, nan = math.inf, math.nan
DOUBLES = [0.0, 0.5, -0.5, 1.0, -1.0, 2.0, -1.5, 3.0, 1e-310, 1e300, -1e300, inf, -inf, nan, None]
INTS = [0, 1, -1, -3, 7, 63, 64, 70, -65, -(2**63), 2**63 - 1, None]


def rows() -> list[tuple]:
    """Every pair of integers, with the doubles cycling past them."""
    pairs = list(itertools.product(INTS, INTS))
    n = len(DOUBLES)
    return [
        (k, DOUBLES[k % n], DOUBLES[(7 * k + 3) % n], i, j, [True, False, None][k % 3])
        for k, (i, j) in enumerate(pairs)
    ]


EXPRS: dict[str, Any] = {
    "sqrt, exp, ln": lambda: X.select(x.k, a=x.x.sqrt(), b=x.x.exp(), c=x.x.ln()),
    "log10, log2, log(b)": lambda: X.select(x.k, a=x.x.log10(), b=x.x.log2(), c=x.x.log(x.y)),
    "sin, cos, tan, cot": lambda: X.select(x.k, a=x.x.sin(), b=x.x.cos(), c=x.x.tan(), d=x.x.cot()),
    "asin, acos, atan, atan2": lambda: X.select(
        x.k, a=x.x.asin(), b=x.x.acos(), c=x.x.atan(), d=x.x.atan2(x.y)
    ),
    "degrees, radians, pi, e": lambda: X.select(
        x.k, a=x.x.degrees(), b=x.x.radians(), c=x.x * ibis.pi, d=x.x + ibis.e
    ),
    "sign, isinf": lambda: X.select(x.k, a=x.x.sign(), b=x.i.sign(), c=x.x.isinf()),
    "of integers": lambda: X.select(x.k, a=x.i.sqrt(), b=x.i.ln(), c=x.i.exp()),
    "and, or, xor, not": lambda: X.select(x.k, a=x.i & x.j, b=x.i | x.j, c=x.i ^ x.j, d=~x.i),
    "shifts": lambda: X.select(x.k, a=x.i << x.j, b=x.i >> x.j),
    "logical xor": lambda: X.select(x.k, a=x.b ^ (x.i > 0)),
}


def normalize(v: object, t: Any, lean: bool) -> object:
    """Lean writes doubles as codes or decimals; NaN as a string so it equals
    itself. Ibis types `SIGN` of an integer as an integer, DataFusion
    returns a double."""
    if v is None:
        return None
    if t.is_floating():
        f = decode_double(v) if lean and isinstance(v, int) else float(v)  # type: ignore[arg-type]
        return "nan" if math.isnan(f) else f + 0.0
    if t.is_integer() and isinstance(v, float):
        return int(v)
    return v


def table_rows(expr: Any, rs: list[tuple], lean: bool) -> list[tuple]:
    """In the order of the key `k`: DataFusion may return rows in any order."""
    types = list(expr.schema().types)
    out = [tuple(normalize(v, t, lean) for v, t in zip(r, types, strict=True)) for r in rs]
    return sorted(out, key=lambda r: r[0])


def close(printed: object, exact: object) -> bool:
    """Lean prints doubles with six decimals."""
    if isinstance(printed, float) and isinstance(exact, float):
        return math.isclose(printed, exact, rel_tol=1e-6, abs_tol=1e-6)
    return printed == exact


@pytest.fixture(scope="module")
def con():
    con = connect()
    create_table(con, "x", X.schema(), rows())
    return con


@pytest.mark.parametrize("label", EXPRS)
def test_lean_agrees_with_datafusion_and_engines(con, label):
    expr = EXPRS[label]()
    out = run_sql(con, to_sql(expr))
    expected = table_rows(expr, [tuple(r.values()) for r in out.to_pylist()], lean=False)
    lean = lean_values(json.dumps(inline_tables(to_substrait(expr), {"x": rows()})))
    got = table_rows(expr, lean, lean=True)
    assert len(got) == len(expected)
    for g, e in zip(got, expected, strict=True):
        assert all(close(a, b) for a, b in zip(g, e, strict=True)), (g, e)
    written = written_plan(json.dumps(to_substrait(expr)))
    for engine in ("polars", "duckdb"):
        got = run_plan(con, written, engine)
        assert table_rows(expr, [tuple(r.values()) for r in got.to_pylist()], False) == expected


def test_shifts_wrap_as_datafusion_does():
    """DataFusion shifts by the count modulo 64, wrapping (Rust's
    `wrapping_shl`); DuckDB raises instead, so the SQL avoids its `<<`."""
    con = connect()
    rs = [(0, None, None, -3, 70, None), (1, None, None, 2**62, 1, None)]
    create_table(con, "x", X.schema(), rs)
    expr = X.select(x.k, a=x.i << x.j, b=x.i >> x.j)
    want = [(0, -192, -1), (1, -(2**63), 2**61)]
    assert sorted(tuple(r.values()) for r in run_sql(con, to_sql(expr)).to_pylist()) == want
    got = run_plan(con, written_plan(json.dumps(to_substrait(expr))), "duckdb")
    assert sorted(tuple(r.values()) for r in got.to_pylist()) == want


def test_rows_cover_the_edges():
    t = pa.table({"i": [r[3] for r in rows()]})
    assert t.num_rows == len(INTS) ** 2
