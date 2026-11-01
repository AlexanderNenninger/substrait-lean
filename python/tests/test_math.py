"""Elementary functions of doubles and bitwise operations of integers
(`SubstraitLean/Numeric.lean`).

Lean computes `SQRT`, `LN`, `SIN`, … with native floats (C's `libm`) and the
bitwise operations in 64-bit two's complement. Inside each function's domain,
on edge values (±0, ±inf, NaN, subnormals, huge values, the extreme integers),
Lean agrees with DataFusion running Ibis's own SQL (to the six decimals Lean
prints), and Polars and DuckDB, running the plan Lean writes back, agree with
DataFusion bit for bit.

Outside a domain (`sqrt` of a negative, `ln 0`, `asin 2`, `atan2(0, 0)`, a
shift by 64) the reference raises (Substrait's `on_domain_error` = ERROR):
the checker reports a domain error, and Polars and DuckDB raise. DataFusion
returns NaN, -inf or a wrapped shift there instead, which an error allows.
"""

import json
import math
from typing import Any, cast

import duckdb
import ibis
import pytest

import sverify as sv
from sverify import polars_engine
from sverify.contracts import decode_double
from sverify.engine import connect, create_table, run_plan, run_sql, to_sql, written_plan
from sverify.ibis_substrait import to_substrait, to_substrait_json
from sverify.testing import inline_tables, lean_values

X = ibis.table(
    {
        "k": "int64",
        "x": "float64",
        "p": "float64",
        "u": "float64",
        "i": "int64",
        "j": "int64",
        "n": "int64",
        "b": "boolean",
    },
    name="x",
)
x = X

inf, nan = math.inf, math.nan
#: Any double, positive ones (the logarithms' domain, and NaN), ones in
#: [-1, 1] (`asin`, `acos`), any integer and shift counts.
DOUBLES = [0.0, 0.5, -0.5, 1.0, -1.0, 2.0, -1.5, 3.0, 1e-310, 1e300, -1e300, inf, -inf, nan, None]
POSITIVE = [0.5, 1.0, 2.0, 3.0, 1e-310, 1e300, inf, nan, None, 7.25]
UNIT = [0.0, 0.5, -0.5, 1.0, -1.0, 1e-310, -0.75, nan, None]
INTS = [0, 1, -1, -3, 7, 63, 64, 70, -65, -(2**63), 2**63 - 1, None]
COUNTS = [0, 1, 3, 62, 63, None]


def rows() -> list[tuple]:
    """Every pair of integers, with the other columns cycling past them."""
    pairs = [(i, j) for i in INTS for j in INTS]

    def at(vs: list, k: int, step: int = 1) -> Any:
        return vs[(step * k) % len(vs)]

    return [
        (k, at(DOUBLES, k), at(POSITIVE, k, 3), at(UNIT, k, 5), i, j, at(COUNTS, k, 7),
         [True, False, None][k % 3])
        for k, (i, j) in enumerate(pairs)
    ]  # fmt: skip


#: Inside each function's domain.
EXPRS: dict[str, Any] = {
    "sqrt, exp, ln": lambda: X.select(x.k, a=x.p.sqrt(), b=x.x.exp(), c=x.p.ln()),
    "log(b)": lambda: X.select(x.k, b=x.p.log(3), c=x.p.log(x.p + 2)),
    "sin, cos, tan, cot": lambda: X.select(x.k, a=x.x.sin(), b=x.x.cos(), c=x.x.tan(), d=x.x.cot()),
    "asin, acos, atan, atan2": lambda: X.select(
        x.k, a=x.u.asin(), b=x.u.acos(), c=x.x.atan(), d=x.x.atan2(x.p)
    ),
    "degrees, radians, pi, e": lambda: X.select(
        x.k, a=x.x.degrees(), b=x.x.radians(), c=x.x * ibis.pi, d=x.x + ibis.e
    ),
    "sign, isinf": lambda: X.select(x.k, a=x.x.sign(), b=x.i.sign(), c=x.x.isinf()),
    "of integers": lambda: X.select(x.k, a=x.n.sqrt(), b=x.i.exp(), c=(x.n + 1).ln()),
    "and, or, xor, not": lambda: X.select(x.k, a=x.i & x.j, b=x.i | x.j, c=x.i ^ x.j, d=~x.i),
    "shifts": lambda: X.select(x.k, a=x.i << x.n, b=x.i >> x.n),
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
    return sorted(out, key=lambda r: cast(int, r[0]))


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
    written = written_plan(to_substrait_json(expr))
    for engine in ("polars", "duckdb"):
        ran = run_plan(con, written, engine)
        assert table_rows(expr, [tuple(r.values()) for r in ran.to_pylist()], False) == expected


def test_log10_and_log2_are_libm():
    """Ibis writes `LOG(x)` and `LOG(2, x)` for DataFusion, which are
    `ln x / ln b`, not libm's `log10` and `log2` (the last bit differs); Lean
    and the engines compute `log10` and `log2`, as DataFusion's own do."""
    con = connect()
    ps = [*POSITIVE, 3.0, 5.5, 1e-5]
    rs = [(k, None, p, None, None, None, None, None) for k, p in enumerate(ps)]
    create_table(con, "x", X.schema(), rs)
    expr = X.select(x.k, a=x.p.log10(), b=x.p.log2())

    def libm(f: Any, p: float | None) -> object:
        return normalize(None if p is None else f(p), expr.a.type(), False)

    want = [(k, libm(math.log10, p), libm(math.log2, p)) for k, p in enumerate(ps)]
    lean = lean_values(json.dumps(inline_tables(to_substrait(expr), {"x": rs})))
    for g, e in zip(table_rows(expr, lean, lean=True), want, strict=True):
        assert all(close(a, b) for a, b in zip(g, e, strict=True)), (g, e)
    written = written_plan(to_substrait_json(expr))
    for engine in ("polars", "duckdb", "datafusion"):
        ran = run_plan(con, written, engine)
        assert table_rows(expr, [tuple(r.values()) for r in ran.to_pylist()], False) == want


#: An expression outside its domain on some row, and that row's `x`, `i`, `n`.
OUTSIDE = [
    ("sqrt", lambda: X.select(a=x.x.sqrt()), (-1.0, 0, 0)),
    ("ln of 0", lambda: X.select(a=x.x.ln()), (0.0, 0, 0)),
    ("ln of -inf", lambda: X.select(a=x.x.ln()), (-inf, 0, 0)),
    ("log10", lambda: X.select(a=x.x.log10()), (-2.0, 0, 0)),
    ("log2", lambda: X.select(a=x.x.log2()), (0.0, 0, 0)),
    ("log base 1", lambda: X.select(a=x.p.log(x.x)), (1.0, 0, 0)),
    ("asin", lambda: X.select(a=x.x.asin()), (1.5, 0, 0)),
    ("acos", lambda: X.select(a=x.x.acos()), (inf, 0, 0)),
    ("atan2(0, 0)", lambda: X.select(a=x.x.atan2(x.x)), (0.0, 0, 0)),
    ("shift by 64", lambda: X.select(a=x.i << x.n), (0.0, 5, 64)),
    ("shift by -1", lambda: X.select(a=x.i >> x.n), (0.0, 5, -1)),
]


@pytest.mark.parametrize(("label", "build", "row"), OUTSIDE, ids=[o[0] for o in OUTSIDE])
def test_domain_errors_raise(label, build, row):
    """The checker reports the domain error, the engines raise on the row,
    and DataFusion (whose IEEE result or wrapped shift an error allows) runs."""
    expr = build()
    assert [i.kind for i in sv.verify(expr).errors] == ["domain error"], label
    con = connect()
    xv, iv, nv = row
    create_table(con, "x", X.schema(), [(0, xv, 2.0, None, iv, None, nv, None)])
    written = written_plan(to_substrait_json(expr))
    with pytest.raises(polars_engine.DomainError):
        run_plan(con, written, "polars")
    with pytest.raises(duckdb.Error, match="sverify: domain error"):
        run_plan(con, written, "duckdb")
    run_sql(con, to_sql(expr))


@pytest.mark.parametrize(
    ("label", "expr"),
    [
        ("filter x > 0", X.filter(x.x > 0).select(a=x.x.ln(), b=x.x.sqrt())),
        ("case guard", X.select(a=ibis.cases((x.x >= 0, x.x.sqrt()), else_=0.0))),
        ("bounded asin", X.filter(x.x.between(-1, 1)).select(a=x.x.asin(), b=x.x.acos())),
        ("atan2 off 0", X.filter(x.p > 0).select(a=x.x.atan2(x.p))),
        ("log base 2", X.filter((x.p > 1) & (x.x > 0)).select(a=x.x.log(x.p))),
        ("bounded shift", X.filter(x.n.between(0, 63)).select(a=x.i << x.n, b=x.i >> x.n)),
        ("constant shift", X.select(a=x.i << 3)),
    ],
)
def test_guards_rule_out_domain_errors(label, expr):
    assert not sv.verify(expr).errors, label


def test_out_of_domain_is_null_in_lean():
    expr = X.select(x.k, a=x.x.sqrt(), b=x.i << x.n)
    rs = [(0, -4.0, None, None, 1, None, 64, None), (1, 4.0, None, None, 1, None, 63, None)]
    lean = lean_values(json.dumps(inline_tables(to_substrait(expr), {"x": rs})))
    got = table_rows(expr, lean, lean=True)
    assert got == [(0, None, None), (1, 2.0, -(2**63))]
