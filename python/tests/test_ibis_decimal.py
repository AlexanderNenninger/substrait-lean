"""Decimals in the Ibis producer (#67, #27).

Ibis types decimal arithmetic loosely (`decimal(15, 2) * decimal(15, 2)` is a
`decimal(15, 2)` to it), but its SQL computes exactly, and writes a float
constant next to a decimal as a SQL numeral, which is a decimal. The plans
follow the SQL: Lean's values agree with DuckDB running Ibis's own SQL.
"""

import json
from decimal import Decimal as D
from typing import Any

import ibis
import ibis.expr.operations as ops
import pyarrow as pa
import pytest
from ibis import _

from sverify.contracts import decode_double
from sverify.engine import connect, put_table, run_plan, written_plan
from sverify.ibis_substrait import exact, to_substrait
from sverify.testing import inline_tables, lean_values

li = ibis.table(
    {
        "k": "string",
        "price": "decimal(15, 2)",
        "disc": "decimal(15, 2)",
        "qty": "int64",
        "f": "float64",
    },
    name="li",
)

ROWS = [
    ("a", D("901.00"), D("0.05"), 3, 0.5),
    ("a", D("1234.56"), D("0.07"), 1, -1.25),
    ("b", D("0.01"), D("0.00"), 7, 2.0),
    ("b", D("-12.35"), D("0.10"), 2, 0.1),
    ("c", None, D("0.06"), 5, None),
]
TABLE = pa.table(
    {
        "k": pa.array([r[0] for r in ROWS]),
        "price": pa.array([r[1] for r in ROWS], pa.decimal128(15, 2)),
        "disc": pa.array([r[2] for r in ROWS], pa.decimal128(15, 2)),
        "qty": pa.array([r[3] for r in ROWS], pa.int64()),
        "f": pa.array([r[4] for r in ROWS], pa.float64()),
    }
)

CASES = {
    "product": lambda: li.select(x=li.price * (1 - li.disc)),
    "sum of a product": lambda: li.group_by("k").aggregate(
        s=(li.price * (1 - li.disc) * (1 + li.disc)).sum()
    ),
    "between float constants": lambda: li.filter(li.disc.between(0.05, 0.07)).select("price"),
    "float constant": lambda: li.select(x=li.price * 0.0001, y=li.price > 900.5),
    "integer column": lambda: li.select(x=li.price * li.qty, y=li.price + li.qty),
    "double column": lambda: li.select(x=li.price * li.f),
    "case": lambda: li.group_by("k").aggregate(s=(li.qty > 2).ifelse(li.price, 0).sum()),
    "coalesce": lambda: li.select(x=li.price.fill_null(0) + li.disc),
    "mean": lambda: li.group_by("k").aggregate(m=li.price.mean()),
    "divide": lambda: li.group_by("k").aggregate(r=li.price.sum() / li.disc.sum()),
    "derived column": lambda: (
        li.mutate(v=li.price * (1 - li.disc)).group_by("k").aggregate(s=_.v.sum()).filter(_.s > 0.5)
    ),
    "aggregate arithmetic": lambda: li.group_by("k").aggregate(
        spread=li.price.max() - li.price.min(), share=li.price.sum() * 0.0001
    ),
}


def number(v: object, double: bool) -> object:
    """Decimals and doubles compare as numbers, to the 6 places Lean prints
    doubles with (DuckDB's `AVG` and decimal × double are doubles). Lean
    writes small doubles as their codes."""
    if double and isinstance(v, int):
        v = decode_double(v)
    if isinstance(v, float | D):
        return round(float(v), 6)
    return v


@pytest.fixture(scope="module")
def con():
    c = connect()
    put_table(c, "li", TABLE)
    return c


@pytest.mark.parametrize("label", list(CASES))
def test_plans_mean_what_ibis_sql_means(con, label):
    expr = CASES[label]()
    duck = con.ibis.con.sql(ibis.to_sql(expr, dialect="duckdb")).to_arrow_table()
    op: Any = expr.op()
    doubles = [exact(ops.Field(op, n)).is_floating() for n in op.schema.names]

    def rows(rs: list) -> list[tuple]:
        out = [tuple(number(v, d) for v, d in zip(r, doubles, strict=True)) for r in rs]
        return sorted(out, key=repr)

    plan = inline_tables(to_substrait(expr), {"li": ROWS})
    got = rows(lean_values(json.dumps(plan)))
    assert got == rows([tuple(r.values()) for r in duck.to_pylist()])


def test_decimal_arithmetic_is_exact():
    """`price * (1 - disc)` is a decimal of scale 4 in the plan, not Ibis's
    `decimal(15, 2)`: no cast rounds it."""
    plan = json.dumps(to_substrait(li.select(x=li.price * (1 - li.disc))))
    assert '"scale": 2' in plan
    assert "cast" not in plan


# --------------------------------------------------------------------------
# DuckDB runs decimal plans as the reference computes them (#27)

ed = ibis.table({"k": "string", "x": "decimal(15, 2)", "y": "decimal(5, 4)"}, name="ed")
#: `AVG` of one ±0.01 and 31 zeros is ±0.0003125: half away from zero at
#: scale 6 is ±0.000313, where truncating or a double's rounding differ.
ED_ROWS = (
    [("h", D("0.01"), D("1.0000"))]
    + [("h", D("0.00"), D("0.0001"))] * 31
    + [("n", D("-0.01"), D("-1.0000"))]
    + [("n", D("0.00"), D("0.0000"))] * 31
    + [
        ("t", D("2.57"), D("9.9999")),
        ("t", D("-2.57"), D("-9.9999")),
        ("t", D("9999999999999.99"), D("9.9999")),
        ("t", None, None),
    ]
)
ED_TABLE = pa.table(
    {
        "k": pa.array([r[0] for r in ED_ROWS]),
        "x": pa.array([r[1] for r in ED_ROWS], pa.decimal128(15, 2)),
        "y": pa.array([r[2] for r in ED_ROWS], pa.decimal128(5, 4)),
    }
)

ENGINE_CASES = {
    **CASES,
    "avg rounds half away from zero": lambda: ed.group_by("k").aggregate(m=ed.x.mean()),
    "cast to an integer truncates": lambda: ed.filter(ed.k == "t").select(i=ed.x.cast("int64")),
    # 9999999999999.99² has 30 digits; DuckDB types the product of two
    # `DECIMAL(15, 2)`s with 18 unless it is widened.
    "a product wider than DuckDB's type": lambda: ed.select(p=ed.x * ed.x, q=ed.y * ed.y),
    "sum of squares": lambda: ed.group_by("k").aggregate(s=(ed.x * ed.x).sum()),
    "cast to a double": lambda: ed.select(f=ed.x.cast("float64"), g=(ed.x * ed.x).cast("float64")),
    "cast to a smaller scale": lambda: ed.select(r=ed.y.cast("decimal(6, 2)")),
}


@pytest.fixture(scope="module")
def con_ed(con):
    put_table(con, "ed", ED_TABLE)
    return con


@pytest.mark.parametrize("label", list(ENGINE_CASES))
def test_duckdb_runs_decimal_plans_as_the_reference(con_ed, label):
    """The written plan on DuckDB gives `Rel.eval`'s rows: decimals exactly,
    doubles as Lean prints them."""
    expr = ENGINE_CASES[label]()
    plan = to_substrait(expr)
    op: Any = expr.op()
    doubles = [exact(ops.Field(op, n)).is_floating() for n in op.schema.names]

    def rows(rs: list) -> list[tuple]:
        out = [
            tuple(number(v, True) if d else v for v, d in zip(r, doubles, strict=True)) for r in rs
        ]
        return sorted(out, key=repr)

    def duckdb(plan: dict) -> list[tuple]:
        out = run_plan(con_ed, written_plan(json.dumps(plan)), "duckdb")
        return rows([tuple(r.values()) for r in out.to_pylist()])

    on_tables = duckdb(plan)
    # The tables as `VALUES` (`inline_tables` changes the plan in place).
    inlined = inline_tables(plan, {"li": ROWS, "ed": ED_ROWS})
    lean = rows(lean_values(json.dumps(inlined)))
    assert on_tables == lean
    assert duckdb(inlined) == lean
