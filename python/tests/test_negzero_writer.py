"""The SQL writers print raw doubles (D31, #1461): `-0.0` reaches `atan2`, IEEE
division and the results as the reference has it, and a key is canonicalised
only where the engine's own boundary says so.

The model is the checker on the plan with the rows inlined; the written SQL
is `to_sql(written_plan(...), "duckdb")` run on a DuckDB table; both are read
by the sign of their zeros (`math.copysign`)."""

from __future__ import annotations

import json
import math
from typing import Any

import duckdb
import ibis
import pytest
from ibis import _

from sverify._lean_eval import inline_tables, lean_values
from sverify.engine import written_plan
from sverify.ibis_substrait import to_substrait
from sverify.sql.core._base import to_sql

SCHEMA = ibis.schema({"k": "int64", "x": "float64"})
T = ibis.table(SCHEMA, name="t")
X = T.x
NEG_ZERO = -0.0


def signed(v: float | None) -> Any:
    """A double with the sign of a zero: `-0.0` and `+0.0` differ."""
    if v is None or isinstance(v, bool | int):
        return v
    if math.isnan(v):
        return "nan"
    # The model prints six digits.
    return (v, math.copysign(1.0, v)) if v == 0 else round(v, 6)


def on_duckdb(sql: str, rows: list[tuple[int, float]]) -> list[tuple[int, Any]]:
    db = duckdb.connect()
    db.execute("CREATE TABLE t(k BIGINT, x DOUBLE)")
    db.executemany("INSERT INTO t VALUES (?, ?)", rows)
    return sorted((k, signed(v)) for k, v in db.execute(sql).fetchall())


def written(expr, rows) -> list[tuple[int, Any]]:
    """The written plan's result on DuckDB."""
    return on_duckdb(to_sql(written_plan(json.dumps(to_substrait(expr))), "duckdb"), rows)


def model(expr, rows) -> list[tuple[int, Any]]:
    plan = inline_tables(to_substrait(expr), {"t": rows})
    return sorted((k, signed(v)) for k, v in lean_values(json.dumps(plan)))


# A computed `-0.0`: `x * -1.0` of `0.0`, which IEEE gives and the model keeps.
COMPUTED = {
    "x * -1.0": T.select(T.k, v=X * -1.0),
    "-x": T.select(T.k, v=-X),
    "atan2(x * -1.0, -1.0)": T.select(T.k, v=(X * -1.0).atan2(-1.0)),
    "atan2(-x, -1.0)": T.select(T.k, v=(-X).atan2(-1.0)),
    "abs(x * -1.0)": T.select(T.k, v=(X * -1.0).abs()),
    "floor(x * -1.0)": T.select(T.k, v=(X * -1.0).floor().cast("float64")),
    "x * -1.0 + 0.0": T.select(T.k, v=X * -1.0 + 0.0),
}


@pytest.mark.parametrize("label", COMPUTED)
def test_a_computed_zero_is_the_models_on_the_written_plan(label: str) -> None:
    rows = [(0, 0.0), (1, 2.0), (2, -3.0)]
    assert written(COMPUTED[label], rows) == model(COMPUTED[label], rows), label


def test_atan2_of_a_negative_zero_is_minus_pi_in_the_model_and_on_duckdb() -> None:
    """The soundness witness of #1461: `atan2(x * -1.0, -1.0) < 0` at `x = 0`
    holds in the model, and on the plan the writer prints (the contract
    analysis bounds `atan2` by `[-π, π]` only, so `verify` can't prove it)."""
    expr = T.select(T.k, v=(X * -1.0).atan2(-1.0))
    rows = [(0, 0.0), (1, 0.0)]
    want = [(0, -round(math.pi, 6)), (1, -round(math.pi, 6))]
    assert model(expr, rows) == written(expr, rows) == want
    assert all(v < 0 for _, v in written(expr, rows))


@pytest.mark.parametrize(
    ("label", "expr", "want"),
    [
        ("ln(-0.0)", lambda x: x.ln(), "domain"),
        ("log10(-0.0)", lambda x: x.log10(), "domain"),
        ("atan2(-0.0, 0.0)", lambda x: x.atan2(0.0), "domain"),
        ("1.0 / -0.0", lambda x: 1.0 / x, "division"),
        ("1.0 % -0.0", lambda x: 1.0 % x, "division"),
    ],
)
def test_the_guards_still_raise_on_a_negative_zero(label: str, expr, want: str) -> None:
    """The guards compare with `= 0`, which holds for `-0.0` too."""
    t = T.select(T.k, v=expr(X * -1.0))
    sql = to_sql(written_plan(json.dumps(to_substrait(t))), "duckdb")
    with pytest.raises(duckdb.Error):
        on_duckdb(sql, [(0, 0.0)])


def test_round_and_ceil_print_the_proved_template() -> None:
    """`round(x)` of a negative value that rounds to zero is the reference's
    `+0.0`, and of `-0.0` itself `-0.0` (`FloatCode.round_negZero`)."""
    rows = [(0, -0.4), (1, NEG_ZERO), (2, 0.0), (3, 2.5), (4, -2.5)]
    for expr in (
        T.select(T.k, v=X.round()),
        T.select(T.k, v=X.ceil().cast("float64")),
        T.select(T.k, v=X.round(2)),
    ):
        assert written(expr, rows) == model(expr, rows)
    sql = to_sql(written_plan(json.dumps(to_substrait(T.select(T.k, v=X.round())))), "duckdb")
    assert "CASE WHEN" in sql and "ROUND(" in sql and "+ CAST" not in sql


# A stored `-0.0` reaches the model: the plan's literal keeps the sign.
STORED = {
    "x": T.select(T.k, v=X),
    "-x": T.select(T.k, v=-X),
    "atan2(x, -1.0)": T.select(T.k, v=X.atan2(-1.0)),
    "sqrt(x)": T.select(T.k, v=X.sqrt()),
    "x + 0.0": T.select(T.k, v=X + 0.0),
    "x = 0.0": T.select(T.k, v=(X == 0.0)),
    "x < 0.0": T.select(T.k, v=(X < 0.0)),
    "round(x)": T.select(T.k, v=X.round()),
}


@pytest.mark.parametrize("label", STORED)
def test_a_stored_zero_is_the_models_on_the_written_plan(label: str) -> None:
    rows = [(0, NEG_ZERO), (1, 0.0), (2, 1.5)]
    expr = STORED[label]
    assert written(expr, rows) == model(expr, rows), label
    # and the model reads the stored sign: `atan2(-0.0, -1.0)` is `-π`.
    if label == "atan2(x, -1.0)":
        assert model(expr, rows)[0] == (0, -round(math.pi, 6))


def test_the_zeros_are_one_key_at_the_identity_boundaries() -> None:
    """Grouping, `IN` and a comparison read `-0.0` as `0.0` on DuckDB
    (duckdb-float-signs); the written plan adds no canon."""
    rows = [(0, NEG_ZERO), (1, 0.0), (2, NEG_ZERO)]
    groups = T.group_by("x").aggregate(n=T.k.count()).select(k=_.n, v=_.n)
    assert written(groups, rows) == model(groups, rows) == [(3, 3)]
    member = T.select(T.k, v=X.isin([0.0]))
    assert written(member, rows) == model(member, rows) == [(0, True), (1, True), (2, True)]


@pytest.mark.parametrize("order", [[0, 1, 2], [2, 1, 0], [1, 2, 0]])
def test_the_representative_of_a_zero_class_is_canonical_whatever_the_row_order(order) -> None:
    """D31 leaves the zero of a `MIN`, `MAX`, group key or `DISTINCT` row open
    (a member of the class, or its canonical value): DuckDB's pick depends on
    row order, so the writer prints the class's canonical `+0.0` and a rerun
    gives the same sign (`Dialect.zero_rep`)."""
    base = [(0, NEG_ZERO), (1, 0.0), (2, NEG_ZERO)]
    rows = [base[i] for i in order]
    for agg in (X.min(), X.max()):
        expr = T.aggregate(v=agg).mutate(k=ibis.literal(0)).select("k", "v")
        assert written(expr, rows) == [(0, (0.0, 1.0))]
        assert model(expr, rows)[0][1][0] == 0.0  # either member of the class
    keys = T.group_by("x").aggregate(n=T.k.count()).select(k=_.n, v=_.x)
    assert written(keys, rows) == [(3, (0.0, 1.0))]
    distinct = T.select(T.k * 0, v=X).distinct()
    assert written(distinct, rows) == [(0, (0.0, 1.0))]


@pytest.mark.parametrize("pair", [(NEG_ZERO, 0.0), (0.0, NEG_ZERO)])
def test_least_and_greatest_of_both_zeros_are_the_models_up_to_a_zero(pair) -> None:
    """`least` and `greatest` keep the first of equal zeros on DuckDB; the model
    reads a zero as open here (D31)."""
    rows = [(0, pair[0])]
    other = ibis.literal(pair[1])
    for expr in (
        T.select(T.k, v=ibis.least(X, other)),
        T.select(T.k, v=ibis.greatest(X, other)),
    ):
        ((k, got),) = written(expr, rows)
        assert got[0] == 0.0
        ((k2, want),) = model(expr, rows)
        assert want[0] == 0.0


def test_sum_and_average_of_negative_zeros_are_positive_in_the_model_and_on_duckdb() -> None:
    rows = [(0, NEG_ZERO), (1, NEG_ZERO)]
    for fn in ("sum", "mean"):
        expr = T.aggregate(v=getattr(X, fn)()).mutate(k=ibis.literal(0)).select("k", "v")
        assert written(expr, rows) == model(expr, rows) == [(0, (0.0, 1.0))]
