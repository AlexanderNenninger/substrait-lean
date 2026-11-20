"""Assumed issues are checked by values an engine returns (#2018, ruling 195).

An assumed issue (a `SUM` that leaves 64 bits, an operation on finite doubles
that gives `±∞`) raises in the reference wherever the plan as written
evaluates it, whatever sits above it (`Rel.HasIssue`). An engine evaluates
lazily: it prunes a column nothing reads, pushes a filter or a limit below a
projection, skips one side of a join whose other side is empty and counts
rows without computing them. A guard inside the plan is then never evaluated.
The run checks each assumed issue first, by a statement whose result is the
verdict (`Report._check_assumed`), on the run's own engine.

Each shape, on each engine, with an integer `SUM` and a product of doubles:
the run is refused before it runs where the plan as written overflows, and
runs where it does not.
"""

import json
import math

import ibis
import pyarrow as pa
import pytest
from hypothesis import given, settings
from hypothesis import strategies as st
from ibis import _

import sverify as sv
from _engines import PROFILED
from sverify._lean_eval import lean_assumed, with_tables
from sverify.engine import connect, put_table, written_plan
from sverify.errors import PreconditionError

EXACT = [sv.equivalent(floats="exact")]
FINITE = {"t": [_.f >= -1.5e308, _.f <= 1.5e308]}


def _verify(shape: str) -> sv.Report:
    requires = FINITE if shape.split("-")[0] in ("fsum", "variance") else None
    return sv.verify(SHAPES[shape](), requires=requires, ensures=EXACT)


T = ibis.table({"a": "int64", "x": "int64", "f": "float64"}, name="t")
E = ibis.table({"a": "int64"}, name="e")

# The group a = -1 overflows: its x sum leaves 64 bits, its sum of |f| and its
# variance of f are past the largest double, and its f times 10 is ±inf. The
# row with a > 0 does not.
BAD = pa.table({"a": [1, -1, -1], "x": [1, 2**62, 2**62], "f": [1.0, 1e308, -1e308]})
GOOD = pa.table({"a": [1, -1, -1], "x": [1, 2, 3], "f": [1.0, 2.0, 3.0]})


def _sums():
    return T.group_by("a").aggregate(s=T.x.sum())


def _product():
    return T.select("a", g=T.f * 10.0)


SHAPES = {
    # (a) #2018: a left join on a key, of whose right input no column is used.
    "sum-unused-join": lambda: T.select("a").left_join(s := _sums(), _.a == s.a).select(T.a),
    "product-unused-join": lambda: (
        T.select("a")
        .left_join(p := _product().group_by("a").aggregate(m=_.g.max()), _.a == p.a)
        .select(T.a)
    ),
    # (b) a filter above the guarded column, which the output reads.
    "sum-filter": lambda: _sums().filter(_.a > 0),
    "product-filter": lambda: _product().filter(_.a > 0),
    # (c) a limit above it.
    "sum-limit": lambda: _sums().order_by("a").limit(1),
    "product-limit": lambda: _product().order_by("a").limit(1),
    # (d) a join to an empty input.
    "sum-empty-join": lambda: _sums().join(E, "a"),
    "product-empty-join": lambda: _product().join(E, "a"),
    # A SUM of doubles per group, and a VARIANCE, under a filter: their checks
    # fail closed near the largest double (`Measure.infCheck`). The inputs are
    # finite (`FINITE`), or an infinity among them is a domain error.
    "fsum-filter": lambda: T.group_by("a").aggregate(s=T.f.abs().sum()).filter(_.a > 0),
    "variance-filter": lambda: T.group_by("a").aggregate(v=T.f.var()).filter(_.a > 0),
    # A window's SUM, per frame the plan computes, under a filter.
    "sum-window-filter": lambda: T.select("a", w=T.x.sum().over(group_by="a", order_by="x")).filter(
        _.a > 0
    ),
    # (e) a count above it.
    "sum-count": lambda: (s := _sums()).aggregate(n=s.count()),
    "product-count": lambda: (p := _product()).aggregate(n=p.count()),
}


def _con(t: pa.Table):
    con = connect()
    put_table(con, "t", t)
    put_table(con, "e", pa.table({"a": pa.array([], pa.int64())}))
    return con


@pytest.mark.parametrize("engine", PROFILED)
@pytest.mark.parametrize("shape", SHAPES)
def test_an_assumed_issue_the_output_does_not_need_refuses_the_run(engine, shape):
    report = _verify(shape)
    assert report.assumed, report.issues
    report.run(_con(GOOD), engine, optimize=False)
    with pytest.raises(PreconditionError, match="assumed"):
        report.run(_con(BAD), engine, optimize=False)


@pytest.mark.parametrize("engine", PROFILED)
def test_an_assumed_issue_in_a_branch_no_row_takes_runs(engine):
    # The product is in the branch for a > 0, and only row 2 (a = -1) would
    # overflow: the plan as written evaluates the product on no row that
    # overflows (`Expr.issues` counts the branch a CASE takes).
    expr = T.select(g=ibis.cases((T.a > 0, T.f * 10.0), else_=0.0))
    report = sv.verify(expr, ensures=EXACT)
    assert report.assumed
    assert report.run(_con(BAD), engine, optimize=False).num_rows == 3


# The values around the edges: sums past 64 bits, products past the largest
# double, and operands that are not finite (whose product is no overflow).
_INTS = st.sampled_from([0, 1, -1, 2**62, -(2**62), 2**63 - 1, -(2**63)])
_FLOATS = st.sampled_from([0.0, 1.0, -1.0, 2e307, 1e308, -1e308, math.inf, -math.inf, math.nan])
_ROWS = st.lists(st.tuples(st.sampled_from([-1, 0, 1]), _INTS, _FLOATS), max_size=4)
_REPORTS: dict[str, sv.Report] = {}


@pytest.mark.parametrize("engine", ["duckdb", "polars"])
# The oracle evaluates no window (`--assumed`), and an aggregate of doubles is
# checked failing closed (`Measure.infCheck`): those are tested one way, below.
@pytest.mark.parametrize(
    "shape", [k for k in SHAPES if k.split("-")[0] in ("sum", "product") and "window" not in k]
)
@settings(deadline=None)
@given(rows=_ROWS)
def test_the_run_refuses_exactly_where_the_reference_runs_into_an_assumed_issue(
    engine, shape, rows
):
    # The oracle is the Lean evaluator (`--assumed`: `Expr.issues` on every
    # row an operator evaluates and the groups' true sums, `Rel.HasIssue`).
    report = _REPORTS.get(shape) or _REPORTS.setdefault(shape, _verify(shape))
    assert report.internal_plan is not None
    plan = json.loads(written_plan(report.internal_plan))
    expected = lean_assumed(json.dumps(with_tables(plan, {"t": rows, "e": []})))
    data = pa.table(
        {k: [r[i] for r in rows] for i, k in enumerate("axf")},
        schema=pa.schema([("a", pa.int64()), ("x", pa.int64()), ("f", pa.float64())]),
    )
    if expected is None:
        report.run(_con(data), engine, optimize=False)
    else:
        with pytest.raises(PreconditionError, match="assumed"):
            report.run(_con(data), engine, optimize=False)


@pytest.mark.parametrize("engine", ["duckdb", "polars"])
@pytest.mark.parametrize("shape", ["fsum-filter", "variance-filter"])
@settings(deadline=None)
@given(rows=_ROWS)
def test_an_aggregate_of_doubles_refuses_wherever_the_reference_overflows(engine, shape, rows):
    # Failing closed: the run refuses wherever the reference's value of the
    # aggregate overflows, and may refuse near the largest double where it
    # does not.
    report = _REPORTS.get(shape) or _REPORTS.setdefault(shape, _verify(shape))
    assert report.internal_plan is not None
    plan = json.loads(written_plan(report.internal_plan))
    expected = lean_assumed(json.dumps(with_tables(plan, {"t": rows, "e": []})))
    data = pa.table(
        {k: [r[i] for r in rows] for i, k in enumerate("axf")},
        schema=pa.schema([("a", pa.int64()), ("x", pa.int64()), ("f", pa.float64())]),
    )
    if expected is not None:
        # Refused: by the check, or by `FINITE` on data that breaks it.
        with pytest.raises(PreconditionError):
            report.run(_con(data), engine, optimize=False)
