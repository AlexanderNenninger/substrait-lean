"""`SUM` and `AVG` of doubles maintained from an exact state (#918 Part B,
`sverify._exact_sum`, `SubstraitLean/IncrementalFloat.lean`): the glue's
fold and finish against exact rationals and against the checker's
`floatSumCR`, and a pipeline that keeps them exactly over random inserts and
deletes."""

from __future__ import annotations

import json
import math
import random
from fractions import Fraction

import ibis
import pyarrow as pa
import pytest
from ibis import _ as col

import sverify as sv
from _pipelines import rows
from sverify import _exact_sum
from sverify.counterexample import evaluate
from sverify.engine import plan_json
from sverify.io import Changes, StaticSource

SPECIAL = [
    0.0,
    -0.0,
    5e-324,
    -5e-324,
    2.2250738585072014e-308,
    1e-300,
    1e308,
    -1e308,
    1.5,
    math.nan,
    math.inf,
    -math.inf,
    None,
]


def value(rng: random.Random) -> float | None:
    if rng.random() < 0.3:
        return rng.choice(SPECIAL)
    return rng.choice([-1, 1]) * rng.uniform(0, 1) * 10.0 ** rng.randrange(-320, 300)


def finite_value(rng: random.Random) -> float | None:
    """A value whose sums stay finite and never meet both infinities."""
    v = value(rng)
    return v if v is None or (math.isfinite(v) and abs(v) < 1e300) else rng.uniform(-1, 1)


def test_fold_is_exact():
    rng = random.Random(918)
    vals = [value(rng) for _ in range(5000)]
    ws = [rng.choice([1, 1, -1, 2, 300, -1000, 2**40]) for _ in vals]
    ks = [rng.choice([0, 1, None]) for _ in vals]
    got = _exact_sum.fold(pa.table({"k0": ks}), pa.array(vals, pa.float64()), pa.array(ws))
    want: dict = {}
    for k, v, w in zip(ks, vals, ws, strict=True):
        if v is None:
            continue
        acc = want.setdefault((k,), [0, 0, 0, 0])
        if math.isnan(v):
            acc[1] += w
        elif math.isinf(v):
            acc[2 if v > 0 else 3] += w
        else:
            acc[0] += w * int(Fraction(v) * _exact_sum.SCALE)
    assert got == want


def test_finish_rounds_once():
    for s in [1, -1, 3, 2**1074 + 1, 10**400, -(10**400)]:
        assert _exact_sum.finish([s, 0, 0, 0], 1, False) == float(Fraction(s, _exact_sum.SCALE))
    assert _exact_sum.finish([0, 0, 0, 0], 0, False) is None
    both = _exact_sum.finish([0, 0, 1, 1], 2, False)  # +inf and -inf
    assert both is not None and math.isnan(both)
    assert _exact_sum.finish([0, 0, 1, 0], 2, True) == math.inf
    assert _exact_sum.finish([2**2200, 0, 0, 0], 1, False) == math.inf
    assert _exact_sum.raises([2**2200, 0, 0, 0], math.inf) is not None
    assert _exact_sum.raises([0, 0, 1, 1], math.nan) is not None
    assert _exact_sum.raises([0, 1, 1, 1], math.nan) is None


def _agree(groups: dict[int, list[float | None]]) -> list[tuple]:
    """Whether `sverify._exact_sum`'s SUM and AVG of each group equal the
    checker's (`Rel.eval`, `floatSumCR` and `floatAvgCR`). Lean prints
    doubles with six decimals, so the plan compares them and prints the
    booleans."""
    t = ibis.table({"g": "int64", "x": "float64"}, name="t")
    e = ibis.table({"eg": "int64", "es": "float64", "ea": "float64"}, name="e")
    agg = t.group_by("g").aggregate(s=t.x.sum(), a=t.x.mean())
    j = agg.join(e, agg.g == e.eg)

    def same(a, b):
        return (a.isnull() & b.isnull()) | (a.isnan() & b.isnan()).fill_null(False) | (a == b)

    q = j.select("g", ok_s=same(j.s, j.es).fill_null(False), ok_a=same(j.a, j.ea).fill_null(False))
    expected = []
    for g, xs in groups.items():
        k = pa.table({"k0": [g] * len(xs)})
        mo = _exact_sum.fold(k, pa.array(xs, pa.float64()), pa.array([1] * len(xs)))
        m = mo.get((g,), [0, 0, 0, 0])
        n = sum(x is not None for x in xs)
        expected.append((g, _exact_sum.finish(m, n, False), _exact_sum.finish(m, n, True)))
    data = [(g, x) for g, xs in groups.items() for x in xs]
    plan = json.loads(plan_json(None, q))  # pyrefly: ignore[bad-argument-type]
    return evaluate(plan, {"t": data, "e": expected})


@pytest.mark.parametrize("seed", range(3))
def test_finish_is_the_checkers_floatsumcr(seed):
    rng = random.Random(seed)
    groups = {g: [value(rng) for _ in range(rng.randrange(1, 12))] for g in range(40)}
    groups[40] = [math.inf, -math.inf, 1.0]
    groups[41] = [-0.0, -0.0]
    groups[42] = [5e-324] * 7
    groups[43] = [None]
    got = _agree(groups)
    assert len(got) == len(groups)
    assert all(ok_s and ok_a for _, ok_s, ok_a in got), [r for r in got if not all(r[1:])]


SCHEMA = pa.schema([("g", pa.int64()), ("x", pa.float64())])


def table(rs) -> pa.Table:
    return pa.table({"g": [r[0] for r in rs], "x": [r[1] for r in rs]}, schema=SCHEMA)


@sv.transform(requires={"t": [col.x.isnull() | ((col.x > -1e300) & (col.x < 1e300))]})
def sums(t):
    return t.group_by("g").aggregate(s=t.x.sum(), a=t.x.mean(), n=t.x.count())


def _check(node, live) -> None:
    by: dict[int, list] = {}
    for g, x in live:
        by.setdefault(g, []).append(x)
    got = {r[0]: r for r in rows(node)}
    assert set(got) == set(by)
    agree = _agree(by)
    assert all(ok_s and ok_a for _, ok_s, ok_a in agree)
    for g, (_, s, a, _) in got.items():
        mo = _exact_sum.fold(
            pa.table({"k0": [g] * len(by[g])}),
            pa.array(by[g], pa.float64()),
            pa.array([1] * len(by[g])),
        ).get((g,), [0, 0, 0, 0])
        n = sum(x is not None for x in by[g])
        want_s, want_a = _exact_sum.finish(mo, n, False), _exact_sum.finish(mo, n, True)
        for got_v, want in ((s, want_s), (a, want_a)):
            if got_v is None or want is None:
                assert got_v is None and want is None
            else:
                assert got_v == want or (math.isnan(got_v) and math.isnan(want))


@pytest.mark.parametrize("engine", ["duckdb", "polars"])
@pytest.mark.parametrize("seed", range(2))
def test_a_maintained_double_sum_is_exact(seed, engine):
    rng = random.Random(seed)
    src = StaticSource(table([]), name="t")
    node = src.pipe(sums)
    node.refresh(engine=engine)
    assert node._stage is not None and node._stage.view.strategy == "delta rules"
    live: list[tuple[int, float | None]] = []
    for _ in range(25):
        ins = [(rng.randrange(5), finite_value(rng)) for _ in range(rng.randrange(6))]
        dels = rng.sample(live, min(len(live), rng.randrange(4)))
        for d in dels:
            live.remove(d)
        live += ins
        src.apply(Changes(inserts=table(ins), deletes=table(dels)))
        out = node.refresh(engine=engine)["sums"]
        assert out.report is not None and not out.report.touched and not out.report.diffed
        _check(node, live)


def test_no_drift_where_a_running_sum_drifts():
    """`1e16 + 1 − 1e16` in doubles is 0; the exact state keeps the 1."""
    src = StaticSource(table([(1, 1.0)]), name="t")
    node = src.pipe(sums)
    node.refresh()
    for _ in range(50):
        src.apply(Changes(inserts=table([(1, 1e16)])))
        node.refresh()
        src.apply(Changes(deletes=table([(1, 1e16)])))
        node.refresh()
    src.apply(Changes(inserts=table([(1, 2.0)])))
    node.refresh()
    assert [r[:2] for r in rows(node)] == [(1, 3.0)]


def test_a_job_resumed_from_a_delta_sink_stays_exact(tmp_path):
    """The exact state is not stored: a restarted job rebuilds it from the
    inputs (`_groups_on`), and the sink holds the finished doubles, which
    round-trip. A delete that a running double sum would lose stays exact."""
    from deltalake import DeltaTable, write_deltalake

    from sverify.io import DeltaSink, DeltaSource

    path, out = str(tmp_path / "t"), str(tmp_path / "sums")
    DeltaTable.create(path, SCHEMA, configuration={"delta.enableChangeDataFeed": "true"})
    live = [(1, 1.0), (2, 0.5)]
    write_deltalake(path, table(live), mode="append")

    def job():
        return sums(DeltaSource(path)).write(DeltaSink(out))

    node = job()
    node.refresh()
    for batch in ([(1, 1e16), (2, 5e-324), (2, -0.0)], [(1, -1e16), (3, 0.1)]):
        write_deltalake(path, table(batch), mode="append")
        live += batch
        node.refresh()
        _check(node, live)
    again = job()
    started = again.refresh()["sums"].started
    assert started is not None and started.startswith("resumed")
    write_deltalake(path, table([(1, 2.0), (3, 0.2)]), mode="append")
    live += [(1, 2.0), (3, 0.2)]
    again.refresh()
    _check(again, live)
    stored = pa.table(DeltaTable(out).to_pyarrow_table()).to_pylist()
    assert sorted(tuple(r.values()) for r in stored) == sorted(rows(again))
