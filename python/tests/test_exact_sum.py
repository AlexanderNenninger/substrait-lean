"""`SUM`, `AVG`, `VAR`, `STDDEV`, `COVAR` and `CORR` of doubles maintained
from an exact state (#918 Part B, `sverify._exact_sum`,
`SubstraitLean/IncrementalFloat.lean`): the glue's fold and finish against
exact rationals and against the checker's `floatSumCR`, `varOf`, `covOf` and
`corrOf`, and a pipeline that keeps them exactly over random inserts and
deletes."""

from __future__ import annotations

import json
import math
import random
from decimal import Decimal
from fractions import Fraction

import ibis
import pyarrow as pa
import pyarrow.compute as pc
import pytest
from hypothesis import given, settings
from hypothesis import strategies as st
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


def _scaled(v: float) -> int:
    if math.isnan(v):
        return _exact_sum.MAX_MAG + 2
    if math.isinf(v):
        return _exact_sum.MAX_MAG + 1 if v > 0 else -(_exact_sum.MAX_MAG + 1)
    return int(Fraction(v) * _exact_sum.SCALE)


EDGES = [
    5e-324,
    -5e-324,
    2.225073858507201e-308,  # the largest subnormal
    2.2250738585072014e-308,
    1.7976931348623157e308,
    -1.7976931348623157e308,
    *(2.0**k * (1 - 2**-53) for k in range(-1021, 1025, 97)),  # 2^k - ulp
    *(2.0**k for k in range(-1074, 1024, 89)),
]


def _moments(kind: str, xs, ys, ws) -> dict:
    """Each group's exact moments, row by row with Python ints."""
    terms = _exact_sum.TERMS[kind]
    pair = kind in ("cov", "corr")
    out: dict = {}
    for k, x, y, w in zip(xs[0], xs[1], ys, ws, strict=True):
        vs = [x, y] if pair else [x]
        if any(v is None for v in vs):
            continue
        acc = out.setdefault(_exact_sum.key_of([k]), [0] * _exact_sum.width(kind))
        sv_ = {"x": _scaled(vs[0]), "y": _scaled(vs[-1])}
        for j, t in enumerate(terms):
            acc[j] += w * math.prod(sv_[c] for c in t)
        for v in vs:
            if math.isnan(v):
                acc[len(terms)] += w
            elif math.isinf(v):
                acc[len(terms) + (1 if v > 0 else 2)] += w
    return out


def _limbs(engine: str, kind: str, ks, xs, ys, ws, key_type: str = "int64") -> dict:
    """The engine's limbs of the rows, added up per group and code, read
    back as each group's moments (`_exact_sum.moments`)."""
    from sverify.engine import connect, put_table, run_plan, written_plan

    e = _exact_sum.Exact(0, kind)
    t = ibis.table(
        {"k0": key_type, "__w": "int64", "__ok0": "int64", "__x0": "float64", "__y0": "float64"},
        name="rows",
    )
    parts = _exact_sum.limbs(t, ["k0"], [(e, "__x0", "__y0" if e.pair else None, "__ok0")])
    code, value = _exact_sum.CODE, _exact_sum.VALUE
    summed = parts.group_by(["k0", code]).aggregate(**{value: parts[value].sum()})
    plan = written_plan(plan_json(None, summed))  # pyrefly: ignore[bad-argument-type]
    con = connect("duckdb" if engine == "spark" else engine)  # Spark reads DuckDB's tables
    ok = [int(x is not None and (not e.pair or y is not None)) for x, y in zip(xs, ys, strict=True)]
    data = {"k0": ks, "__w": ws, "__ok0": ok, "__x0": xs, "__y0": ys}
    put_table(con, "rows", pa.table(data, schema=t.schema().to_pyarrow()))
    slots: dict = {}
    for r in run_plan(con, plan, engine).to_pylist():
        _, rest = divmod(r[code], _exact_sum._SLOTS * _exact_sum._LIMBS)
        slot, limb = divmod(rest, _exact_sum._LIMBS)
        g = slots.setdefault(_exact_sum.key_of([r["k0"]]), {})
        g[slot] = g.get(slot, 0) + (int(r[value]) << (_exact_sum._BITS * limb))
    assert all(_exact_sum.BROKEN not in g for g in slots.values())
    return {k: _exact_sum.moments(e, g) for k, g in slots.items() if any(g.values())}


# Spark runs the limbs with the split that needs no POWER or LOG2 (E7 of
# ruling 167, pending Fable's sign-off on #1873).
ENGINES = ["duckdb", "polars", pytest.param("spark", marks=pytest.mark.backend("spark"))]


def _frexp(x: float) -> tuple[int, int]:
    """The grid position and signed integer mantissa of a finite double:
    `x = m · 2^(p - 1074)`, with `2⁵²` ≤ `|m|` < `2⁵³` for a normal `x`."""
    e = max(math.frexp(x)[1] - 1, -1022)
    return e + 1022, int(Fraction(x) * 2 ** (52 - e))


@pytest.mark.parametrize("engine", ENGINES)
def test_the_split_is_frexp(engine):
    """The engine's split of a double into mantissa and grid position is
    `frexp`'s: every `2^k` and `2^k - ulp` (so every literal and every step of
    the split), the subnormals' edges, the largest double, both signs, and
    random values across the range (S2, S4 of ruling 174)."""
    from sverify.engine import connect, put_table, run_plan, written_plan

    rng = random.Random(174)
    xs = [2.0**k for k in range(-1074, 1024)]
    xs += [math.nextafter(2.0**k, 0.0) for k in range(-1073, 1024)] + [
        math.nextafter(math.inf, 0.0)
    ]
    xs += [5e-324, math.nextafter(2.0**-1022, 0.0), 2.0**-1022]
    xs += [math.ldexp(rng.uniform(0.5, 1), rng.randint(-1074, 1024)) for _ in range(2000)]
    xs = [x for x in xs if x != 0 and math.isfinite(x)]
    xs += [-x for x in xs] + [0.0, -0.0, math.nan, math.inf, -math.inf]
    t = ibis.table({"i": "int64", "x": "float64"}, name="rows")
    split = _exact_sum._split(t, "x").select("i", "x_p", "x_m", "x_bad")
    plan = written_plan(plan_json(None, split))  # pyrefly: ignore[bad-argument-type]
    con = connect("duckdb" if engine == "spark" else engine)  # Spark reads DuckDB's tables
    put_table(con, "rows", pa.table({"i": list(range(len(xs))), "x": xs}))
    got = {
        r["i"]: (r["x_p"], r["x_m"], r["x_bad"]) for r in run_plan(con, plan, engine).to_pylist()
    }
    want = [
        (*_frexp(x), 0) if x != 0 and math.isfinite(x) else (got[i][0], 0, 0)
        for i, x in enumerate(xs)
    ]
    assert [got[i] for i in range(len(xs))] == want


@pytest.mark.parametrize("engine", ENGINES)
@pytest.mark.parametrize("kind", ["fsum", "var", "cov", "corr"])
def test_limbs_are_the_exact_moments(engine, kind):
    """The engine's limbs of random rows (NaN, infinities, subnormals, the
    largest double, `2^k - ulp`, NULLs, large and negative weights) add up to
    the exact moments; the same rows deleted leave no limb (E6)."""
    rng = random.Random(918)
    xs = [value(rng) for _ in range(1500)] + EDGES + [-v for v in EDGES]
    ys = [value(rng) for _ in xs]
    ws = [rng.choice([1, 1, -1, 2, 300, -1000, 2**40]) for _ in xs]
    ks = [rng.choice([0, 1, None]) for _ in xs]
    want = {k: m for k, m in _moments(kind, (ks, xs), ys, ws).items() if any(m)}
    assert _limbs(engine, kind, ks, xs, ys, ws) == want
    gone = _limbs(engine, kind, ks + ks, xs + xs, ys + ys, ws + [-w for w in ws])
    assert gone == {}


doubles = st.one_of(st.none(), st.sampled_from(SPECIAL), st.floats(allow_nan=True))


@settings(max_examples=100, deadline=None)
@given(
    kind=st.sampled_from(["fsum", "favg", "var", "cov", "corr"]),
    rows=st.lists(
        st.tuples(
            st.sampled_from([0.0, -0.0, 1.5, math.nan, None]),
            doubles,
            doubles,
            st.one_of(st.integers(-3, 3), st.integers(-(2**40), 2**40)),
        ),
        max_size=40,
    ),
)
def test_limbs_are_the_row_by_row_moments(kind, rows):
    """The engine's limbs give the moments a row-by-row fold gives: float
    keys (NaN, `-0.0`), NaN and infinities, and weights up to `2⁴⁰`."""
    ks, xs, ys, ws = (list(c) for c in zip(*rows, strict=True)) if rows else ([], [], [], [])
    want = {k: m for k, m in _moments(kind, (ks, xs), ys, ws).items() if any(m)}
    assert _limbs("duckdb", kind, ks, xs, ys, ws, "float64") == want


def _state(n: int, slots: dict[tuple[int, int], int | None]) -> pa.Table:
    """A state of one group: its own row with `n` values and a limb row per
    (slot, limb)."""
    code, value = _exact_sum.CODE, _exact_sum.VALUE
    limb_type = pa.decimal128(38, 0)
    rows = [{"k0": 1, "__count": n, "__n0": n, "__s0": None, code: None, value: Decimal(0)}]
    for (slot, limb), v in slots.items():
        rows.append(
            {
                "k0": 1,
                "__count": 0,
                "__n0": 0,
                "__s0": None,
                code: slot * 256 + limb,
                value: None if v is None else Decimal(v),
            }
        )
    schema = pa.schema(
        [("k0", pa.int64()), ("__count", pa.int64()), ("__n0", pa.int64()),
         ("__s0", pa.float64()), (code, pa.int32()), (value, limb_type)]
    )  # fmt: skip
    return pa.Table.from_pylist(rows, schema=schema)


def test_attach_finishes_from_limbs_and_guards_them():
    """The finish reads a group's limbs; past the limbs' headroom (E1), with
    a failed split (E2) or a NULL limb (an overflow an engine let through,
    S5 of ruling 174) it raises."""
    e = [_exact_sum.Exact(0, "fsum")]
    got = _exact_sum.attach(
        _state(2, {(_exact_sum.X, 1073 // 32): 3 * 2 ** (1073 % 32)}), ["k0"], e, check=True
    )
    assert got.filter(pc.call_function("is_null", [got.column("__l")])).column(
        "__s0"
    ).to_pylist() == [1.5]
    with pytest.raises(ValueError, match="exceeds the exact state"):
        _exact_sum.attach(_state(_exact_sum.HEADROOM, {}), ["k0"], e, check=False)
    with pytest.raises(ValueError, match="split into limbs failed"):
        _exact_sum.attach(_state(1, {(_exact_sum.BROKEN, 0): 1}), ["k0"], e, check=False)
    with pytest.raises(ValueError, match="limb of measure 0 is NULL"):
        _exact_sum.attach(_state(1, {(_exact_sum.X, 3): None}), ["k0"], e, check=False)


def test_finish_rounds_once():
    f = _exact_sum.finish
    for s in [1, -1, 3, 2**1074 + 1, 10**400, -(10**400)]:
        assert f("fsum", [s, 0, 0, 0], 1) == float(Fraction(s, _exact_sum.SCALE))
    assert f("fsum", [0, 0, 0, 0], 0) is None
    both = f("fsum", [0, 0, 1, 1], 2)  # +inf and -inf
    assert both is not None and math.isnan(both)
    assert f("favg", [0, 0, 1, 0], 2) == math.inf
    assert f("fsum", [2**2200, 0, 0, 0], 1) == math.inf
    assert _exact_sum.raises("fsum", [2**2200, 0, 0, 0], math.inf) is not None
    assert _exact_sum.raises("fsum", [0, 0, 1, 1], math.nan) is not None
    assert _exact_sum.raises("fsum", [0, 1, 1, 1], math.nan) is None
    assert _exact_sum.raises("var", [0, 0, 0, 1, 0], math.nan) is not None


def _ours(kind: str, xs, ys=None, sample: bool = False, sqrt: bool = False):
    """The aggregate of one group's values from their exact moments,
    finished by `sverify._exact_sum`."""
    ys = ys if ys is not None else [0.0] * len(xs)
    mo = _moments(kind, ([0] * len(xs), xs), ys, [1] * len(xs))
    m = mo.get((0,), [0] * _exact_sum.width(kind))
    pair = kind in ("cov", "corr")
    n = sum(x is not None and (not pair or y is not None) for x, y in zip(xs, ys, strict=True))
    return _exact_sum.finish(kind, m, n, sample, sqrt)


MEASURES = {
    "s": (lambda t: t.x.sum(), lambda xs, ys: _ours("fsum", xs)),
    "a": (lambda t: t.x.mean(), lambda xs, ys: _ours("favg", xs)),
    "vs": (lambda t: t.x.var(how="sample"), lambda xs, ys: _ours("var", xs, sample=True)),
    "vp": (lambda t: t.x.var(how="pop"), lambda xs, ys: _ours("var", xs)),
    "ds": (
        lambda t: t.x.std(how="sample"),
        lambda xs, ys: _ours("var", xs, sample=True, sqrt=True),
    ),
    "dp": (lambda t: t.x.std(how="pop"), lambda xs, ys: _ours("var", xs, sqrt=True)),
    "cs": (lambda t: t.x.cov(t.y, how="sample"), lambda xs, ys: _ours("cov", xs, ys, sample=True)),
    "cp": (lambda t: t.x.cov(t.y, how="pop"), lambda xs, ys: _ours("cov", xs, ys)),
    "r": (lambda t: t.x.corr(t.y, how="pop"), lambda xs, ys: _ours("corr", xs, ys)),
}


def _agree(groups: dict[int, list[tuple]], names: list[str]) -> list[tuple]:
    """Whether `sverify._exact_sum`'s aggregates of each group's `(x, y)`
    equal the checker's (`Rel.eval`: `floatSumCR`, `floatAvgCR`, `varOf`,
    `covOf`, `corrOf`). Lean prints doubles with six decimals, so the plan
    compares them and prints the booleans."""
    t = ibis.table({"g": "int64", "x": "float64", "y": "float64"}, name="t")
    e = ibis.table({"eg": "int64", **{f"e_{n}": "float64" for n in names}}, name="e")
    agg = t.group_by("g").aggregate(**{n: MEASURES[n][0](t) for n in names})
    j = agg.join(e, agg.g == e.eg)

    def same(a, b):
        return (a.isnull() & b.isnull()) | (a.isnan() & b.isnan()).fill_null(False) | (a == b)

    q = j.select("g", **{f"ok_{n}": same(j[n], j[f"e_{n}"]).fill_null(False) for n in names})
    expected = []
    for g, ps in groups.items():
        xs, ys = [p[0] for p in ps], [p[1] for p in ps]
        expected.append((g, *(MEASURES[n][1](xs, ys) for n in names)))
    data = [(g, x, y) for g, ps in groups.items() for x, y in ps]
    plan = json.loads(plan_json(None, q))  # pyrefly: ignore[bad-argument-type]
    return evaluate(plan, {"t": data, "e": expected})


def _groups(seed: int, gen) -> dict[int, list[tuple]]:
    rng = random.Random(seed)
    groups = {g: [(gen(rng), gen(rng)) for _ in range(rng.randrange(1, 12))] for g in range(40)}
    groups[40] = [(math.inf, 1.0), (-math.inf, 2.0), (1.0, 3.0)]
    groups[41] = [(-0.0, -0.0), (-0.0, 1.0)]
    groups[42] = [(5e-324, 1e-300)] * 7
    groups[43] = [(None, 1.0)]
    groups[44] = [(math.nan, 1.0), (math.nan, 2.0)]
    groups[45] = [(3.0, 1.0)]
    return groups


@pytest.mark.parametrize("seed", range(3))
def test_finish_is_the_checkers_floatsumcr(seed):
    groups = _groups(seed, value)
    got = _agree(groups, ["s", "a"])
    assert len(got) == len(groups)
    assert all(all(r[1:]) for r in got), [r for r in got if not all(r[1:])]


@pytest.mark.parametrize("seed", range(3))
def test_finish_is_the_checkers_varof_covof_corrof(seed):
    """D30's values: `varOf`, `covOf`, `corrOf` of exact moments rounded
    once, `STDDEV` and `CORR` through `sqrtMag`; values of a few magnitudes
    so the moments do not overflow, NaN, `±∞`, `-0.0` and subnormals among
    them."""

    def gen(rng: random.Random) -> float | None:
        if rng.random() < 0.15:
            return rng.choice([0.0, -0.0, 5e-324, 1e-300, 1.5, math.nan, math.inf, None])
        return rng.choice([-1, 1]) * rng.uniform(0, 1) * 10.0 ** rng.randrange(-20, 20)

    names = ["vs", "vp", "ds", "dp", "cs", "cp", "r"]
    groups = _groups(seed, gen)
    got = _agree(groups, names)
    assert len(got) == len(groups)
    assert all(all(r[1:]) for r in got), [r for r in got if not all(r[1:])]


SCHEMA = pa.schema([("g", pa.int64()), ("x", pa.float64())])


def table(rs) -> pa.Table:
    return pa.table({"g": [r[0] for r in rs], "x": [r[1] for r in rs]}, schema=SCHEMA)


@sv.transform(requires={"t": [col.x.isnull() | ((col.x > -1e300) & (col.x < 1e300))]})
def sums(t):
    return t.group_by("g").aggregate(s=t.x.sum(), a=t.x.mean(), n=t.x.count())


def _same(got_v, want) -> bool:
    if got_v is None or want is None:
        return got_v is None and want is None
    return got_v == want or (math.isnan(got_v) and math.isnan(want))


def _check(node, live, names=("s", "a")) -> None:
    """The view's rows are `_exact_sum`'s of the current rows, which are the
    checker's (`_agree`)."""
    by: dict[int, list[tuple]] = {}
    for r in live:
        by.setdefault(r[0], []).append((r[1], r[2] if len(r) > 2 else 0.0))
    got = {r[0]: r for r in rows(node)}
    assert set(got) == set(by)
    assert all(all(r[1:]) for r in _agree(by, list(names)))
    for g, row in got.items():
        xs, ys = [p[0] for p in by[g]], [p[1] for p in by[g]]
        for c, n in enumerate(names, start=1):
            assert _same(row[c], MEASURES[n][1](xs, ys)), (g, n, row[c])


@pytest.mark.parametrize("engine", ENGINES)
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
    # Every row deleted: no group and no limb is left (E6).
    src.apply(Changes(deletes=table(live)))
    node.refresh(engine=engine)
    assert rows(node) == []
    groups = node._stage.view.groups
    assert groups is not None and groups.num_rows == 0


@pytest.mark.backend("spark")
def test_a_refresh_on_spark_without_ansi_is_refused():
    """A refresh meets the settings check before any plan runs
    (`sverify.routes.choose`, `check_settings`). Without ANSI, Spark's
    `DECIMAL(38,0)` `SUM` gives NULL on overflow (`spark-decimal-arith`),
    so a limb's sum would fail silently: the refresh is refused (S5 of
    ruling 174)."""
    from sverify.routes import EngineSettingsError
    from sverify_spark import engine

    spark = engine.session()
    src = StaticSource(table([(0, 1.5)]), name="t")
    node = src.pipe(sums)
    node.refresh(engine="spark")
    src.apply(Changes(inserts=table([(0, 2.5)]), deletes=table([])))
    spark.conf.set("spark.sql.ansi.enabled", "false")
    try:
        with pytest.raises(EngineSettingsError, match="spark.sql.ansi.enabled"):
            node.refresh(engine="spark")
    finally:
        spark.conf.set("spark.sql.ansi.enabled", "true")
    node.refresh(engine="spark")
    assert rows(node)[0][1] == 4.0


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


STATS = pa.schema([("g", pa.int64()), ("x", pa.float64()), ("y", pa.float64())])


def stat_table(rs) -> pa.Table:
    return pa.table({n: [r[i] for r in rs] for i, n in enumerate(STATS.names)}, schema=STATS)


@sv.transform(
    requires={
        "t": [
            col.x.isnull() | ((col.x > -1e100) & (col.x < 1e100)),
            col.y.isnull() | ((col.y > -1e100) & (col.y < 1e100)),
        ]
    }
)
def stats(t):
    return t.group_by("g").aggregate(
        vs=t.x.var(how="sample"),
        dp=t.x.std(how="pop"),
        cs=t.x.cov(t.y, how="sample"),
        r=t.x.corr(t.y, how="pop"),
    )


@pytest.mark.parametrize("engine", ["duckdb"])  # Polars refuses COVAR (#271)
@pytest.mark.parametrize("seed", range(2))
def test_maintained_statistics_are_exact(seed, engine):
    """`VAR`, `STDDEV`, `COVAR` and `CORR` of doubles, maintained from exact
    moments over inserts and deletes, are the checker's `varOf`, `covOf` and
    `corrOf` of the current rows after every batch."""

    def gen(rng: random.Random) -> float | None:
        if rng.random() < 0.1:
            return rng.choice([0.0, -0.0, 5e-324, None])
        return 1e8 + rng.uniform(-1, 1) * 10.0 ** rng.randrange(-3, 3)

    rng = random.Random(seed)
    src = StaticSource(stat_table([]), name="t")
    node = src.pipe(stats)
    node.refresh(engine=engine)
    assert node._stage is not None and node._stage.view.strategy == "delta rules"
    live: list[tuple] = []
    for _ in range(20):
        ins = [(rng.randrange(4), gen(rng), gen(rng)) for _ in range(rng.randrange(6))]
        dels = rng.sample(live, min(len(live), rng.randrange(4)))
        for d in dels:
            live.remove(d)
        live += ins
        src.apply(Changes(inserts=stat_table(ins), deletes=stat_table(dels)))
        out = node.refresh(engine=engine)["stats"]
        assert out.report is not None and not out.report.touched and not out.report.diffed
        _check(node, live, ("vs", "dp", "cs", "r"))


def test_the_exact_fold_needs_no_numpy():
    """The base package does not declare numpy (#1447): the fold is Arrow's."""
    import subprocess
    import sys

    code = "import sys; sys.modules['numpy'] = None; import sverify._exact_sum, sverify.incremental"
    subprocess.run([sys.executable, "-c", code], check=True)
