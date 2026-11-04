"""#444's prototype slice, end to end: one test per row of the expanded slice
(https://github.com/AlexanderNenninger/substrait-lean/issues/444#issuecomment-6633505268).

Each test verifies a plan, runs it on DuckDB and on Polars by the route
`sverify.routes.choose` picks (`docs/core-semantics.md`, "Which plans run on
an engine", D13), and asserts the route, the class (#568) and the result.

Most rows wait for the Lean side: the class, `q` and shim columns of
`Profile.duckdb`'s and `Profile.polars`'s choices (steps 3a, 3b, D15) and
the option dependency report (3c). Those are expected failures while the
checker has no classes, and strict ones: they must pass once it does.
Rows that also wait for step 1c (`UNSPECIFIED` sort keys, open choices
proved over every pick), #575 (`±∞` as an error of the reference) or
`Profile.polars` contracts are expected failures without strictness, with
the reason.
"""

from __future__ import annotations

import json
import math

import ibis
import pyarrow as pa
import pytest
from ibis import _

import sverify as sv
from sverify import routes
from sverify.errors import PreconditionError, RouteError

ENGINES = ("duckdb", "polars")
DIVIDENDS = [-7, 2, 4, 3, -1, 5, 6]
DIVISORS = [2, -3, 3, -2, 2, 4, -4]


def _classed() -> bool:
    """Whether the checker's tables give the engines' classes (D15)."""
    rows = [routes.choices(p) for p in ENGINES]
    if any(r is None for r in rows):
        return False
    return any(
        r.get("class") is not None
        for p in ENGINES
        for r in (routes._options_json().get("choices") or {}).get(p, [])
    )


CLASSED = _classed()

#: The row needs the engines' classes from the checker.
classes = pytest.mark.xfail(
    not CLASSED,
    reason="Profile.duckdb and Profile.polars choices with class, q and shim (#444 3a, 3b, 3c)",
    strict=True,
)


def waits_for(why: str) -> pytest.MarkDecorator:
    """The row needs more than the classes; `why` names it."""
    return pytest.mark.xfail(reason=why, strict=False)


@pytest.fixture
def con() -> sv.engine.Connection:
    c = sv.connect()
    c.put(
        "t",
        pa.table(
            {
                "k": pa.array([1, 1, 1, 2, 2, None, None], pa.int64()),
                "i": pa.array(DIVIDENDS, pa.int64()),
                "j": pa.array(DIVISORS, pa.int64()),
                "n": pa.array([10, 20, 30, 40, 50, 60, 70], pa.int32()),
                "x": [0.1, 0.2, 0.3, 1e-3, 1e3, 2.5, -2.5],
                "s": ["abc", "héllo", None, "abc", "b", "xyz", "ab"],
            }
        ),
    )
    return c


def run_both(report: sv.Report, con, q: sv.observation.Observation | None = None) -> dict:
    """The plan's result on each engine, by the route `auto` picks; the
    results agree up to `q` (the report's observation by default)."""
    out = {e: report.run(con, e, route="auto") for e in ENGINES}
    q = q or report.observation
    assert q.difference(out["duckdb"], out["polars"]) is None
    return out


def route_of(report: sv.Report, engine: str) -> routes.Route:
    return report.routes.get(engine) or routes.choose(report, engine)


# -- A: integers and doubles -------------------------------------------------


@classes
def test_a1_integer_arithmetic_with_negative_operands(con) -> None:
    """`+ − × ÷ %` on `i64` with negative operands: Polars floors `//` and
    `%`, so its translation shims both (value side); DuckDB truncates, as
    the reference does."""
    t = con.table("t")
    req = {"t": [_.i.between(-100, 100), _.j.between(-100, 100), _.j != 0]}
    expr = t.select(
        "k",
        add=t.i + t.j,
        sub=t.i - t.j,
        mul=t.i * t.j,
        div=t.i // t.j,
        mod=t.i % t.j,
    )
    report = sv.verify(expr, requires=req)
    assert report.proved, str(report)
    out = run_both(report, con)
    assert sorted(out["duckdb"].column("mod").to_pylist()) == sorted(
        int(math.fmod(i, j)) for i, j in zip(DIVIDENDS, DIVISORS, strict=True)
    )
    assert route_of(report, "duckdb").kind == "reference"
    assert route_of(report, "duckdb").cls == "refines"
    assert route_of(report, "polars").kind == "reference"
    assert route_of(report, "polars").cls == "shim"


@classes
def test_a2_sum_of_a_bounded_int32(con) -> None:
    """Overflow proved absent from the bounds: no shim, no guard."""
    t = con.table("t")
    report = sv.verify(
        t.group_by("k").aggregate(total=t.n.sum()),
        requires={"t": [_.n.between(0, 1000), sv.max_rows(1_000_000)]},
    )
    assert report.proved and not report.assumed and not report.issues
    run_both(report, con)
    for e in ENGINES:
        assert route_of(report, e).kind == "reference"
        assert route_of(report, e).cls == "refines"


@classes
def test_a3_overflowing_batch_is_refused_before_the_run(con) -> None:
    """`SUM` of an unbounded `i64`: assumed to fit and checked on the data.
    A batch that overflows is refused before the plan runs, on both
    engines, with the precondition in the message.

    `i` may be NULL, and Polars sums a group of NULLs to 0 where the
    reference gives NULL: its translation shims `sum_empty_null`. With `i`
    NOT NULL in the preconditions no group is all NULL, and Polars refines."""
    t = con.table("t")
    report = sv.verify(t.group_by("k").aggregate(total=t.i.sum()))
    assert report.proved and [i.what for i in report.assumed] == ["i"]
    run_both(report, con)
    assert route_of(report, "duckdb").cls == "refines"
    assert route_of(report, "polars").cls == "shim"
    assert any("sum_empty_null" in s for s in route_of(report, "polars").shims)
    present = sv.verify(t.group_by("k").aggregate(total=t.i.sum()), requires={"t": [_.i.notnull()]})
    assert present.proved, str(present)
    run_both(present, con)
    for e in ENGINES:
        assert route_of(present, e).cls == "refines"
    # The plan reads every column of `t`: the bad batch has them all.
    bad = sv.connect()
    rows = con.get("t").slice(0, 2)
    i = rows.schema.get_field_index("i")
    bad.put("t", rows.set_column(i, "i", pa.array([2**62, 2**62], pa.int64())))
    for e in ENGINES:
        with pytest.raises(
            PreconditionError, match=r"SUM of i fits 64 bits.*refused before the run"
        ):
            report.run(bad, e, route="auto")


@waits_for("#575: overflow of doubles to ±inf as an error of the reference, with inferred bounds")
def test_a4_double_product_that_may_reach_infinity(con) -> None:
    """`x * y` on doubles: the bounds that keep it finite are inferred and
    checked on the data; a verified run never yields a new `±∞`."""
    u = ibis.table({"x": "float64", "y": "float64"}, name="u")
    report = sv.verify(u.select(z=u.x * u.y))
    assert report.proved, str(report)
    assert report.inferred.get("u"), "the bounds that keep x * y finite"
    good = sv.connect()
    good.put("u", pa.table({"x": [2.0, -3.0], "y": [4.0, 0.5]}))
    out = run_both(report, good)
    assert all(math.isfinite(z) for z in out["polars"].column("z").to_pylist())
    for e in ENGINES:
        assert route_of(report, e).cls == "refines"
    bad = sv.connect()
    bad.put("u", pa.table({"x": [1e200], "y": [1e200]}))
    for e in ENGINES:
        with pytest.raises(PreconditionError, match="refused before the run"):
            report.run(bad, e, route="auto")


@classes
def test_a5_avg_of_int32_and_rounding_ties(con) -> None:
    """`round` on ties (half away from zero in the reference; Polars rounds
    half to even natively, so its translation writes the mode), and `AVG`
    of an `i32` with a double result: its sum's order is open
    (`sum_order`), so with a row cap Lean bounds it per plan (`ε`) and
    Polars is `approx` within the postcondition's tolerance."""
    ties = sv.connect()
    ties.put(
        "t",
        pa.table({"k": [1, 1, 2], "n": pa.array([1, 2, 3], pa.int32()), "x": [0.5, 2.5, -1.5]}),
    )
    tt = ties.table("t")
    req = {"t": [_.x.between(-100, 100), _.n.between(-100, 100), sv.max_rows(1_000)]}
    rounded = sv.verify(tt.select("k", r=tt.x.round()), requires=req)
    mean = sv.verify(
        tt.group_by("k").aggregate(a=tt.n.mean()),
        requires=req,
        ensures=[sv.equivalent(floats=sv.within(abs=1e-6))],
    )
    for report in (rounded, mean):
        assert report.proved, str(report)
    assert sorted(run_both(rounded, ties)["polars"].column("r").to_pylist()) == [-2, 1, 3]
    assert sorted(run_both(mean, ties)["polars"].column("a").to_pylist()) == [1.5, 3.0]
    assert route_of(rounded, "duckdb").cls == "refines"
    assert route_of(rounded, "polars").cls == "shim"
    assert mean.epsilon, "the plan's bound on the mean"
    assert route_of(mean, "duckdb").cls in ("refines", "approx")
    assert route_of(mean, "polars").cls == "approx"


# -- B: observations ---------------------------------------------------------


@classes
def test_b1_float_aggregates_within_a_tolerance(con) -> None:
    """Float `SUM` and `AVG` with a tolerance postcondition: the summation
    order is open, so an engine is `approx` within the plan's bound (#85,
    `ε` per column), and the stated tolerance must cover it.

    With `x` in ±10⁶ the sum can cancel, so only an absolute bound exists
    (about 222 for the sum of 10⁶ rows, 2.2e-4 for the mean) and the
    postcondition states an absolute tolerance. With `x` non-negative
    nothing cancels, and a relative tolerance suffices."""
    t = con.table("t")
    cases = [
        (_.x.between(-1e6, 1e6), sv.within(abs=1e3)),
        (_.x.between(0, 1e6), sv.within(rel=1e-6)),
    ]
    for bound, tolerance in cases:
        report = sv.verify(
            t.group_by("k").aggregate(total=t.x.sum(), mean=t.x.mean()),
            requires={"t": [bound, sv.max_rows(1_000_000)]},
            ensures=[sv.equivalent(floats=tolerance), sv.approx(_.mean <= 1e6)],
        )
        assert report.proved, str(report)
        assert report.epsilon, "the plan's bound on the doubles"
        data = con if tolerance.abs is not None else _non_negative(con)
        run_both(report, data)
        assert route_of(report, "polars").cls == "approx", tolerance
        assert route_of(report, "duckdb").cls in ("refines", "approx")
    tight = sv.verify(
        t.group_by("k").aggregate(total=t.x.sum()),
        requires={"t": [_.x.between(-1e6, 1e6), sv.max_rows(1_000_000)]},
        ensures=[sv.equivalent()],
    )
    refused = routes.choose(tight, "polars")
    assert refused.refused and ("floats" in refused.reason or "doubles" in refused.reason)


def _non_negative(con) -> sv.engine.Connection:
    """`con`'s table `t` with `x` made non-negative."""
    out = sv.connect()
    t = con.get("t")
    x = [abs(v) for v in t.column("x").to_pylist()]
    out.put("t", t.set_column(t.schema.get_field_index("x"), "x", pa.array(x)))
    return out


@classes
def test_b2_group_by_a_double_key_with_zeros_and_nan(con) -> None:
    """`GROUP BY` a double holding `-0.0`, `0.0` and NaN: NaN equality is
    native, but Polars keeps the first zero it sees. Without
    `zeros="canon"` the q-refinement check refuses Polars (or writes the
    canon shim); with it, Polars refines up to `canon`."""
    z = sv.connect()
    z.put("d", pa.table({"x": [-0.0, 0.0, float("nan"), float("nan"), 1.0], "v": [1, 2, 3, 4, 5]}))
    d = z.table("d")
    expr = d.group_by("x").aggregate(n=d.v.count())
    exact = sv.verify(expr)
    assert exact.proved, str(exact)
    strict = routes.choose(exact, "polars")
    assert (strict.refused and "zeros" in strict.reason) or strict.cls == "shim", strict
    canon = sv.verify(expr, ensures=[sv.equivalent(zeros="canon")])
    out = run_both(canon, z)
    assert sorted(out["polars"].column("n").to_pylist()) == [1, 2, 2]
    assert route_of(canon, "polars").cls == "refines_up_to"
    assert route_of(canon, "duckdb").cls in ("refines", "refines_up_to")


# -- C: order and NULLs ------------------------------------------------------


@classes
def test_c1_explicit_nulls_first(con) -> None:
    """A key that states `NULLS FIRST`: explicit intent, native on both."""
    t = con.table("t")
    report = sv.verify(
        t.select("k", "i").order_by([ibis.asc("k", nulls_first=True), "i"]),
        ensures=[sv.equivalent(rows="sequence")],
    )
    out = run_both(report, con)
    assert out["polars"].column("k").to_pylist()[:2] == [None, None]
    for e in ENGINES:
        assert route_of(report, e).cls == "refines"


@waits_for(
    "the lift cannot tell `ORDER BY k` from `ORDER BY k NULLS LAST`: SQLGlot reads both as "
    "nulls_first=False, so it states NULLS_LAST, which Polars then takes natively"
)
def test_c2_unspecified_null_order(con) -> None:
    """`ORDER BY k` without a NULL placement: the reference puts NULLs last
    (D8), as DuckDB does; Polars puts them first, so its translation states
    `nulls_last`."""
    t = con.table("t")
    report = sv.verify(
        "SELECT k, i FROM t ORDER BY k, i",
        tables={"t": t},
        ensures=[sv.equivalent(rows="sequence")],
    )
    assert '"SORT_DIRECTION_UNSPECIFIED"' in (report.plan or "") or "UNSPECIFIED" in (
        report.plan or ""
    )
    out = run_both(report, con)
    assert out["polars"].column("k").to_pylist()[-2:] == [None, None]
    assert route_of(report, "duckdb").cls == "refines"
    assert route_of(report, "polars").cls == "shim"


def test_c3_limit_over_ties_is_reported_and_refused_where_required(con) -> None:
    """A sort with ties, then `LIMIT`: which tied rows survive is open.
    The report says so, the route warns, and a run that must be repeatable
    (an idempotent sink's epoch) is refused."""
    t = con.table("t")
    report = sv.verify(t.order_by("k").limit(2))
    assert report.proved and not report.deterministic
    r = routes.choose(report, "polars")
    assert r.kind == "reference" and not r.deterministic and r.warnings
    with pytest.raises(RouteError, match="rerun must give the same result"):
        report.run(con, "polars", route="auto", deterministic=True)


@classes
def test_c4_join_on_keys_with_nulls(con) -> None:
    """`=` skips NULL keys on both engines, as in the reference."""
    t = con.table("t")
    other = t.select(k2="k", m="n")
    report = sv.verify(t.join(other, t.k == other.k2).select("k", "i", "m"))
    out = run_both(report, con)
    assert None not in out["polars"].column("k").to_pylist()
    for e in ENGINES:
        assert route_of(report, e).cls == "refines"


# -- D: open options ---------------------------------------------------------


@waits_for(
    "the contract checker reports every condition over an open pick or element order as "
    "undetermined; it proves none over every choice yet"
)
def test_d1_open_picks_and_element_order(con) -> None:
    """`collect` and `first` without an order leave the elements' order and
    the pick open. Under `elements="multiset"` the plan runs on both
    engines; a condition that reads the open choice is reported, and one
    that holds for every choice is proved."""
    t = con.table("t")
    expr = t.group_by("k").aggregate(f=t.i.first(), mx=t.i.max(), l=t.i.collect())
    req = {"t": [_.i.between(-100, 100)]}
    q = sv.equivalent(elements="multiset")
    report = sv.verify(expr, requires=req, ensures=[q, _.f <= _.mx, _.l.length() >= 1])
    assert report.proved, str(report)
    run_both(report, con, sv.equivalent(elements="multiset"))
    for e in ENGINES:
        assert route_of(report, e).kind == "reference"
        assert route_of(report, e).cls in ("refines", "refines_up_to")
    reads = sv.verify(expr, requires=req, ensures=[q, _.f == _.mx, _.l[0] <= _.mx])
    assert {c.label: c.ignores for c in reads.ensures} == {
        "(_.f == _.mx)": ("picks",),
        "(_.l[0] <= _.mx)": ("elements",),
    }
    assert routes.choose(reads, "polars").refused


# -- E: strings --------------------------------------------------------------


@classes
def test_e1_substring_with_a_negative_start_and_strpos(con) -> None:
    """Polars counts from 0, in bytes for `strpos`, and gives NULL where
    `strpos` gives 0: the translation rewrites both."""
    t = con.table("t")
    report = sv.verify(
        "SELECT substring(s, -2, 2) AS tail, strpos(s, 'b') AS at FROM t",
        tables={"t": t},
    )
    assert report.proved, str(report)
    out = run_both(report, con)
    assert sorted(out["polars"].column("at").to_pylist(), key=lambda v: (v is None, v)) == [
        0,
        0,
        1,
        2,
        2,
        2,
        None,
    ]
    assert route_of(report, "duckdb").cls == "refines"
    assert route_of(report, "polars").cls == "shim"


# -- F: routes between profiles ----------------------------------------------


@waits_for(
    "a contract checked under Polars's own choices: `--contract` transfers the reference's "
    "proof to Substrait only, and Polars's `%` floors where the reference truncates"
)
def test_f1_verified_under_polars_runs_natively(con) -> None:
    """Route (a): a plan verified under `Profile.polars` runs natively."""
    t = con.table("t")
    report = sv.verify(
        t.select("k", m=t.i % t.j),
        requires={"t": [_.i.between(-100, 100), _.j.between(-100, 100), _.j != 0]},
        semantics="polars",
    )
    assert report.proved and report.semantics == "polars"
    out = report.run(con, "polars", route="auto")
    r = report.routes["polars"]
    assert (r.kind, r.profile, r.cls) == ("native", "polars", "refines")
    assert sorted(out.column("m").to_pylist(), key=lambda v: (v is None, v)) == sorted(
        i % j for i, j in zip(DIVIDENDS, DIVISORS, strict=True)
    )


@classes
def test_f2_duckdb_plan_transfers_to_polars(con) -> None:
    """Route (c) succeeds: double arithmetic allowed to reach `±∞`, verified
    under `Profile.duckdb`; on every option the proof uses, Polars's IEEE
    choices are within DuckDB's."""
    big = sv.connect()
    big.put("u", pa.table({"x": [1e200, 2.0, -3.0], "y": [1e200, 3.0, 0.5]}))
    report = sv.verify(
        "SELECT x * y AS z FROM u",
        tables={"u": big.table("u")},
        requires={"u": ["x BETWEEN -1e300 AND 1e300", "y BETWEEN -1e300 AND 1e300"]},
        semantics="duckdb",
    )
    assert report.proved, str(report)
    assert routes.choose(report, "duckdb").kind == "native"
    r = routes.choose(report, "polars")
    assert (r.kind, r.cls) == ("transfer", "refines"), r
    out = run_both(report, big)
    assert math.inf in out["polars"].column("z").to_pylist()


# Needs the engines' choices (the transfer check), not their classes: it holds
# from the DuckDB and Polars tables on (#587).
def test_f3_duckdb_null_order_is_refused_on_polars(con) -> None:
    """Route (c) fails: a sort read with DuckDB's default NULL order,
    verified under `Profile.duckdb`; Polars puts NULLs first, and the
    re-check under `Profile.polars` fails too. Refused, with the reason."""
    t = con.table("t")
    report = sv.verify(
        "SELECT k FROM t ORDER BY k",
        tables={"t": t},
        ensures=[sv.equivalent(rows="sequence")],
        semantics="duckdb",
    )
    assert report.proved, str(report)
    assert routes.choose(report, "duckdb").kind == "native"
    r = routes.choose(report, "polars")
    assert r.refused and r.cls == "refused"
    assert any(f["option"] == "null_order" for f in r.failures), r.failures
    assert "transfer check fails on" in r.reason and "Profile.polars" in r.reason
    with pytest.raises(RouteError, match="refused on polars"):
        report.run(con, "polars", route="auto")


@pytest.mark.skipif(
    routes.lean_transfer("reference", "reference", []) is None,
    reason="the checker has no --transfer yet (#444 3c)",
)
def test_f_lean_transfer_agrees(con) -> None:
    """The checker's transfer check is authoritative (D1); the Python
    lookup agrees with it on F2's and F3's plans."""
    t = con.table("t")
    for sql in ("SELECT k FROM t ORDER BY k", "SELECT i * 2 AS d FROM t"):
        report = sv.verify(sql, tables={"t": t}, semantics="duckdb")
        depends = (
            report.depends
            if report.depends is not None
            else routes.plan_options(json.loads(report.plan or "{}"))
        )
        lean = routes.lean_transfer("duckdb", "polars", depends)
        assert lean is not None, "substrait-check --transfer"
        mine = routes.transfer("duckdb", "polars", depends)
        assert mine is not None
        assert lean["ok"] == (not mine)
        if mine:
            assert lean["failures"][0]["option"] in {f["option"] for f in mine}


# -- G, H: refusals and versions ---------------------------------------------


def test_g1_md5_runs_on_duckdb_and_is_refused_on_polars(con) -> None:
    """Polars has no expression for `md5`: refused with the reason."""
    t = con.table("t")
    report = sv.verify(t.select(h=t.s.hexdigest("md5")))
    assert report.proved
    out = report.run(con, "duckdb", route="auto")
    assert out.column("h").to_pylist()[0] == "900150983cd24fb0d6963f7d28e17f72"
    assert report.routes["duckdb"].kind == "reference"
    r = routes.choose(report, "polars")
    assert r.refused and r.cls == "refused" and "#271" in r.reason
    with pytest.raises(RouteError, match="md5 is not yet supported on polars"):
        report.run(con, "polars", route="auto")


def test_h1_engine_versions(con, monkeypatch: pytest.MonkeyPatch) -> None:
    """Another minor version of Polars warns; another major is refused (D14)."""
    t = con.table("t")
    report = sv.verify(t.select("k"))
    monkeypatch.setattr(routes, "installed_version", lambda e: "2.2.0" if e == "polars" else None)
    with pytest.warns(routes.EngineVersionWarning, match="polars 2.2.0"):
        r = routes.choose(report, "polars")
    assert r.kind == "reference" and any("2.2.0" in w for w in r.warnings)
    monkeypatch.setattr(routes, "installed_version", lambda e: "3.0.0" if e == "polars" else None)
    with pytest.raises(routes.EngineVersionError, match="re-run the probes"):
        report.run(con, "polars", route="auto")
    assert routes.choose(report, "duckdb").kind == "reference"
