"""#444's prototype slice, end to end: one test per row of the expanded slice
(https://github.com/AlexanderNenninger/substrait-lean/issues/444#issuecomment-6633505268).

Each test verifies a plan, runs it on DuckDB and on Polars by the route
`sverify.routes.choose` picks (`docs/core-semantics.md`, "Which plans run on
an engine", D13), and asserts the route, the class (#568) and the result.

The class, `q` and shim columns of `Profile.duckdb`'s and
`Profile.polars`'s choices (steps 3a, 3b, D15) and the option dependency
report (3c) come from the checker. Rows that wait for more are expected
failures without strictness, with the reason. The F rows check
`Profile.polars` (`engines/polars/Sverify/Polars/Profile.lean`): a plan whose `%`
floors runs natively on Polars and is refused on DuckDB.
"""

from __future__ import annotations

import math

import ibis
import pyarrow as pa
import pytest
from ibis import _

import sverify as sv
from sverify import routes
from sverify.errors import PreconditionError, ProfilePendingWarning, RouteError

pytestmark = pytest.mark.filterwarnings("ignore::sverify.errors.ProfilePendingWarning")

ENGINES = ("duckdb", "polars")
DIVIDENDS = [-7, 2, 4, 3, -1, 5, 6]
DIVISORS = [2, -3, 3, -2, 2, 4, -4]


def waits_for(why: str) -> pytest.MarkDecorator:
    """The row needs more than the checker's tables give; `why` names it."""
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
    assert report.verdict == sv.Verdict.PROVED, str(report)
    out = run_both(report, con)
    assert sorted(out["duckdb"].column("mod").to_pylist()) == sorted(
        int(math.fmod(i, j)) for i, j in zip(DIVIDENDS, DIVISORS, strict=True)
    )
    assert route_of(report, "duckdb").kind == "translated"
    assert route_of(report, "duckdb").cls == "exact"
    assert route_of(report, "polars").kind == "translated"
    assert route_of(report, "polars").cls == "shim"


def test_a2_sum_of_a_bounded_int32(con) -> None:
    """Overflow proved absent from the bounds: no shim, no guard."""
    t = con.table("t")
    report = sv.verify(
        t.group_by("k").aggregate(total=t.n.sum()),
        requires={"t": [_.n.between(0, 1000), sv.max_rows(1_000_000)]},
    )
    assert report.verdict == sv.Verdict.PROVED and not report.assumed and not report.issues
    run_both(report, con)
    for e in ENGINES:
        assert route_of(report, e).kind == "translated"
        assert route_of(report, e).cls == "exact"


def test_a3_overflowing_batch_is_refused_before_the_run(con) -> None:
    """`SUM` of an unbounded `i64`: assumed to fit and checked on the data.
    A batch that overflows is refused before the plan runs, on both
    engines, with the precondition in the message.

    `i` may be NULL, and Polars sums a group of NULLs to 0 where the
    reference gives NULL: its translation shims `sum_empty_null`. With `i`
    NOT NULL in the preconditions no group is all NULL, and Polars refines."""
    t = con.table("t")
    report = sv.verify(t.group_by("k").aggregate(total=t.i.sum()))
    assert report.verdict == sv.Verdict.PROVED_WITH_CHECKS and [i.what for i in report.assumed] == [
        "i"
    ]
    run_both(report, con)
    assert route_of(report, "duckdb").cls == "exact"
    assert route_of(report, "polars").cls == "shim"
    assert any("sum_empty_null" in s for s in route_of(report, "polars").shims)
    present = sv.verify(t.group_by("k").aggregate(total=t.i.sum()), requires={"t": [_.i.notnull()]})
    assert present.verdict == sv.Verdict.PROVED_WITH_CHECKS, str(present)
    run_both(present, con)
    for e in ENGINES:
        assert route_of(present, e).cls == "exact"
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


def test_a4_double_product_that_may_reach_infinity(con) -> None:
    """`x * y` on doubles. Two conditions, kept apart (#1803): `0 * ±inf` is
    NaN, a domain error that only a bound on the columns rules out; and a
    product of finite values that overflows to `±∞` is assumed and checked on
    the data, so a verified run never yields a new `±∞`."""
    u = ibis.table({"x": "float64", "y": "float64"}, name="u")
    unbounded = sv.verify(u.select(z=u.x * u.y))
    assert unbounded.verdict == sv.Verdict.UNPROVED
    assert [i.kind for i in unbounded.issues] == ["domain error"]
    assert "0 times" in str(unbounded)
    finite = [_.x.between(-1e300, 1e300), _.y.between(-1e300, 1e300)]
    report = sv.verify(u.select(z=u.x * u.y), requires={"u": finite})
    assert report.verdict == sv.Verdict.PROVED_WITH_CHECKS, str(report)
    assert [i.kind for i in report.assumed] == ["overflow to infinity"]
    good = sv.connect()
    good.put("u", pa.table({"x": [2.0, -3.0], "y": [4.0, 0.5]}))
    out = run_both(report, good)
    assert all(math.isfinite(z) for z in out["polars"].column("z").to_pylist())
    for e in ("duckdb", "spark"):
        assert route_of(report, e).cls == "exact"
    # Polars is observed for any double product, proved outright or not: its
    # route reads `-0.0` as `0.0` (facts polars-zero-sign, polars-zero-add).
    proved = sv.verify(
        u.select(z=u.x * u.y),
        requires={"u": [_.x.between(-1e150, 1e150), _.y.between(-1e150, 1e150)]},
    )
    assert proved.verdict == sv.Verdict.PROVED
    assert route_of(proved, "polars").cls == route_of(report, "polars").cls == "observed"
    bad = sv.connect()
    bad.put("u", pa.table({"x": [1e200], "y": [1e200]}))
    for e in ENGINES:
        with pytest.raises(PreconditionError, match="refused before the run"):
            report.run(bad, e, route="auto")


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
        assert report.verdict == sv.Verdict.PROVED, str(report)
    assert sorted(run_both(rounded, ties)["polars"].column("r").to_pylist()) == [-2, 1, 3]
    assert sorted(run_both(mean, ties)["polars"].column("a").to_pylist()) == [1.5, 3.0]
    # DuckDB's `round(-0.4)` is `-0.0` (`round_zero_sign`): the default
    # observation reads one zero, so DuckDB runs it as written; an
    # observation that reads the signs gets the written plan's proved
    # template, which gives the reference's `0.0`. Polars shims the
    # rounding mode either way.
    assert route_of(rounded, "duckdb").cls == "observed"
    assert route_of(rounded, "polars").cls == "shim"
    signed = sv.verify(
        tt.select("k", r=tt.x.round()),
        requires=req,
        ensures=[sv.equivalent(floats="plan")],
    )
    assert route_of(signed, "duckdb").cls == "shim"
    assert route_of(signed, "polars").cls == "shim"
    assert mean._epsilon, "the plan's bound on the mean"
    assert route_of(mean, "duckdb").cls in ("exact", "observed")
    assert route_of(mean, "polars").cls == "observed"


# -- B: observations ---------------------------------------------------------


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
        assert report.verdict == sv.Verdict.PROVED, str(report)
        assert report._epsilon, "the plan's bound on the doubles"
        data = con if tolerance.abs is not None else _non_negative(con)
        run_both(report, data)
        assert route_of(report, "polars").cls == "observed", tolerance
        assert route_of(report, "duckdb").cls in ("exact", "observed")
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


def test_b2_group_by_a_double_key_with_zeros_and_nan(con) -> None:
    """`GROUP BY` a double holding `-0.0`, `0.0` and NaN: NaN equality is
    native, but Polars keeps the first zero it sees. Without
    `zeros="canon"` the q-refinement check refuses Polars (or writes the
    canon shim); with it, Polars refines up to `canon`."""
    z = sv.connect()
    z.put("d", pa.table({"x": [-0.0, 0.0, float("nan"), float("nan"), 1.0], "v": [1, 2, 3, 4, 5]}))
    d = z.table("d")
    expr = d.group_by("x").aggregate(n=d.v.count())
    exact = sv.verify(expr, ensures=[sv.equivalent(floats="plan")])
    assert exact.verdict == sv.Verdict.PROVED, str(exact)
    strict = routes.choose(exact, "polars")
    assert (strict.refused and "zeros" in strict.reason) or strict.cls == "shim", strict
    canon = sv.verify(expr, ensures=[sv.equivalent(zeros="canon")])
    out = run_both(canon, z)
    assert sorted(out["polars"].column("n").to_pylist()) == [1, 2, 2]
    assert route_of(canon, "polars").cls == "observed"
    assert route_of(canon, "duckdb").cls in ("exact", "observed")


# -- C: order and NULLs ------------------------------------------------------


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
        assert route_of(report, e).cls == "exact"


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
    assert '"SORT_DIRECTION_UNSPECIFIED"' in (report.internal_plan or "") or "UNSPECIFIED" in (
        report.internal_plan or ""
    )
    out = run_both(report, con)
    assert out["polars"].column("k").to_pylist()[-2:] == [None, None]
    assert route_of(report, "duckdb").cls == "exact"
    assert route_of(report, "polars").cls == "shim"


def test_c3_limit_over_ties_is_reported_and_refused_where_required(con) -> None:
    """A sort with ties, then `LIMIT`: which tied rows survive is open.
    The report says so, the route warns, and a run that must be repeatable
    (an idempotent sink's epoch) is refused."""
    t = con.table("t")
    report = sv.verify(t.order_by("k").limit(2))
    assert report.verdict == sv.Verdict.PROVED and not report.deterministic
    r = routes.choose(report, "polars")
    assert r.kind == "translated" and not r.deterministic and r.warnings
    with pytest.raises(RouteError, match="rerun must give the same result"):
        report.run(con, "polars", route="auto", reproducible=sv.equivalent())


def test_c4_join_on_keys_with_nulls(con) -> None:
    """`=` skips NULL keys on both engines, as in the reference."""
    t = con.table("t")
    other = t.select(k2="k", m="n")
    report = sv.verify(t.join(other, t.k == other.k2).select("k", "i", "m"))
    out = run_both(report, con)
    assert None not in out["polars"].column("k").to_pylist()
    for e in ENGINES:
        assert route_of(report, e).cls == "exact"


# -- D: open options ---------------------------------------------------------


@waits_for(
    "the checker proves conditions over every pick and element order (D24), but its "
    "abstract values relate no FIRST to its group's MAX, nor a collected list's length to "
    "its group's rows"
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
    assert report.verdict == sv.Verdict.PROVED, str(report)
    run_both(report, con, sv.equivalent(elements="multiset"))
    for e in ENGINES:
        assert route_of(report, e).kind == "translated"
        assert route_of(report, e).cls in ("exact", "observed")
    reads = sv.verify(expr, requires=req, ensures=[q, _.f == _.mx, _.l[0] <= _.mx])
    assert {c.label: c.ignores for c in reads.ensures} == {
        "(_.f == _.mx)": ("picks",),
        "(_.l[0] <= _.mx)": ("elements",),
    }
    assert routes.choose(reads, "polars").refused


# -- E: strings --------------------------------------------------------------


def test_e1_substring_with_a_negative_start_and_strpos(con) -> None:
    """Polars counts from 0, in bytes for `strpos`, and gives NULL where
    `strpos` gives 0: the translation rewrites both."""
    t = con.table("t")
    report = sv.verify(
        "SELECT substring(s, -2, 2) AS tail, strpos(s, 'b') AS at FROM t",
        tables={"t": t},
    )
    assert report.verdict == sv.Verdict.PROVED, str(report)
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
    assert route_of(report, "duckdb").cls == "exact"
    assert route_of(report, "polars").cls == "shim"


# -- F: routes between profiles ----------------------------------------------


def _floor_report(con, **kw) -> sv.Report:
    """`i % j` and `i // j` requested under `semantics="polars"`, which the
    checker reports as pending until #271: the report is the reference's. The
    producer still states `division_type: FLOOR`, which the core reads as the
    floored `//` and `%`."""
    t = con.table("t")
    return sv.verify(
        t.select("k", m=t.i % t.j, q=t.i // t.j),
        requires={"t": [_.i.between(-100, 100), _.j.between(-100, 100), _.j != 0]},
        semantics="polars",
        **kw,
    )


def test_f1_a_polars_request_runs_translated_on_polars(con) -> None:
    """Route (a): the request is reported under the reference (#271), so the
    plan reaches Polars by the translation, which computes the stated `FLOOR`."""
    with pytest.warns(ProfilePendingWarning):
        report = _floor_report(con)
    assert report.verdict == sv.Verdict.PROVED and report.semantics == "reference", str(report)
    out = report.run(con, "polars", route="auto")
    r = report.routes["polars"]
    assert (r.kind, r.profile) == ("translated", "reference")
    pairs = list(zip(DIVIDENDS, DIVISORS, strict=True))
    assert sorted(out.column("m").to_pylist()) == sorted(i % j for i, j in pairs)
    assert sorted(out.column("q").to_pylist()) == sorted(i // j for i, j in pairs)


def test_f1b_the_same_report_runs_translated_on_duckdb(con) -> None:
    """The report is the reference's, so DuckDB takes it by the translation too."""
    report = _floor_report(con)
    r = routes.choose(report, "duckdb")
    assert r.kind == "translated", r
    out = report.run(con, "duckdb", route="auto")
    pairs = list(zip(DIVIDENDS, DIVISORS, strict=True))
    assert sorted(out.column("m").to_pylist()) == sorted(i % j for i, j in pairs)
    assert sorted(out.column("q").to_pylist()) == sorted(i // j for i, j in pairs)


def test_f1d_zero_divisor_is_a_precondition_under_a_polars_request(con) -> None:
    """Polars gives NULL for `i % 0`; the reference raises there (D21), so
    `verify` infers `j != 0` and checks it on the data before the run."""
    t = con.table("t")
    report = sv.verify(t.select(m=t.i % t.j), semantics="polars", on_inferred="ignore")
    assert report.verdict == sv.Verdict.PROVED, str(report)
    assert report._inferred == {"t": ['"j" IS NULL OR "j" <> 0']}, report._inferred
    bad = sv.connect()
    bad.put("t", con.get("t").set_column(2, "j", pa.array([0] * 7, pa.int64())))
    with pytest.raises(PreconditionError, match="refused before the run"):
        report.run(bad, "polars", route="auto")


def test_f1e_recheck_is_unavailable_for_polars_until_271(con) -> None:
    """Route (d): the checker cannot prove again under `Profile.polars` yet."""
    t = con.table("t")
    report = sv.verify(
        t.select("k", m=t.i % t.j),
        requires={"t": [_.i.between(-100, 100), _.j.between(-100, 100), _.j != 0]},
    )
    ok, why = routes.recheck(report, "polars")
    assert not ok and 'semantics="polars"' in why
    out = report.run(con, "polars")
    assert report.routes["polars"].kind == "translated"
    assert sorted(out.column("m").to_pylist()) == sorted(
        int(math.fmod(i, j)) for i, j in zip(DIVIDENDS, DIVISORS, strict=True)
    )


def test_f2_duckdb_plan_is_refused_on_polars_until_271(con) -> None:
    """Double arithmetic allowed to reach `±∞`, verified under `Profile.duckdb`:
    DuckDB's `zero_sign` is `ONE_ZERO` and Polars's `IEEE`, so the transfer
    check fails, and the re-check under Polars's profile waits for #271."""
    big = sv.connect()
    big.put("u", pa.table({"x": [1e200, 2.0, -3.0], "y": [1e200, 3.0, 0.5]}))
    report = sv.verify(
        "SELECT x * y AS z FROM u",
        tables={"u": big.table("u")},
        requires={"u": ["x BETWEEN -1e300 AND 1e300", "y BETWEEN -1e300 AND 1e300"]},
        semantics="duckdb",
    )
    assert report.verdict == sv.Verdict.PROVED, str(report)
    assert routes.choose(report, "duckdb").kind == "native"
    r = routes.choose(report, "polars")
    assert r.refused and "semantics='reference'" in r.reason, r
    assert math.inf in report.run(big, "duckdb").column("z").to_pylist()


# Needs the engines' choices (the transfer check), not their classes: it holds
# from the DuckDB and Polars tables on (#587).
def test_f3_duckdb_null_order_stated_transfers(con) -> None:
    """Route (c): a sort read with DuckDB's NULL order, verified under
    `Profile.duckdb`. The lift states `NULLS LAST`, and Polars gives a stated
    placement as stated, so the checker's transfer check (`transferB` over the
    plan's reads with their preferences, `Rel.transfer_of_transferB`) passes
    on `null_order`, and the run puts the NULLs last (#1166)."""
    t = con.table("t")
    report = sv.verify(
        "SELECT k FROM t ORDER BY k",
        tables={"t": t},
        ensures=[sv.equivalent(rows="sequence")],
        semantics="duckdb",
    )
    assert report.verdict == sv.Verdict.PROVED, str(report)
    assert routes.choose(report, "duckdb").kind == "native"
    taken = routes.choose(report, "polars", route="transfer")
    assert not taken.refused, taken.reason
    assert routes.choose(report, "polars").kind == "transfer"
    out = report.run(con, "polars", route="auto")
    assert out.column("k").to_pylist()[-2:] == [None, None]


# -- G, H: refusals and versions ---------------------------------------------


def test_g1_md5_runs_on_duckdb_and_is_refused_on_polars(con) -> None:
    """Polars has no expression for `md5`: refused with the reason."""
    t = con.table("t")
    report = sv.verify(t.select(h=t.s.hexdigest("md5")))
    assert report.verdict == sv.Verdict.PROVED
    out = report.run(con, "duckdb", route="auto")
    assert out.column("h").to_pylist()[0] == "900150983cd24fb0d6963f7d28e17f72"
    assert report.routes["duckdb"].kind == "translated"
    r = routes.choose(report, "polars")
    assert r.refused and r.cls == "refused" and "#271" in r.reason
    with pytest.raises(RouteError, match=r"hexdigest\('md5'\) \(SQL md5\) runs on duckdb only"):
        report.run(con, "polars", route="auto")


def test_h1_engine_versions(con, monkeypatch: pytest.MonkeyPatch) -> None:
    """Another minor version of Polars warns; another major is refused (D14)."""
    t = con.table("t")
    report = sv.verify(t.select("k"))
    monkeypatch.setattr(routes, "installed_version", lambda e: "2.2.0" if e == "polars" else None)
    with pytest.warns(routes.EngineVersionWarning, match="polars 2.2.0"):
        r = routes.choose(report, "polars")
    assert r.kind == "translated" and any("2.2.0" in w for w in r.warnings)
    monkeypatch.setattr(routes, "installed_version", lambda e: "3.0.0" if e == "polars" else None)
    with pytest.raises(routes.EngineVersionError, match="install a 2.x release of polars"):
        report.run(con, "polars", route="auto")
    assert routes.choose(report, "duckdb").kind == "translated"
