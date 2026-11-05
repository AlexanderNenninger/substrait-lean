"""Error bounds for aggregates of doubles (#85, `docs/float-bounds.md`).

* The bounds proved in `float-bounds/` hold of DuckDB's results on adversarial
  inputs: cancellation, large and small magnitudes, many rows. `SUM` and `AVG`
  are within `γ` of the exact sum and mean (DuckDB adds in parallel, so the
  sharded bound applies), `VAR_*`/`STDDEV_*` within the generic co-moment
  bound `64 · n² · u · B²`, whatever algorithm DuckDB uses.
* With a row cap (`sv.max_rows`), the checker bounds `SUM` and `AVG` of
  doubles by the proved tolerance: `sv.approx(_.avg <= 100)` proves where the
  exact `_.avg <= 100` does not, and signs are exact without a cap.
"""

import math
import re
from fractions import Fraction
from pathlib import Path

import duckdb
import ibis
import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st
from ibis import _

import sverify as sv
from _pipelines import bound_orders
from sverify.errors import PreconditionError

U = Fraction(1, 2**53)
TINY = Fraction(1, 2**1022)


def gamma(n: int) -> Fraction:
    return n * U / (1 - n * U)


def exact(xs: list[float]) -> tuple[Fraction, Fraction]:
    """The exact sum and `Σ (|x| + tiny)`."""
    return sum((Fraction(x) for x in xs), Fraction(0)), sum(
        (abs(Fraction(x)) + TINY for x in xs), Fraction(0)
    )


magnitudes = st.sampled_from([1e-300, 1e-12, 1.0, 1e9, 1e100, 1e300])
values = st.floats(min_value=-1.0, max_value=1.0, allow_nan=False, allow_subnormal=True)


@st.composite
def adversarial(draw: st.DrawFn) -> list[float]:
    """Doubles that stress rounding: one magnitude or several, with
    cancelling pairs and subnormals, up to a few thousand rows."""
    scale = draw(magnitudes)
    xs = [x * scale for x in draw(st.lists(values, min_size=1, max_size=60))]
    if draw(st.booleans()):
        # Cancellation: large values that cancel, around small ones.
        big = draw(st.sampled_from([1e16, 1e200]))
        xs = [big, *xs, -big]
    if draw(st.booleans()):
        xs = xs * draw(st.integers(1, 80))
    return xs


def duckdb_aggregates(xs: list[float]) -> tuple[float, float, float | None, float | None]:
    con = duckdb.connect()
    con.execute("CREATE TABLE t (x DOUBLE)")
    con.executemany("INSERT INTO t VALUES (?)", [(x,) for x in xs])
    row = con.execute("SELECT SUM(x), AVG(x), VAR_POP(x), STDDEV_POP(x) FROM t").fetchone()
    assert row is not None
    return row


@settings(max_examples=60, deadline=None, suppress_health_check=[HealthCheck.too_slow])
@given(xs=adversarial())
def test_duckdb_meets_the_proved_bounds(xs: list[float]) -> None:
    n = len(xs)
    s, mag = exact(xs)
    got_sum, got_avg, got_var, got_sd = duckdb_aggregates(xs)
    # Any split into k ≤ n shards of at most n values: γ (n + k) · (mag + k · tiny).
    assert abs(Fraction(got_sum) - s) <= gamma(2 * n) * (mag + n * TINY)
    assert abs(Fraction(got_avg) - s / n) <= gamma(2 * n + 2) * (mag + n * TINY) / n
    # The co-moment bound, whatever the algorithm, then one division, for
    # values up to 2⁴⁰⁰ (`Scale`; above, the squares may overflow).
    b = max(max(abs(Fraction(x)) for x in xs), Fraction(1, 2**500))
    if b > 2**400:
        return
    mean = s / n
    sxx = sum(((Fraction(x) - mean) ** 2 for x in xs), Fraction(0))
    e = 64 * n**2 * U * b**2
    tol_var = e / n + 3 * U * 4 * n * b**2 / n
    assert got_var is not None and abs(Fraction(got_var) - sxx / n) <= tol_var
    # STDDEV: within √E + u (√V + √E + tiny), here with `√` from above.
    assert got_sd is not None
    sd = math.sqrt(sxx / n)
    assert abs(got_sd - sd) <= math.sqrt(tol_var) * (1 + 1e-12) + 1e-300 + 2 * float(U) * (
        sd + math.sqrt(tol_var)
    )


def kahan(xs: list[float]) -> float:
    """Polars's `KahanSum` (polars-sum-float): the running sum, without the
    compensation."""
    s = c = 0.0
    for x in xs:
        y = x - c
        t = s + y
        c = (t - s) - y
        s = t
    return s


@settings(max_examples=60, deadline=None)
@given(xs=adversarial())
def test_kahan_meets_the_tree_bound(xs: list[float]) -> None:
    """`Rnd.kahan_near`: Kahan's sum is within the sequential sum's bound
    `γ n · Σ (|x| + tiny)`, as a tree sum is."""
    s, mag = exact(xs)
    assert abs(Fraction(kahan(xs)) - s) <= gamma(len(xs)) * mag
    assert abs(Fraction(kahan(xs[:3])) - exact(xs[:3])[0]) <= gamma(len(xs[:3])) * exact(xs[:3])[1]


def test_rows_cite_theorems_float_bounds_has() -> None:
    """The core cannot see `float-bounds`' theorems: the names its engine rows
    cite (`floatBoundsTheorems`) are the ones `float-bounds` checks exist."""
    root = Path(__file__).resolve().parents[2]
    core = (root / "SubstraitLean" / "EngineTables.lean").read_text()
    names = re.compile(r'"(FloatBounds\.[\w.]+)"')
    cited = core[core.index("def floatBoundsTheorems") :].split("\n\n")[0]
    checked = "".join(
        (root / "float-bounds" / "FloatBounds" / f).read_text().split("run_cmd do")[1]
        for f in ("Epsilon.lean", "ChanCorr.lean")
    )
    assert set(names.findall(cited)) == set(names.findall(checked)) != set()


def test_cancellation_is_within_the_bound_but_not_exact() -> None:
    xs = [1e16, 1.0, -1e16] * 10
    got_sum, *_ = duckdb_aggregates(xs)
    s, mag = exact(xs)
    assert Fraction(got_sum) != s
    assert abs(Fraction(got_sum) - s) <= gamma(2 * len(xs)) * mag


metrics = ibis.table({"host": "string", "cpu": "float64"}, name="metrics")
rollup = metrics.group_by("host").aggregate(
    cpu_avg=metrics.cpu.mean(), cpu_sum=metrics.cpu.sum(), cpu_max=metrics.cpu.max()
)
CPU = [_.cpu >= 0, _.cpu <= 100, _.cpu.notnull()]


def test_averages_within_0_to_100_are_proved_up_to_rounding() -> None:
    report = sv.verify(
        rollup,
        requires={"metrics": [*CPU, sv.max_rows(10_000_000)]},
        ensures=[
            _.cpu_avg >= 0,
            sv.approx(_.cpu_avg <= 100),
            sv.approx(_.cpu_sum <= 1_000_000_000),
            _.cpu_sum >= 0,
            _.cpu_avg <= 100.001,
        ],
    )
    assert report.proved, str(report)


def test_exact_claims_that_rounding_breaks_are_not_proved() -> None:
    report = sv.verify(
        rollup,
        requires={"metrics": [*CPU, sv.max_rows(10_000_000)]},
        ensures=[_.cpu_avg <= 100, sv.approx(_.cpu_avg <= 100, rel=1e-20), _.cpu_avg <= 99],
    )
    assert [c.proved for c in report.ensures] == [False, False, False]
    # The first misses only by rounding, and the report says so.
    [hint] = [h for h in report.hints if "rounding" in h]
    assert hint.startswith("(_.cpu_avg <= 100) holds up to rounding") and "sv.approx" in hint


def test_without_a_row_cap_only_signs_are_proved() -> None:
    report = sv.verify(
        rollup,
        requires={"metrics": CPU},
        ensures=[_.cpu_avg >= 0, _.cpu_sum >= 0, sv.approx(_.cpu_avg <= 100)],
    )
    assert [c.proved for c in report.ensures] == [True, True, False]


def test_a_cap_too_large_for_the_bound_proves_nothing() -> None:
    report = sv.verify(
        rollup,
        requires={"metrics": [*CPU, sv.max_rows(2**40)]},
        ensures=[sv.approx(_.cpu_avg <= 100)],
    )
    assert not report.proved


def test_negative_values_keep_their_sign() -> None:
    t = ibis.table({"k": "int64", "x": "float64"}, name="t")
    report = sv.verify(
        t.group_by("k").aggregate(s=t.x.sum(), a=t.x.mean()),
        requires={"t": [_.x <= 0, _.x.notnull()]},
        ensures=[_.s <= 0, _.a <= 0],
    )
    assert report.proved, str(report)


def test_approx_rewrites_comparisons() -> None:
    t = ibis.table({"x": "float64"}, name="t")
    relaxed = sv.approx((_.x <= 100) & (_.x > -5) | (_.x == 0), rel=1e-3)(t)
    sql = ibis.to_sql(t.filter(relaxed), dialect="duckdb")
    assert "100.1" in sql and "-5.005" in sql
    assert "approx" in sv.contracts.label(sv.approx(_.x <= 100))
    with pytest.raises(TypeError):
        sv.approx("x <= 100")
    with pytest.raises(TypeError):
        sv.approx(_.x.isnull())(t)


def test_max_rows_is_checked_on_the_data() -> None:
    @sv.transform(requires={"orders": [sv.max_rows(1)]}, ensures=[_.n >= 0])
    def count(orders):
        return orders.aggregate(n=orders.id.count())

    with pytest.raises(PreconditionError, match="max_rows"):
        count(bound_orders([(1, "ada", 30), (2, "bob", 40)]))
    count(bound_orders([(1, "ada", 30)]))


def test_truncating_a_bounded_average_is_exact() -> None:
    """The cast of a double carries its tolerance: `[0, 100.0000001]` casts to
    `[0, 100]`."""
    g = metrics.group_by("host").aggregate(cpu_avg=metrics.cpu.mean())
    report = sv.verify(
        g.select(c=g.cpu_avg.cast("int64")),
        requires={"metrics": [*CPU, sv.max_rows(10_000_000)]},
        ensures=[_.c >= 0, _.c <= 100],
    )
    assert report.proved, str(report)


def test_sums_and_means_of_converted_integers() -> None:
    """`SUM(CAST(x AS DOUBLE))` and Ibis' mean of integers: the conversion is
    exact up to 2⁵³, and the summation bound applies to the converted values."""
    t = ibis.table({"host": "string", "cpu": "int64"}, name="t")
    g = t.group_by("host").aggregate(s=t.cpu.cast("float64").sum(), m=t.cpu.mean())
    report = sv.verify(
        g,
        requires={"t": [_.cpu >= 0, _.cpu <= 100, _.cpu.notnull(), sv.max_rows(10_000_000)]},
        ensures=[_.s >= 0, sv.approx(_.s <= 1_000_000_000), _.m >= 0, sv.approx(_.m <= 100)],
    )
    assert report.proved, str(report)


pairs = st.lists(st.tuples(values, values), min_size=2, max_size=40)
TINY = Fraction(1, 2**1022)


def sqrt_up(q: Fraction) -> Fraction:
    """A rational at least `√q`, for the witnesses of `StatProps`."""
    k = 2**40
    return Fraction(math.isqrt(q.numerator * q.denominator * k * k) + 1, q.denominator * k)


@settings(max_examples=60, deadline=None, suppress_health_check=[HealthCheck.too_slow])
@given(ps=pairs, scale=magnitudes, shift=st.sampled_from([0.0, 1.0, 1e6]))
def test_duckdb_var_covar_and_corr_have_the_generic_properties(
    ps: list[tuple[float, float]], scale: float, shift: float
) -> None:
    """`StatProps` (`SubstraitLean/StatProps.lean`): `VAR_POP` within `varTol`,
    `COVAR_POP` within `covTol`, `|CORR| ≤ 1 + 3E/L + 8u` (`corrErr`) when both
    co-moments are at least `L ≥ 8E`, with the square roots by rational
    witnesses above them. The bounds scale with the spread, so a shift of
    `10⁶` keeps them small."""
    ps = [(x * scale + shift, y * scale - shift) for x, y in ps]
    n = len(ps)
    con = duckdb.connect()
    con.execute("CREATE TABLE t (x DOUBLE, y DOUBLE)")
    con.executemany("INSERT INTO t VALUES (?, ?)", ps)
    row = con.execute("SELECT VAR_POP(x), COVAR_POP(y, x), CORR(y, x) FROM t").fetchone()
    assert row is not None
    var, cov, corr = row
    xs, ys = [Fraction(x) for x, _ in ps], [Fraction(y) for _, y in ps]
    if max(abs(v) for v in xs + ys) > 2**398:
        return

    def comoment(a: list[Fraction], c: list[Fraction]) -> Fraction:
        sa, sc = sum(a, Fraction(0)), sum(c, Fraction(0))
        return sum((p * q for p, q in zip(a, c, strict=True)), Fraction(0)) - sa * sc / n

    def qsum(a: list[Fraction]) -> Fraction:
        return sum(((abs(v) + TINY) ** 2 for v in a), Fraction(0))

    sx, sy, c = comoment(xs, xs), comoment(ys, ys), comoment(xs, ys)
    qx, qy = qsum(xs), qsum(ys)
    second = n**2 * U * TINY
    var_tol = (160 * n * U * sqrt_up(qx * sx) + 3970 * n**2 * U**2 * qx + 800 * second) / n
    assert abs(Fraction(var) - sx / n) <= var_tol
    cov_tol = (
        71 * n * U * (sqrt_up(qx * sy) + sqrt_up(qy * sx))
        + 15 * n * U * sqrt_up(sx * sy)
        + 3970 * n**2 * U**2 * sqrt_up(qx * qy)
        + 800 * second
    ) / n
    assert abs(Fraction(cov) - c / n) <= cov_tol
    r = max(sqrt_up(a * b) for a in (qx, qy, sx) for b in (sx, sy))
    e = 447 * n * U * r + 11883 * n**2 * U**2 * (qx + qy) + 2379 * second
    low = min(sx, sy)
    if corr is not None and not math.isnan(corr) and low >= 8 * e and sx * sy <= 2**1000:
        assert abs(Fraction(corr)) <= 1 + 3 * e / low + 8 * U


hosts = ibis.table({"host": "string", "cpu": "float64", "n": "int64"}, name="hosts")
HOSTS = [*CPU, _.n >= 0, _.n <= 1000, _.n.notnull(), sv.max_rows(10_000_000)]


def test_casts_of_rounded_aggregates_keep_their_bounds() -> None:
    # The cast truncates both ends of the error bound, and fits.
    rolled = hosts.group_by("host").aggregate(
        a=hosts.cpu.mean(), s=hosts.n.cast("float64").sum(), av=hosts.n.cast("float64").mean()
    )
    casts = rolled.mutate(
        ai=_.a.cast("int64"),
        avi=_.av.cast("int64"),
        si=_.s.cast("int64"),
        ad=_.a.cast("decimal(6, 2)"),
    )
    report = sv.verify(
        casts,
        requires={"hosts": HOSTS},
        ensures=[
            _.ai >= 0,
            _.ai <= 100,
            _.avi <= 1000,
            sv.approx(_.s <= 10_000_000_000),
            sv.approx(_.av <= 1000),
            _.ad <= 100.01,
        ],
    )
    assert report.proved, str(report)
    assert not report.issues
    # Rounding can take the sum past the exact bound, and its cast with it.
    loose = sv.verify(casts, requires={"hosts": HOSTS}, ensures=[_.si <= 10_000_000_000])
    assert not loose.proved


def test_casts_of_rounded_aggregates_need_a_cap() -> None:
    capless = [c for c in HOSTS if not isinstance(c, sv.contracts.MaxRows)]
    rolled = hosts.group_by("host").aggregate(ai=hosts.cpu.mean().cast("int64"))
    report = sv.verify(rolled, requires={"hosts": capless}, ensures=[_.ai >= 0])
    assert [i.kind for i in report.issues] == ["cast out of range"]


def test_a_decimal_too_narrow_for_the_bound_may_overflow() -> None:
    rolled = hosts.group_by("host").aggregate(ad=hosts.cpu.mean().cast("decimal(4, 2)"))
    report = sv.verify(rolled, requires={"hosts": HOSTS}, ensures=[])
    assert report.issues and not report.proved
