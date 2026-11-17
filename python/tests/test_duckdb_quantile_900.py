"""#900: the written `quantile_cont` stays in the model's neighbours.

DuckDB 2.0.0 computes `RN = (n - 1)·q` in doubles and interpolates
`lo·(1 - d) + hi·d`, which leaves the model's neighbours (`contAllowed`, exact
`q`) at a whole exact position the double misses, and where the lower
neighbour is the first value (`duckdb-quantile-cont-interpolation`). The
written plan (`DuckDBDialect.quantile`) guards both; each case here is a
membership test of its result against the model.
"""

import math
import random
from dataclasses import replace
from fractions import Fraction

import duckdb
import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st

from sverify.sql.core import Unsupported
from sverify_duckdb.dialect import DUCKDB

pytestmark = pytest.mark.backend("duckdb")

CON = duckdb.connect()
CON.execute("SET threads=1")


def neighbours(values: list[float], q: Fraction) -> tuple[float, float]:
    s = sorted(values, key=lambda v: (math.isnan(v), v))  # NaN sorts last
    p = (len(s) - 1) * q
    return s[math.floor(p)], s[math.ceil(p)]


def written(values: list[float], q: str) -> float:
    CON.execute("CREATE OR REPLACE TEMP TABLE t(x DOUBLE)")
    CON.executemany("INSERT INTO t VALUES (?)", [(v,) for v in values])
    return CON.execute(f"SELECT {DUCKDB.quantile(True, 'x', q)} FROM t").fetchall()[0][0]


def allowed(values: list[float], q: str, got: float) -> bool:
    lo, hi = neighbours(values, Fraction(q))
    # The model's order puts NaN above every number (`contAllowedOf`).
    key = lambda v: (math.isnan(v), 0.0 if math.isnan(v) else v)  # noqa: E731
    return key(lo) <= key(got) <= key(hi)


def whole_missed(limit: int = 2000):
    """(n, q) whose exact position is whole and whose double is not: 388 below 2000."""
    for n in range(2, limit):
        for num in range(1, 100):
            if ((n - 1) * num) % 100 == 0 and (n - 1) * (num / 100) != ((n - 1) * num) // 100:
                yield n, f"0.{num:02d}"


def written_sql(source: str, q: str) -> float:
    """The written quantile of the column `x` of the SQL `source`."""
    return CON.execute(f"SELECT {DUCKDB.quantile(True, 'x', q)} FROM ({source}) s(x)").fetchall()[
        0
    ][0]


def test_the_whole_positions_the_double_misses_give_the_model_value():
    cases = list(whole_missed())
    assert len(cases) == 388
    for n, q in cases:
        m = ((n - 1) * int(q[2:])) // 100
        # 1.0 up to the position, 1e300 after: the unguarded value is 1e285.
        step = (
            f"SELECT CASE WHEN i <= {m} THEN 1.0::DOUBLE ELSE 1e300::DOUBLE END "
            f"FROM range({n}) r(i)"
        )
        assert written_sql(step, q) == 1.0, (n, q)
        ramp = f"SELECT CAST(i AS DOUBLE) FROM range({n}) r(i)"
        assert written_sql(ramp, q) == float(m), (n, q)


def test_a_lower_neighbour_that_is_first_stays_between_the_neighbours():
    rng = random.Random(900)
    for k in (0, 1):
        for q in ("0.05", "0.1", "0.15", "0.2", "0.3", "0.33", "0.37", "0.4", "0.45", "0.49"):
            for _ in range(300):
                c = rng.uniform(0.1, 10.0) * 10.0 ** rng.choice((-300, -5, 0, 7, 300))
                hi = c if k == 0 else math.nextafter(c, math.inf)
                values = [c, hi, 4 * c]
                rng.shuffle(values)
                assert allowed(values, q, written(values, q)), (values, q)


@settings(max_examples=150, deadline=None, suppress_health_check=[HealthCheck.too_slow])
@given(
    st.lists(
        st.floats(min_value=-1e300, max_value=1e300, allow_nan=False), min_size=2, max_size=40
    ),
    st.integers(min_value=1, max_value=99),
)
def test_a_random_group_stays_between_the_neighbours(values, num):
    q = f"0.{num:02d}"
    assert allowed(values, q, written(values, q))


def test_a_dyadic_fraction_needs_no_guard():
    sql = DUCKDB.quantile(True, "x", "0.25")
    assert "quantile_disc" not in sql and "min(x, 2)" not in sql
    assert "quantile_disc" in DUCKDB.quantile(True, "x", "0.28")


def band_of(n1: int, q: Fraction) -> tuple[bool, int, int]:
    """(in the band, k, nearest whole position m) of the position `n1·q`."""
    k, r = divmod(n1 * q.numerator, q.denominator)
    d = min(r, q.denominator - r)
    return d <= (n1 * q.denominator) // 2**51, k, k if 2 * r < q.denominator else k + 1


def test_the_band_arithmetic():
    """Outside the band the double position's floor and ceiling are the exact ones; in it
    and below the count limit the shifted `quantile_disc` index is the nearest whole
    position, which the engine's pair holds."""
    rng = random.Random(900)
    eps = Fraction(1, 10**15)
    seen = {"band": 0, "outside": 0}
    for _ in range(30_000):
        scale = rng.randint(2, 21)
        den0 = 10**scale
        n1 = rng.choice((rng.randint(1, 60), rng.randint(1, 10**14 - 1)))
        num0 = rng.choice((rng.randint(1, den0 - 1), rng.randint(1, 20), den0 - rng.randint(1, 20)))
        q = Fraction(num0, den0)
        if q.denominator & (q.denominator - 1) == 0:
            continue
        band, k, m = band_of(n1, q)
        rn = float(n1) * (q.numerator / q.denominator)
        pair = (math.floor(rn), math.ceil(rn))
        if not band:
            seen["outside"] += 1
            assert pair == (k, k + 1), (n1, q)
            continue
        seen["band"] += 1
        assert m in pair, (n1, q)
        n = n1 + 1
        shifted = q + eps if 2 * q < 1 else q - eps
        assert max(1, math.ceil(n * shifted)) - 1 == m, (n1, q)
    assert seen["band"] > 100 and seen["outside"] > 100


BAND_QS = tuple(
    f"0.{num:0{scale}d}"
    for scale in (16, 18, 21)
    for num in (1, 2, 3, 7, 10**scale - 1, 10**scale - 4)
)


@settings(max_examples=150, deadline=None, suppress_health_check=[HealthCheck.too_slow])
@given(
    st.lists(
        st.one_of(
            st.floats(min_value=-1e300, max_value=1e300),
            st.sampled_from([-math.inf, math.inf, math.nan]),
        ),
        min_size=2,
        max_size=12,
    ),
    st.sampled_from(BAND_QS),
)
def test_a_group_with_a_position_in_the_band_stays_between_the_neighbours(values, q):
    lo, hi = neighbours(values, Fraction(q))
    p = (len(values) - 1) * Fraction(q)
    if lo == -math.inf and hi == math.inf and p.denominator != 1:
        with pytest.raises(duckdb.Error, match="domain"):
            written(values, q)
    else:
        assert allowed(values, q, written(values, q))


def test_the_domain_error_in_the_band():
    q = "0.9999999999999999"
    with pytest.raises(duckdb.Error, match="domain"):
        written([-math.inf, math.inf], q)
    # Both infinities in the group, but the neighbours at the fractional position are +inf.
    assert written([-math.inf, math.inf, math.inf], q) == math.inf
    # Without the guards the engine's own value comes back.
    sql = replace(DUCKDB, guards=False).quantile(True, "x", q)
    CON.execute(f"SELECT {sql} FROM (VALUES ('-inf'::DOUBLE), ('inf'::DOUBLE)) s(x)").fetchall()


def test_a_third_at_scale_16_is_not_refused():
    # Ibis prints `quantile(1/3)` at scale 16; it was refused from n = 2.
    assert written([1.0, 2.0], "0.3333333333333333") == pytest.approx(1.3333333333333333)


def test_more_than_21_decimals_are_refused_when_written():
    with pytest.raises(Unsupported, match="21"):
        DUCKDB.quantile(True, "x", "0.1234567890123456789012")
    DUCKDB.quantile(True, "x", "0.123456789012345678901")
    DUCKDB.quantile(True, "x", "0.500000000000000000000000")  # dyadic


def test_the_count_limit_stays_without_guards():
    # An engine limit, which `guard_free` cannot prove absent. 10^14 rows do not fit a test:
    # lower the limit in the written SQL.
    sql = replace(DUCKDB, guards=False).quantile(True, "x", "0.3333333333333333")
    assert str(10**14) in sql
    with pytest.raises(duckdb.Error, match="quantile count"):
        CON.execute(
            f"SELECT {sql.replace(str(10**14), '2')} FROM (VALUES (1.0), (2.0), (3.0)) s(x)"
        ).fetchall()
