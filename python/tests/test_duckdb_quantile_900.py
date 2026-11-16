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
from fractions import Fraction

import duckdb
import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st

from sverify_duckdb.dialect import DUCKDB

pytestmark = pytest.mark.backend("duckdb")

CON = duckdb.connect()
CON.execute("SET threads=1")


def neighbours(values: list[float], q: Fraction) -> tuple[float, float]:
    s = sorted(values)
    p = (len(s) - 1) * q
    return s[math.floor(p)], s[math.ceil(p)]


def written(values: list[float], q: str) -> float:
    CON.execute("CREATE OR REPLACE TEMP TABLE t(x DOUBLE)")
    CON.executemany("INSERT INTO t VALUES (?)", [(v,) for v in values])
    return CON.execute(f"SELECT {DUCKDB.quantile(True, 'x', q)} FROM t").fetchone()[0]


def allowed(values: list[float], q: str, got: float) -> bool:
    lo, hi = neighbours(values, Fraction(q))
    return lo <= got <= hi


def whole_missed(limit: int = 2000):
    """(n, q) whose exact position is whole and whose double is not: 388 below 2000."""
    for n in range(2, limit):
        for num in range(1, 100):
            if ((n - 1) * num) % 100 == 0 and (n - 1) * (num / 100) != ((n - 1) * num) // 100:
                yield n, f"0.{num:02d}"


def written_sql(source: str, q: str) -> float:
    """The written quantile of the column `x` of the SQL `source`."""
    return CON.execute(f"SELECT {DUCKDB.quantile(True, 'x', q)} FROM ({source}) s(x)").fetchone()[0]


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
