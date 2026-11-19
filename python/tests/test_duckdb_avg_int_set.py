"""DuckDB's native `avg` of integers is a member of the set `duckdb-avg-int`
states (#1608 12d-2), which `DuckAgg.Allowed` (`DuckDB/AvgSet.lean`) proves
the lifted plan's value is in.

For exact sum `s`, count `n` and `q = s / n`: with `|s| <= 2^53` and
`n <= 2^53`, one of the two doubles around `q` (`q` itself when it is one);
otherwise a double within `8 * 2^-53` of `q`, relatively. The checks here
compute the set exactly with fractions, as the Lean definition does with
integers, and compare against it, not against one double: which member
DuckDB returns depends on its platform and the plan's shape."""

import math
import random
from fractions import Fraction

import pyarrow as pa
import pytest

duckdb = pytest.importorskip("duckdb")


def allowed(s: int, n: int, r: float) -> bool:
    """`r` is in DuckDB's set for the sum `s` of `n` integers."""
    q = Fraction(s, n)
    if abs(s) <= 2**53 and n <= 2**53:
        f = float(q)  # correctly rounded
        if Fraction(f) == q:
            around = {f}
        elif Fraction(f) < q:
            around = {f, math.nextafter(f, math.inf)}
        else:
            around = {math.nextafter(f, -math.inf), f}
        # +0.0 only: the set holds one code per value, never -0.0.
        return r in around and not (r == 0 and math.copysign(1, r) < 0)
    return 2**53 * abs(Fraction(r) - q) <= 8 * abs(q)


def model(s: int, n: int) -> float:
    """`DuckAgg.eval .duckdb .avgBigint`: the sum and the count as doubles,
    divided once."""
    return float(s) / float(n)


# Ruling 79's three instances, and the fact's pair where an 80-bit quotient
# rounded again differs from one division (sum 378693551270 over 88085 rows).
_PAIR = [4299183] * 88084 + [378693551270 - 4299183 * 88084]
CASES = [
    [-9007199254740994],
    [28606501411979134] + [0] * 6,
    [10123957759640631] + [0] * 4,
    _PAIR,
    [2**53 + 1, 0, 0],
    [2**63 - 1, 2**63 - 2, 2**63 - 3],
    [-(2**63), -(2**63) + 1],
    [0, 0, 0],
    [1, 2, 2],
    [7, -3],
]

SHAPES = {
    "ungrouped": "SELECT avg(x) FROM t",
    "grouped": "SELECT avg(x) FROM t GROUP BY g",
    "window": "SELECT DISTINCT avg(x) OVER (PARTITION BY g) FROM t",
}


def _native(values: list[int], shape: str) -> float:
    con = duckdb.connect()
    src = pa.table(
        {"g": pa.array([1] * len(values), pa.int32()), "x": pa.array(values, pa.int64())}
    )
    con.register("src", src)
    con.execute("CREATE TABLE t AS SELECT * FROM src")
    (row,) = con.sql(SHAPES[shape]).fetchall()
    return row[0]


@pytest.mark.parametrize("shape", sorted(SHAPES))
@pytest.mark.parametrize("values", CASES, ids=lambda v: f"{len(v)}-values")
def test_duckdbs_mean_is_in_the_set(values, shape):
    s, n = sum(values), len(values)
    got = _native(values, shape)
    assert allowed(s, n, got), (s, n, got.hex())


@pytest.mark.parametrize("values", CASES, ids=lambda v: f"{len(v)}-values")
def test_the_models_mean_is_in_the_set(values):
    s, n = sum(values), len(values)
    assert allowed(s, n, model(s, n))


def test_a_mean_that_is_an_integer_is_the_one_member():
    # `DuckAgg.avgBigint_exact`: the set of a small integer mean is that integer.
    for s, n in [(6, 3), (-12, 4), (2**53, 1), (0, 5)]:
        q = s // n
        assert allowed(s, n, float(q))
        assert not allowed(s, n, math.nextafter(float(q), math.inf))
    assert not allowed(0, 5, -0.0)


def test_random_means_are_in_the_set():
    rng = random.Random(1608)
    for _ in range(40):
        n = rng.randint(1, 60)
        big = rng.random() < 0.5
        hi = 2**62 if big else 2**40
        values = [rng.randint(-hi, hi) for _ in range(n)]
        for shape in SHAPES:
            got = _native(values, shape)
            assert allowed(sum(values), n, got), (values, shape, got.hex())
