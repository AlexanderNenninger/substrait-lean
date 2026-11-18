"""`avg` of integers: DuckDB against the model's one division (#1608, 12d).

Run on a platform with `uv run --no-project --with duckdb==2.0.0 python avg_int.py`.
It checks pairs (sum, count) that separate the readings of `avg`'s finalize:

1. the fact's open input, `avg` of 2^53 + 1, 0, 0: the model (the sum rounded to a
   double, then one division) gives 3002399751580330.5, a wider division
   3002399751580331;
2. 200 pairs with the sum below 2^53 and a count above 1024 where an 80-bit
   division rounded again to a double differs from one division in doubles;
3. 200 pairs with the sum at or above 2^53 where "round the sum to a double,
   then divide" differs from the exact quotient rounded once.

Each prints how many pairs gave the model's value, the other reading's, or
neither. A table of `count` rows with the given sum is built from integers
`sum // count` and `+1` for `sum % count` of them."""

import platform
import random
from fractions import Fraction

import duckdb


def rnd(q: Fraction, bits: int) -> Fraction:
    """`q` rounded to `bits` significant bits, ties to even (positive `q`)."""
    e = q.numerator.bit_length() - q.denominator.bit_length()
    if Fraction(2) ** e > q:
        e -= 1
    scale = Fraction(2) ** (bits - 1 - e)
    v = q * scale
    f = v.numerator // v.denominator
    r = v - f
    if r > Fraction(1, 2) or (r == Fraction(1, 2) and f % 2 == 1):
        f += 1
    return Fraction(f) / scale


def avg_of(con, total: int, count: int, cast: str = "BIGINT") -> float:
    con.execute(
        f"create or replace table t as select (({total} // {count})"
        f" + (i < {total} % {count})::BIGINT)::{cast} v from range({count}) r(i)"
    )
    return con.execute("select avg(v) from t").fetchone()[0]


def main() -> None:
    con = duckdb.connect()
    print(platform.machine(), platform.system(), duckdb.__version__)
    # 1. The fact's own input.
    con.execute(
        "create table u as select 9007199254740993::BIGINT v union all select 0 union all select 0"
    )
    got = con.execute("select avg(v) from u").fetchone()[0]
    print(
        "2^53+1,0,0:", got, float(got).hex(), "(model 3002399751580330.5, wider 3002399751580331.0)"
    )
    rng = random.Random(1)
    # 2. Sums below 2^53 where 80-bit and 53-bit division differ.
    pairs = []
    while len(pairs) < 200:
        y = rng.randrange(1025, 20000)
        e = rng.randrange(0, 30)
        k = rng.randrange(2**52, 2**53)
        x = round(Fraction(2 * k + 1, 2) * Fraction(2) ** (e - 52) * y)
        if not 0 < x < 2**53:
            continue
        q = Fraction(x, y)
        a, b = rnd(q, 53), rnd(rnd(q, 64), 53)
        if a != b:
            pairs.append((x, y, float(a), float(b)))
    tally = {"model": 0, "wider": 0, "neither": 0}
    odd = []
    for x, y, a, b in pairs:
        r = avg_of(con, x, y)
        key = "model" if r == a else "wider" if r == b else "neither"
        tally[key] += 1
        if key != "model":
            odd.append((x, y, r, a, b))
    print("sum < 2^53, 200 pairs:", tally, odd[:3])
    # 3. Sums at or above 2^53: the sum rounded to a double first, or the exact quotient.
    pairs = []
    while len(pairs) < 200:
        x = rng.randrange(2**53, 2**62)
        y = rng.randrange(2, 2000)
        exact, model = float(Fraction(x, y)), float(x) / y
        if exact != model:
            pairs.append((x, y, model, exact))
    tally = {"model (sum rounded, then divided)": 0, "exact quotient rounded once": 0, "neither": 0}
    odd = []
    for x, y, model, exact in pairs:
        r = avg_of(con, x, y)
        key = (
            "model (sum rounded, then divided)"
            if r == model
            else "exact quotient rounded once"
            if r == exact
            else "neither"
        )
        tally[key] += 1
        if key != "model (sum rounded, then divided)":
            odd.append((x, y, r, model, exact))
    print("sum >= 2^53, 200 pairs:", tally, odd[:3])


if __name__ == "__main__":
    main()
