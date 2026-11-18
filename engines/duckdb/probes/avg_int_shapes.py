"""`avg` of integers by query shape: DuckDB against the model's one division (#1608, 12d).

`avg_int.py` ran ungrouped means, which DuckDB rewrites to `sum / count`. This probe
runs the shapes that reach the aggregate's own finalize: `GROUP BY`, `GROUP BY` beside a
`sum`, a whole-partition window and a running window. Run it with
`uv run --no-project --with duckdb==2.0.0 python avg_int_shapes.py`.

Three pools of groups, each a set of (sum, count) pairs built into a table (a group of
`count` integers `sum // count`, and `+1` for `sum % count` of them):

- `adversarial`: 300 pairs with the sum below 2^53 and a count above 1024, where an
  80-bit quotient rounded again to a double differs from one division in doubles;
- `random`: 3000 groups of 2 to 5000 random BIGINTs below 2^40 each, so the sums are
  below 2^53;
- `large sums`: 300 pairs with the sum at or above 2^53, where the sum rounded to a
  double first differs from the exact quotient rounded once.

- `negative sum`: 300 pairs with a negative sum of magnitude 2^53 to 2^63 over 1 to 49
  values, where DuckDB's `HUGEINT` to `DOUBLE` cast of a negative value rounds twice.

Per pool and shape it prints how many groups gave the model's value (one division of
the sum as a double by the count), the 80-bit reading's, the exact quotient rounded
once, or none of them, and the signed distance from the model in units in the last
place for the groups that differ."""

import collections
import platform
import random
from fractions import Fraction

import duckdb

SHAPES = {
    "ungrouped": "select 0, avg(v) from t where g = {g}",
    "group by": "select g, avg(v) from t group by g",
    "group by + sum": "select g, avg(v), sum(v) from t group by g",
    "window partition": "select distinct g, avg(v) over (partition by g) from t",
    "window running": (
        "select g, avg(v) over (partition by g order by i) from t qualify i = max(i) over"
        " (partition by g)"
    ),
}


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


def readings(total: int, count: int) -> tuple[float, float, float]:
    """The model's value, the 80-bit reading's and the exact quotient rounded once."""
    q = Fraction(total, count)
    return float(total) / count, float(rnd(rnd(q, 64), 53)), float(rnd(q, 53))


def ulps(got: float, model: float) -> int:
    """Signed distance of two positive doubles in units in the last place (of the magnitude)."""
    import struct

    bits = lambda x: struct.unpack("<q", struct.pack("<d", x))[0]  # noqa: E731
    return bits(got) - bits(model)


def pool_adversarial(rng: random.Random) -> list[tuple[int, int]]:
    pairs = []
    while len(pairs) < 300:
        y = rng.randrange(1025, 20000)
        k = rng.randrange(2**52, 2**53)
        x = round(Fraction(2 * k + 1, 2) * Fraction(2) ** (rng.randrange(0, 30) - 52) * y)
        if 0 < x < 2**53 and readings(x, y)[0] != readings(x, y)[1]:
            pairs.append((x, y))
    return pairs


def pool_large(rng: random.Random) -> list[tuple[int, int]]:
    pairs = []
    while len(pairs) < 300:
        x, y = rng.randrange(2**53, 2**62), rng.randrange(2, 2000)
        if readings(x, y)[0] != readings(x, y)[2]:
            pairs.append((x, y))
    return pairs


def pool_negative(rng: random.Random) -> list[tuple[int, int]]:
    """Negative sums of magnitude 2^53 to 2^63 over 1 to 50 values."""
    return [(-rng.randrange(2**53, 2**63), rng.randrange(1, 50)) for _ in range(300)]


def load_pairs(con, pairs: list[tuple[int, int]]) -> dict[int, tuple[int, int]]:
    con.execute("create or replace table p(g integer, x bigint, y bigint)")
    con.executemany("insert into p values (?, ?, ?)", [(g, x, y) for g, (x, y) in enumerate(pairs)])
    con.execute(
        "create or replace table t as select g, i::BIGINT i,"
        " sign(x)::BIGINT * ((abs(x) // y) + (i < abs(x) % y)::BIGINT) v"
        " from p, range((select max(y) from p)) r(i) where i < y"
    )
    return dict(enumerate(pairs))


def load_random(con, rng: random.Random) -> dict[int, tuple[int, int]]:
    con.execute(f"select setseed({rng.random()})")
    con.execute(
        "create or replace table t as select g::INTEGER g, i::BIGINT i,"
        " (random() * 2 ** 41 - 2 ** 40)::BIGINT v"
        " from range(3000) a(g), range(5000) b(i)"
        " where i < 2 + (hash(g) % 4999)"
    )
    return {
        g: (int(x), int(y))
        for g, x, y in con.execute(
            "select g, sum(v::HUGEINT), count(*) from t group by g"
        ).fetchall()
    }


def run(con, name: str, groups: dict[int, tuple[int, int]], controls: int) -> None:
    for shape, sql in SHAPES.items():
        if shape == "ungrouped":
            got = {g: con.execute(sql.format(g=g)).fetchone()[1] for g in list(groups)[:controls]}
        else:
            got = {row[0]: row[1] for row in con.execute(sql).fetchall()}
        tally = collections.Counter()
        dist = collections.Counter()
        for g, r in got.items():
            x, y = groups[g]
            model, wide, exact = readings(x, y)
            if x < 0:
                model, wide, exact = (-v for v in readings(-x, y))
            key = (
                "model"
                if r == model
                else "80-bit"
                if r == wide
                else "exact"
                if r == exact
                else "neither"
            )
            tally[key] += 1
            if key != "model":
                dist[ulps(abs(r), abs(model))] += 1
        print(f"{name:12} {shape:17} groups={len(got):5}", dict(tally), "ulp:", dict(dist))


def main() -> None:
    con = duckdb.connect()
    print(platform.machine(), platform.system(), duckdb.__version__)
    rng = random.Random(7)
    run(con, "adversarial", load_pairs(con, pool_adversarial(rng)), 40)
    run(con, "random", load_random(con, rng), 100)
    run(con, "large sums", load_pairs(con, pool_large(rng)), 40)
    run(con, "negative sum", load_pairs(con, pool_negative(rng)), 40)


if __name__ == "__main__":
    main()
