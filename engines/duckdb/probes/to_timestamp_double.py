"""DuckDB's `to_timestamp(double)` against the cast of the double's microseconds (#1922).

Run: python to_timestamp_double.py

For each double `d`, compares three readings of seconds since the epoch:

- `to_timestamp(d)`, as `epoch_us` (or `infinity`, or the error it raises);
- `CAST(d * 1e6 AS BIGINT)`, DuckDB's rounding cast (ties to even, D55);
- the model of ruling 266: `d * 1e6` as a double, rounded half to even,
  raising when it is not finite or leaves 64 bits.

Inputs: ties of the double product (±0.5 … ±3.5 µs and halves between 2^51
and 2^53 µs), -0.0 and subnormals, 10 000 random doubles uniform in exponent
over the timestamp range, and the edges near ±2^63 µs and DuckDB's `infinity`
timestamp (INT64_MAX µs). Prints the counts of each outcome and every input
where two readings differ.
"""

import math
import random
import struct
from collections import Counter

import duckdb

I64 = 2**63


def model(d: float) -> int | str:
    p = d * 1e6
    if not math.isfinite(p):
        return "raise"
    r = round(p)  # Python rounds a float half to even, exactly
    return r if -I64 <= r < I64 else "raise"


def run(con: duckdb.DuckDBPyConnection, sql: str, d: float) -> int | str:
    try:
        v = con.execute(sql, [d]).fetchone()[0]
    except duckdb.Error as e:
        return "raise" if "out of range" in str(e) or "can't be cast" in str(e) else f"error {e}"
    return v


def to_ts(con: duckdb.DuckDBPyConnection, d: float) -> int | str:
    try:
        inf = con.execute("SELECT isinf(to_timestamp($1::DOUBLE))", [d]).fetchone()[0]
    except duckdb.Error as e:
        return "raise" if "out of range" in str(e) else f"error {e}"
    if inf:
        return "infinity"
    return run(con, "SELECT epoch_us(to_timestamp($1::DOUBLE))", d)


def bits(b: int) -> float:
    return struct.unpack("<d", struct.pack("<Q", b))[0]


def inputs(rng: random.Random) -> dict[str, list[float]]:
    ties = [s * k / 1e6 for s in (1, -1) for k in (0.5, 1.5, 2.5, 3.5)]
    ties += [s * (k + 0.5) / 1e6 for s in (1, -1) for k in (2**51 + 1, 2**51 + 2, 2**52 - 1)]
    ties += [s * k / 1e6 for s in (1, -1) for k in (2**52 + 1, 2**53 + 1)]
    # Exactly a tie as a double product: d chosen so that d * 1e6 lands on n + 0.5.
    for _ in range(20_000):
        n = rng.randint(-(2**50), 2**50) >> rng.randint(0, 48)
        d = (n + 0.5) / 1e6
        for step in (d, math.nextafter(d, math.inf), math.nextafter(d, -math.inf)):
            if (step * 1e6) % 1 == 0.5:
                ties.append(step)
                break
    tiny = [0.0, -0.0, bits(1), -bits(1), bits(2**52 - 1), -bits(2**52 - 1), 2.0**-1022, 5e-7]
    # Seconds up to about 9.2e12 (2^63 µs): exponents -30 … 43.
    rand = []
    for _ in range(10_000):
        m = rng.uniform(1, 2) * 2.0 ** rng.randint(-30, 43)
        rand.append(m if rng.random() < 0.5 else -m)
    edge = []
    for s in (1.0, -1.0):
        x = s * I64 / 1e6
        for _ in range(4):
            x = math.nextafter(x, 0)
        for _ in range(9):
            edge.append(x)
            x = math.nextafter(x, s * math.inf)
        # DuckDB's last finite timestamp, 294247-01-10 04:00:54.775806, and around it.
        for us in (I64 - 2, I64 - 1, I64, -I64 + 1, -I64 + 2):
            edge.append(s * abs(us) / 1e6)
    edge += [math.inf, -math.inf, math.nan, 1e300, -1e300]
    return {"ties": ties, "tiny": tiny, "random": rand, "edge": edge}


def main() -> None:
    con = duckdb.connect()
    con.execute("SET timezone = 'UTC'")
    rng = random.Random(1922)
    for name, ds in inputs(rng).items():
        seen: Counter[str] = Counter()
        for d in ds:
            a, b, m = (
                to_ts(con, d),
                run(con, "SELECT CAST($1::DOUBLE * 1e6 AS BIGINT)", d),
                model(d),
            )
            kind = "value" if isinstance(m, int) else m
            if a == b == m:
                seen[f"agree {kind}"] += 1
                continue
            seen["differ"] += 1
            print(f"{name}: d={d!r} to_timestamp={a} cast={b} model={m}")
        print(f"{name}: {len(ds)} inputs, {dict(seen)}")
    print("duckdb", duckdb.__version__)


if __name__ == "__main__":
    main()
