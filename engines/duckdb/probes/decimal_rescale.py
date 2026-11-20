"""DuckDB's drop of decimal places and its cast of a decimal to an integer (#322).

Run: python decimal_rescale.py

For random `DECIMAL(p, s)` values (p up to 38), `CAST(x AS DECIMAL(p, t))` for
every t < s (at most 6 targets) and `CAST(x AS BIGINT)` where the rounded value
fits 64 bits, compared with Python's `ROUND_HALF_UP` (half away from zero on
the magnitude). Prints the number of cases and of mismatches.
"""

import decimal
import random

import duckdb

SHAPES = [(4, 3), (10, 5), (18, 9), (30, 12), (38, 10), (38, 38), (18, 1), (12, 1)]
CTX = decimal.Context(prec=80)


def main() -> None:
    con = duckdb.connect()
    rng = random.Random(1)
    cases = bad = 0
    for p, s in SHAPES:
        for _ in range(300):
            v = decimal.Decimal(rng.randint(-(10**p) + 1, 10**p - 1)).scaleb(-s)
            for t in range(min(s, 6)):
                got = con.execute(
                    f"SELECT CAST(CAST('{v}' AS DECIMAL({p},{s})) AS DECIMAL({p},{t}))"
                )
                want = v.quantize(
                    decimal.Decimal(1).scaleb(-t), rounding=decimal.ROUND_HALF_UP, context=CTX
                )
                cases += 1
                bad += got.fetchone()[0] != want
            whole = v.quantize(decimal.Decimal(1), rounding=decimal.ROUND_HALF_UP, context=CTX)
            if abs(whole) < 2**63:
                got = con.execute(f"SELECT CAST(CAST('{v}' AS DECIMAL({p},{s})) AS BIGINT)")
                cases += 1
                bad += got.fetchone()[0] != int(whole)
    print(cases, bad)


if __name__ == "__main__":
    main()
