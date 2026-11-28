"""DuckDB's `trunc(x)` of every `DECIMAL(p, s)` (1 <= p <= 38, 0 <= s <= p: 779 types),
the rendering of `dtrunc`'s template (ruling 284, Y1), and `CAST(trunc(x) AS HUGEINT)`.

Run: python decimal_trunc.py

For each type: the result type of `trunc(x)`, which must be a decimal of scale 0 and never
a DOUBLE, and its value at ±0.5, ±1.5, ±2.5, -0.0, the type's largest and smallest values
and NULL (those of the type) against `x - x tmod 1`, the truncated value (Python's
`ROUND_DOWN`), with the HUGEINT cast. Prints the types whose result is not a decimal of
scale 0, the result types, and the mismatches."""

import decimal

import duckdb

CTX = decimal.Context(prec=80)


def values(p: int, s: int) -> list[decimal.Decimal | None]:
    top = decimal.Decimal(10**p - 1).scaleb(-s, CTX)
    q = decimal.Decimal(1).scaleb(-s)
    vs = [decimal.Decimal(x) for x in ("0.5", "-0.5", "1.5", "-1.5", "2.5", "-2.5", "-0.0")]
    fits = [v for v in vs if v.copy_abs() <= top and v == v.quantize(q, context=CTX)]
    return [*fits, top, top.copy_negate(), None]


def main() -> None:
    con = duckdb.connect()
    print("duckdb", duckdb.__version__)
    bad_type, bad, cases, types = [], [], 0, set()
    for p in range(1, 39):
        for s in range(p + 1):
            t = con.execute(f"SELECT typeof(trunc(CAST(NULL AS DECIMAL({p},{s}))))").fetchone()[0]
            types.add(t)
            if not (t.startswith("DECIMAL(") and t.endswith(",0)")):
                bad_type.append(((p, s), t))
            for v in values(p, s):
                cases += 1
                lit = "NULL" if v is None else f"'{v}'"
                x = f"CAST({lit} AS DECIMAL({p},{s}))"
                want = None if v is None else int(v.to_integral_value(decimal.ROUND_DOWN, CTX))
                got = con.execute(f"SELECT CAST(trunc({x}) AS HUGEINT)").fetchone()[0]
                if got != want:
                    bad.append(((p, s), v, got, want))
    print(f"{cases} cases over 779 types; result types: {sorted(types)[:3]} … ({len(types)} kinds)")
    print(f"types whose trunc is not a decimal of scale 0: {bad_type}")
    print(f"mismatches: {bad}")


if __name__ == "__main__":
    main()
