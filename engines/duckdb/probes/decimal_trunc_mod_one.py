"""DuckDB's `x % CAST(1 AS DECIMAL(1,0))` and `x - x % CAST(1 AS DECIMAL(1,0))` over every
`DECIMAL(p, s)` (1 <= p <= 38, 0 <= s <= p: 741 types), the template of `dtrunc` (ruling
284, V1), with its cast to HUGEINT (X1) and, after it, to BIGINT (X2).

Run: python decimal_trunc_mod_one.py

For each type it records the result types of the remainder and of the difference, and
checks `CAST(x - x % 1 AS HUGEINT)` against the truncated integer (Python's
`ROUND_DOWN`) at ±0.5, ±1.5, ±2.5, -0.0, the type's largest and smallest values, and
NULL, where they are of the type: always a value (38 digits fit a HUGEINT). Then
`CAST(that AS BIGINT)`: a raise where the truncated value leaves 64 bits, a value elsewhere.
Prints the types that are not decimal, the result types, and the mismatches.
"""

import decimal

import duckdb

ONE = "CAST(1 AS DECIMAL(1,0))"
CTX = decimal.Context(prec=80)


def values(p: int, s: int) -> list[decimal.Decimal | None]:
    top = decimal.Decimal(10**p - 1).scaleb(-s, CTX)
    vs = [decimal.Decimal(x) for x in ("0.5", "-0.5", "1.5", "-1.5", "2.5", "-2.5", "-0.0")]
    fits = [
        v
        for v in vs
        if v.copy_abs() <= top and v == v.quantize(decimal.Decimal(1).scaleb(-s), context=CTX)
    ]
    return [*fits, top, top.copy_negate(), None]


def main() -> None:
    con = duckdb.connect()
    print("duckdb", duckdb.__version__)
    not_decimal, bad, cases = [], [], 0
    types: dict[tuple[str, str], int] = {}
    for p in range(1, 39):
        for s in range(p + 1):
            x = f"CAST(NULL AS DECIMAL({p},{s}))"
            r, d = con.execute(f"SELECT typeof({x} % {ONE}), typeof({x} - {x} % {ONE})").fetchone()
            if not (r.startswith("DECIMAL") and d.startswith("DECIMAL")):
                not_decimal.append(((p, s), r, d))
                continue
            for v in values(p, s):
                cases += 1
                lit = "NULL" if v is None else f"'{v}'"
                x = f"CAST({lit} AS DECIMAL({p},{s}))"
                want = None if v is None else int(v.to_integral_value(decimal.ROUND_DOWN, CTX))
                huge = f"CAST({x} - {x} % {ONE} AS HUGEINT)"
                got_h = con.execute(f"SELECT {huge}").fetchone()[0]
                if got_h != want:
                    bad.append(((p, s), v, "HUGEINT", got_h, want))
                try:
                    got = con.execute(f"SELECT CAST({huge} AS BIGINT)").fetchone()[0]
                except duckdb.ConversionException:
                    got = "raise"
                if want is not None and not -(2**63) <= want < 2**63:
                    want = "raise"
                if got != want:
                    bad.append(((p, s), v, "BIGINT", got, want))
            types[(r, d)] = types.get((r, d), 0) + 1
    print(f"{cases} cases over the decimal types; types not decimal: {not_decimal}")
    print(f"result types (remainder, difference): {len(types)} pairs, e.g. {sorted(types)[:4]}")
    print(f"mismatches: {bad}")


if __name__ == "__main__":
    main()
