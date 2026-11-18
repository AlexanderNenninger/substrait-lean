"""DuckDB probe for the #900 band ruling: the quantile_disc index with a decimal fraction,
grouped and windowed; small in-band cases; the domain witness; one large disagreement."""
# ruff: noqa: E501

import math
import random
import sys
from fractions import Fraction

import duckdb

con = duckdb.connect()
con.execute("SET threads=2")
con.execute("SET memory_limit='3GB'")
print("duckdb", duckdb.__version__)
random.seed(9)


def lit(num0, s):
    return f"0.{num0:0{s}d}"


def exact_idx(n, q):
    return max(1, math.ceil(n * q)) - 1


# (a) index of quantile_disc(x, decimal q) over 0..n-1, grouped and windowed
bad = 0
tried = 0
errs = {}
cases = []
for s in list(range(1, 22)) + [25, 30, 37]:
    den0 = 10**s
    for _ in range(40):
        n = random.randint(1, 3000)
        # boundary: n*num0 = j*den0 + t, t in {-1, 0, 1}: solve roughly
        j = random.randint(0, n)
        base = (j * den0) // n
        for num0 in {base - 1, base, base + 1, random.randint(1, den0 - 1), 1, den0 - 1}:
            if 0 < num0 < den0:
                cases.append((s, n, num0))
for s, n, num0 in cases:
    q = Fraction(num0, 10**s)
    want = exact_idx(n, q)
    tried += 1
    try:
        g = con.execute(f"SELECT quantile_disc(i, {lit(num0, s)}) FROM range({n}) t(i)").fetchone()[
            0
        ]
        w = con.execute(
            f"SELECT DISTINCT quantile_disc(i, {lit(num0, s)}) OVER () FROM range({n}) t(i)"
        ).fetchone()[0]
    except Exception as e:  # noqa: BLE001
        errs.setdefault(s, str(e).splitlines()[0][:110])
        continue
    if g != want or w != want:
        bad += 1
        if bad <= 5:
            print("  index differs:", s, n, num0, "exact", want, "grouped", g, "windowed", w)
print(f"(a) tried {tried}, differ {bad}, scales with an error: {errs}")
# the double path would differ here: n=10, q=0.7 (exact 6)
print(
    "    n=10 q=0.7:",
    con.execute(
        "SELECT quantile_disc(i, 0.7), quantile_disc(i, 0.7::DOUBLE) FROM range(10) t(i)"
    ).fetchone(),
)
print(
    "    typeof(0.0000000000000004):",
    con.execute("SELECT typeof(0.0000000000000004), typeof(0.999999999999999999999)").fetchone(),
)

# (b) small groups in the band (scale 16..21, q near 0 or 1): shifted disc == s[m], and m in engine's pair
B51 = 2**51
okb = 0
for s in range(16, 22):
    den0 = 10**s
    for num0 in [1, 2, 4, 5, den0 - 1, den0 - 3, den0 - 4]:
        for n in [2, 3, 5, 17, 300]:
            n1 = n - 1
            g = math.gcd(num0, den0)
            num, den = num0 // g, den0 // g
            k, r = divmod(n1 * num, den)
            d = min(r, den - r)
            if not d * B51 <= n1 * den:
                continue
            m = k if 2 * r < den else k + 1
            q2 = Fraction(num0, den0) + (
                Fraction(1, 10**15) if 2 * num < den else -Fraction(1, 10**15)
            )
            s2 = max(s, 15)
            n2 = q2 * 10**s2
            assert n2.denominator == 1
            got, cont = con.execute(
                f"SELECT quantile_disc(i, {lit(int(n2), s2)}), quantile_cont(i::DOUBLE, {lit(num0, s)}) FROM range({n}) t(i)"
            ).fetchone()
            RN = float(n1) * (num / den)
            assert got == m, ("shift", s, num0, n, got, m)
            assert m in (math.floor(RN), math.ceil(RN)) and math.floor(RN) <= cont <= math.ceil(
                RN
            ), (s, num0, n, cont, RN)
            okb += 1
print(
    f"(b) in-band small groups: {okb} checked, shifted quantile_disc gives s[m], m in the engine's pair"
)

# (d) the domain witness: reference raises (neighbours -inf, +inf at a fractional position)
print(
    "(d) {-inf,+inf}, q=0.9999999999999999:",
    con.execute(
        "SELECT quantile_cont(x, 0.9999999999999999), quantile_disc(x, 0.9999999999999999), quantile_disc(x, 0.9999999999999989) "
        "FROM (VALUES ('-inf'::DOUBLE), ('inf'::DOUBLE)) t(x)"
    ).fetchone(),
)

# (c) one true disagreement at scale: q = 0.99999999, n = 10^8 - 1 (n1 = 10^8 - 2): k = m = 99999997
if "--large" in sys.argv:
    n = 10**8 - 1
    print(
        "(c)",
        con.execute(
            f"SELECT quantile_disc(i, 0.99999999), quantile_disc(i, 0.999999989999999), quantile_cont(i::DOUBLE, 0.99999999) FROM range({n}) t(i)"
        ).fetchone(),
        "RN =",
        repr(float(n - 1) * 0.99999999),
    )
