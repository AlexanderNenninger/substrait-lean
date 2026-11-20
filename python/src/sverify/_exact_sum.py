"""The exact state of a maintained aggregate of doubles (#918 Part B, #1447).

Internal: not part of sverify's public API.

`SUM`, `AVG`, `VAR_*`, `STDDEV_*`, `COVAR_*` and `CORR` of doubles are, by
D25 and D30, functions of exact moments: integer sums over a group's values
in units of `2⁻¹⁰⁷⁴` (`Σx`, `Σy`) and `2⁻²¹⁴⁸` (`Σx²`, `Σxy`, `Σy²`), with
the counts of NaN, `+∞` and `-∞` among them. `LinearAgg.floatState`,
`varState`, `covState` and `corrState` (`SubstraitLean/IncrementalFloat.lean`)
keep them and finish as `floatSumCR`, `floatAvgCR`, `varOf`, `covOf` and
`corrOf` do; `LinearAgg.no_drift` proves that after any sequence of batches
the state finishes to the aggregate of the group's current rows.

The engine keeps these integers itself, in pieces (`limbs`). A finite double
is `m · 2^(p - 1074)` with `|m| < 2⁵³` and `p` in `[0, 2045]`; it adds
`m · 2^(p mod 32)` to limb `p div 32` of its sum. A square or a product splits
`m` into halves below `2²⁷`, so every piece is below `2⁵⁴` and each limb
holds a `DECIMAL(38,0)` sum of them. A limb is a row of the group state: the
group's keys, `__l` its code (measure, slot, limb) and `__v` its value. Adding
up rows per group and code is the engine's `SUM`, so the state is linear over
Z-sets as the moments are: inserts add, deletes subtract, and the limbs are a
function of the group's current rows, `Σ v · 2^(32 j)` the moment itself.

Substrait has no `frexp`, so the split scales `|x|` into `[1, 2)` by binary
steps, each a comparison with and a product by a power-of-two literal; it
needs no `POWER` or `LOG2`, which Spark's lowering refuses. That the steps
give back the value is taken of the engine: such comparisons and products are
exact in IEEE arithmetic, and `test_the_split_is_frexp` checks every literal
and step on DuckDB, Polars and Spark. Each row checks only the result's
normal form, an integer mantissa below `2⁵³` and, for a normal value, at
least `2⁵²`; a row that fails counts in the `BROKEN` slot, which raises at the
finish. A limb holds at most `HEADROOM` pieces' worth before `DECIMAL(38,0)`
could overflow, so the finish raises for a group with more values, and for a
NULL limb, an overflow an engine let through (E1 and E2 of ruling 167, E2 as
ruling 174 amends it).

It is trusted glue (`docs/proofs.md`): the engine computes the limbs with
the checked plans, and this module reads them back for the touched groups
only and finishes them as Lean does. CPython's `int / int` is correctly
rounded, ties to even, which is `ofExactDiv`; `sqrt_mag` is Lean's `sqrtMag`.
"""

from __future__ import annotations

import math
from collections.abc import Sequence
from dataclasses import dataclass
from decimal import Decimal
from typing import Any

import ibis
import ibis.expr.types as ir
import pyarrow as pa
import pyarrow.compute as pc

from sverify._keys import canonical_keys

SCALE = 2**1074
"""Every finite double is a multiple of `2⁻¹⁰⁷⁴` (`FloatCode.exact`)."""

MAX_MAG = (2**53 - 1) * 2**2045
"""The largest double's magnitude in units of `2⁻¹⁰⁷⁴` (`FloatCode.maxMag`).
Lean's `scaled` of the code of `+∞` is one more, of NaN's two more."""

TERMS: dict[str, tuple[str, ...]] = {
    "fsum": ("x",),
    "favg": ("x",),
    "var": ("x", "xx"),
    "cov": ("x", "y", "xy"),
    "corr": ("x", "y", "xy", "xx", "yy"),
}
"""The sums each kind keeps, before the counts of NaN, `+∞` and `-∞`."""

Kind = str
"""`fsum`, `favg`, or `var`, `cov`, `corr` with `sample` and `sqrt` in
`Exact`."""

CODE, VALUE = "__l", "__v"
"""The state's columns of a limb row: its code, NULL on a group's own row,
and its value."""

LIMB_TYPE = "decimal(38, 0)"

_BITS = 32
"""Bits per limb: a piece below `2⁵⁴` shifted by less than `2³²`."""

_LIMBS = 256
"""Limbs per slot: a square's pieces reach bit `2 · 2045 + 54 + 53`."""

_SLOTS = 32

HEADROOM = 2**41
"""Values per group a limb holds: `2⁴¹` pieces below `2⁸⁵` stay below
`10³⁸`, the top of `DECIMAL(38,0)`."""

FINITE, NAN, POS_INF, NEG_INF = range(4)
_CLASS = (0, MAX_MAG + 2, MAX_MAG + 1, -(MAX_MAG + 1))
"""Lean's `scaled` of each class's code: 0 stands for a finite value, whose
part is in the limbs."""

# The slots of a measure: `X + c` holds `Σx` over the rows whose second value
# has class `c` (always `FINITE` for one value), `Y + c` the same for `y`;
# `CLASSES + 4 · cx + cy` counts the rows with a NaN or an infinity by their
# classes; `BROKEN` counts the rows whose split failed.
X, Y, XX, YY, XY, CLASSES, BROKEN = 0, 4, 8, 9, 10, 12, 28

_HALF = 2**27


def width(kind: Kind) -> int:
    """How many integers a kind's moments are."""
    return len(TERMS[kind]) + 3


def exact(x: float) -> int:
    """A finite double in units of `2⁻¹⁰⁷⁴`, exactly."""
    n, d = x.as_integer_ratio()
    return n * (SCALE // d)


def scaled(x: float) -> int:
    """Lean's `scaled` of the code of `x`: its exact value, and for `±∞` and
    NaN the magnitudes past the largest double their codes have."""
    if math.isnan(x):
        return MAX_MAG + 2
    if math.isinf(x):
        return MAX_MAG + 1 if x > 0 else -(MAX_MAG + 1)
    return exact(x)


def key_of(row: Sequence[Any]) -> tuple:
    """A group key for a dict: a NaN key equals itself, `-0.0` equals `0.0`,
    as the engine's `GROUP BY` has them."""
    out = []
    for v in row:
        if isinstance(v, float):
            v = ("nan",) if math.isnan(v) else v + 0.0
        out.append(v)
    return tuple(out)


Moments = list[int]
"""The sums of `TERMS[kind]`, then the counts of NaN, `+∞` and `-∞`."""


@dataclass(frozen=True)
class Exact:
    """A measure kept exactly: its index, kind and options."""

    index: int
    kind: Kind
    sample: bool = False
    sqrt: bool = False

    @property
    def pair(self) -> bool:
        return self.kind in ("cov", "corr")


# --- The limbs, as Ibis expressions over each changed row --------------------


def _wide(e: Any) -> Any:
    # The checker writes an integer's cast to `DECIMAL(38,0)` away, which
    # leaves a product at 64 bits; a sum at that type keeps it (#1876).
    return e.cast(LIMB_TYPE) + ibis.literal(Decimal(0), LIMB_TYPE)


def _split(t: ir.Table, c: str) -> ir.Table:
    """`t` with the class of the double column `c` (`<c>_c`), its grid
    position `<c>_p` and signed mantissa `<c>_m` (0 for zero or a NaN or
    infinity), and `<c>_bad` 1 where the split does not give back the value.
    Each step reads the step before as columns, so the written plan stays
    small."""
    x: Any = t[c]
    one, zero = ibis.literal(1, "int64"), ibis.literal(0, "int64")
    finite = x.notnull() & ~x.isnan() & ~x.isinf()
    cls = ibis.cases(
        (x.isnull() | finite, ibis.literal(FINITE, "int64")),
        (x.isnan(), ibis.literal(NAN, "int64")),
        (x > 0, ibis.literal(POS_INF, "int64")),
        else_=ibis.literal(NEG_INF, "int64"),
    )
    on = finite & (x != 0)
    t = t.mutate(**{f"{c}_c": cls, f"{c}_f": ibis.ifelse(on, x, 0.0)})
    f: Any = t[f"{c}_f"]
    # |f| scaled into [1, 2) a binary step at a time, each a comparison and a
    # product with a power of two, both exact on every engine: no POWER or
    # LOG2, which some engines compute only within an ulp. `e` counts the
    # steps, so `|f| = a · 2^e`. Each step reads the one before as columns: a
    # guard of the written plan repeats its operands, so nesting grows it.
    a, e, s = f"{c}_a", f"{c}_e", f"{c}_s"
    t = t.mutate(**{a: ibis.ifelse(f == 0, 1.0, f.abs())})
    # A value below 1 first goes up into `[1, 2¹⁰²⁴)`: by `2¹⁰⁷⁴` (two
    # factors of `2⁵³⁷`) below `2⁻⁵⁰`, by `2⁵²` below 1. Then every step
    # scales down, and a subnormal's scaled value is its mantissa. Each
    # operand is gated, not only the product: an engine may compute both
    # branches, and a large value times `2¹⁰⁷⁴` overflows. `e` starts as a
    # 64-bit column: the written plan types an integer literal by its value.
    tiny, small = t[a] < 2.0**-50, t[a] < 1.0
    up_tiny: Any = ibis.ifelse(tiny, t[a], 0.0)
    up_small: Any = ibis.ifelse(small, t[a], 0.0)
    t = t.mutate(
        **{
            s: ibis.cases(
                (tiny, up_tiny * 2.0**537 * 2.0**537),
                (small, up_small * 2.0**52),
                else_=t[a],
            ),
            e: (t[a] * 0.0).cast("int64")
            - ibis.cases(
                (tiny, ibis.literal(1074, "int64")),
                (small, ibis.literal(52, "int64")),
                else_=zero,
            ),
        }
    )
    t = t.mutate(**{a: t[s]})
    for b in range(10, -1, -1):
        # `2¹⁰²⁴` is past the largest double: halve `a` and compare with `2¹⁰²³`.
        big = t[a] * 0.5 >= 2.0**1023 if b == 10 else t[a] >= 2.0 ** (2**b)
        down = t[a] * 2.0**-512 * 2.0**-512 if b == 10 else t[a] * 2.0 ** -(2**b)
        step = ibis.literal(2**b, "int64")
        t = t.mutate(**{a: ibis.ifelse(big, down, t[a]), e: t[e] + ibis.ifelse(big, step, zero)})
    # The mantissa: `a · 2⁵²` signed for a normal value; for a subnormal, the
    # scaled value above (its exponent is clamped to -1022).
    sub = t[e] < -1022
    t = t.mutate(**{f"{c}_n": ibis.ifelse(sub, t[s], t[a] * 2.0**52)})
    t = t.mutate(
        **{
            f"{c}_d": ibis.ifelse(f < 0, -t[f"{c}_n"], ibis.ifelse(f == 0, 0.0, t[f"{c}_n"])),
            e: ibis.greatest(t[e], -1022),
        }
    )
    e = t[e]
    d: Any = t[f"{c}_d"]
    ok = (d.floor() == d) & (d.abs() < 2.0**53) & ((e == -1022) | (d.abs() >= 2.0**52) | (d == 0))
    t = t.mutate(
        **{
            f"{c}_p": e + 1022,
            f"{c}_m": ibis.ifelse(ok, d, 0.0).cast("int64"),
            f"{c}_bad": ibis.ifelse(ok, zero, one),
        }
    )
    # The mantissa's magnitude in halves below `2²⁷`, for squares and products.
    m: Any = t[f"{c}_m"]
    t = t.mutate(**{f"{c}_abs": m.abs()})
    mag: Any = t[f"{c}_abs"]
    return t.mutate(**{f"{c}_hi": mag // _HALF, f"{c}_lo": mag % _HALF})


def limbs(
    rows: ir.Table, keys: Sequence[str], measures: Sequence[tuple[Exact, str, str | None, str]]
) -> ir.Table:
    """The limb rows of `rows`: `keys`, `CODE` and `VALUE`, one per piece
    of a value. `measures` gives each exact measure with its value column,
    its second (a pair's) and the column that holds 1 where the row counts
    for it. The weight is `__w`."""
    for c in {c for _, x, y, _ in measures for c in (x, y) if c is not None}:
        rows = _split(rows, c)
    pieces: list[tuple[Any, Any, Any, Any]] = []
    """(measure index, slot, position, value) per piece, all expressions."""
    zero: Any = ibis.literal(0, "int64")

    for e, xc, yc, okc in measures:
        r: Any = rows
        ok = r[okc] == 1
        cx, px, mx = r[f"{xc}_c"], r[f"{xc}_p"], r[f"{xc}_m"]
        cy: Any = r[f"{yc}_c"] if yc else zero
        py: Any = r[f"{yc}_p"] if yc else None
        my: Any = r[f"{yc}_m"] if yc else None
        hx: Any = r[f"{xc}_hi"]
        lx: Any = r[f"{xc}_lo"]
        hy: Any = r[f"{yc}_hi"] if yc else None
        ly: Any = r[f"{yc}_lo"] if yc else None
        i = e.index
        terms = TERMS[e.kind]
        pieces.append((i, X + cy, px, ibis.ifelse(ok, mx, 0)))
        if yc:
            pieces.append((i, Y + cx, py, ibis.ifelse(ok, my, 0)))
        for name, h, low, pm in (("xx", hx, lx, px), ("yy", hy, ly, py)):
            if name in terms:
                slot = XX if name == "xx" else YY
                for at, v in ((54, h * h), (27, 2 * h * low), (0, low * low)):
                    pieces.append(
                        (i, ibis.literal(slot, "int64"), 2 * pm + at, ibis.ifelse(ok, v, 0))
                    )
        if "xy" in terms:
            sign = ibis.ifelse((mx < 0) != (my < 0), -1, 1)
            for at, v in ((54, hx * hy), (27, hx * ly), (27, lx * hy), (0, lx * ly)):
                pieces.append(
                    (i, ibis.literal(XY, "int64"), px + py + at, ibis.ifelse(ok, sign * v, 0))
                )
        counted = ok & ((cx != FINITE) | (cy != FINITE))
        pieces.append((i, CLASSES + 4 * cx + cy, zero, ibis.ifelse(counted, 1, 0)))
        bad: Any = r[f"{xc}_bad"]
        if yc:
            bad = bad + r[f"{yc}_bad"]
        pieces.append((i, ibis.literal(BROKEN, "int64"), zero, ibis.ifelse(ok, bad, 0)))
    # One row per (row, piece): a cross join with the piece numbers, so the
    # split runs once per row.
    nums = ibis.memtable({"__k": list(range(len(pieces)))}, schema={"__k": "int64"})
    j: Any = rows.cross_join(nums)
    n: Any = j["__k"]

    def pick(at: int) -> Any:
        def lit(v: Any) -> Any:
            return ibis.literal(v, "int64") if isinstance(v, int) else v

        return ibis.cases(*[(n == k, lit(p[at])) for k, p in enumerate(pieces)])

    j = j.mutate(
        __i=pick(0), __slot=pick(1), __pos=pick(2).cast("int64"), __val=pick(3).cast("int64")
    )
    j = j.filter(j["__val"] != 0)
    # `2^(pos mod 32)` from the bits of `pos mod 32`, a 64-bit integer.
    j = j.mutate(__r=j["__pos"] % _BITS, __shift=ibis.literal(1, "int64"))
    for b in range(5):
        bit = (j["__r"] // 2**b) % 2 == 1
        j = j.mutate(__shift=ibis.ifelse(bit, j["__shift"] * 2 ** (2**b), j["__shift"]))
    code = (j["__i"] * _SLOTS + j["__slot"]) * _LIMBS + j["__pos"] // _BITS
    return j.select(
        *keys,
        **{CODE: code.cast("int32"), VALUE: _wide(j["__val"]) * _wide(j["__shift"]) * j["__w"]},
    )


def _grid_exp(a: int, n: int) -> int:
    """Lean's `gridExp`: the bits of `⌊a / n⌋` past 53, or 0."""
    q = a // n
    return max(q.bit_length() - 1 - 52, 0) if q else 0


def _round_grid(t: int, e: int, exact_: bool) -> int:
    """Lean's `roundGrid`: `t / 2⁶⁰` to a multiple of `2ᵉ`, ties to even."""
    m = 2 ** (e + 60)
    q, r = divmod(t, m)
    if 2 * r < m:
        return q * 2**e
    if m < 2 * r:
        return (q + 1) * 2**e
    if exact_:
        return (q if q % 2 == 0 else q + 1) * 2**e
    return (q + 1) * 2**e


def sqrt_mag(a: int, b: int) -> int:
    """Lean's `sqrtMag`: `√(a / b)` on the grid of doubles, ties to even, in
    units of `2⁻¹⁰⁷⁴`."""
    x = a * 2**120 // b
    t = math.isqrt(x)
    return _round_grid(t, _grid_exp(t, 2**60), (a * 2**120) % b == 0 and t * t == x)


def _of_mag(m: int) -> float:
    """`posCode`: the double of the magnitude `m`, `+∞` past the largest."""
    return math.inf if m > MAX_MAG else m / SCALE


def _div(v: int, d: int) -> float:
    """`ofExactDiv`: `v / d` rounded once, `±∞` past the largest double."""
    try:
        return v / d
    except OverflowError:
        return math.inf if v > 0 else -math.inf


def finish(
    kind: Kind, mo: Moments, n: int, sample: bool = False, sqrt: bool = False
) -> float | None:
    """The aggregate from the moments of `n` values (pairs for `cov` and
    `corr`), as Lean finishes it (`floatState`, `varState`, `covState`,
    `corrState`)."""
    nt = len(TERMS[kind])
    nan, pinf, ninf = mo[nt : nt + 3]
    nonfinite = nan > 0 or pinf > 0 or ninf > 0
    if kind in ("fsum", "favg"):
        if n == 0:
            return None
        if nan > 0 or (pinf > 0 and ninf > 0):
            return math.nan
        if pinf > 0:
            return math.inf
        if ninf > 0:
            return -math.inf
        return _div(mo[0], n * SCALE) if kind == "favg" else _div(mo[0], SCALE)
    if kind == "var":
        sx, sxx = mo[0], mo[1]
        if n == 0 or (sample and n == 1):
            return None
        if nonfinite:
            return math.nan
        d = n - 1 if sample else n
        num = n * sxx - sx * sx
        if sqrt:
            return _of_mag(sqrt_mag(max(num, 0), n * d))
        return _div(num, n * d * SCALE * SCALE)
    if kind == "cov":
        sx, sy, sxy = mo[0], mo[1], mo[2]
        if n == 0 or (sample and n == 1):
            return None
        if nonfinite:
            return math.nan
        d = n - 1 if sample else n
        return _div(n * sxy - sx * sy, n * d * SCALE * SCALE)
    # `corr`
    sx, sy, sxy, sxx, syy = mo[:5]
    nx, ny = n * sxx - sx * sx, n * syy - sy * sy
    if n < 2 or nx == 0 or ny == 0:
        return None
    if nonfinite:
        return math.nan
    c = n * sxy - sx * sy
    m = min(sqrt_mag(c * c * 2**2148, max(nx * ny, 0)), 2**1074)
    return -_of_mag(m) if c < 0 else _of_mag(m)


def raises(kind: Kind, mo: Moments, value: float | None) -> str | None:
    """Why the written plan raises where the state finishes to `value`: a
    `SUM` that adds `+∞` and `-∞`, or a statistical aggregate of an
    infinity, creates a NaN (#257); a finite result past the largest double
    overflows (#575)."""
    nt = len(TERMS[kind])
    nan, pinf, ninf = mo[nt : nt + 3]
    if kind in ("fsum", "favg"):
        if nan == 0 and pinf > 0 and ninf > 0:
            return "domain error: a SUM of doubles adds +inf and -inf (#257)"
    elif pinf > 0 or ninf > 0:
        return f"domain error: a {kind.upper()} of an infinity (#257)"
    if value is not None and math.isinf(value) and pinf == 0 and ninf == 0:
        return f"overflow: a {kind.upper()} of finite doubles leaves the range of doubles (#575)"
    return None


# --- Reading the limbs back, and the finish ------------------------------------


def moments(e: Exact, slots: dict[int, int]) -> Moments:
    """The moments of `e` from its slots' integers (`Σ v · 2^(32 j)` over a
    slot's limbs): the finite parts from the limbs, the NaN and infinities
    from their counts by class, as Lean's `scaled` codes add them up."""
    c = _CLASS
    fx = [slots.get(X + k, 0) for k in range(4)]
    fy = [slots.get(Y + k, 0) for k in range(4)]
    sx, sy = sum(fx), sum(fy)
    sxx, syy = slots.get(XX, 0), slots.get(YY, 0)
    sxy = slots.get(XY, 0) + sum(c[k] * (fx[k] + fy[k]) for k in range(1, 4) if fx[k] or fy[k])
    classes = [0] * 4
    for a in range(4):
        for b in range(4):
            n = slots.get(CLASSES + 4 * a + b, 0)
            if not n:
                continue
            sx, sy = sx + n * c[a], sy + n * c[b]
            sxx, syy = sxx + n * c[a] * c[a], syy + n * c[b] * c[b]
            sxy += n * c[a] * c[b]
            classes[a] += n
            if e.pair:
                classes[b] += n
    sums = {"x": sx, "y": sy, "xx": sxx, "yy": syy, "xy": sxy}
    return [sums[t] for t in TERMS[e.kind]] + classes[1:]


_CHUNK = 2**16


def _call(name: str, *args: Any) -> Any:
    # `pyarrow.compute`'s functions are generated at import, so type checkers
    # do not see them; `call_function` is typed.
    return pc.call_function(name, list(args))


def attach(state: pa.Table, keys: Sequence[str], exact: Sequence[Exact], check: bool) -> pa.Table:
    """`state` (a group's own row and its limb rows, per group) with each
    exact measure's `__s` finished from its limbs. Raises where a group has
    more values than the limbs hold, or a value's split failed; with `check`,
    also where the written plan raises. Python reads the state's rows only,
    a chunk at a time: a group's rows and limbs, never an input row."""
    if not exact:
        return state
    canon = canonical_keys(state.select(list(keys)), keys)
    by = [(k, "ascending", "at_start") for k in [*keys, CODE]]
    order = pc.call_function(
        "sort_indices",
        [canon.append_column(CODE, state.column(CODE))],
        pc.SortOptions(sort_keys=by),  # pyrefly: ignore[missing-attribute]
    )
    state = state.take(order)
    canon = canon.take(order)
    ns = [f"__n{e.index}" for e in exact]
    rows = canon.append_column(CODE, state.column(CODE)).append_column(VALUE, state.column(VALUE))
    for n in ns:
        rows = rows.append_column(n, state.column(n))
    by_index = {e.index: e for e in exact}
    done: dict[int, list[float | None]] = {e.index: [] for e in exact}
    cur: tuple | None = None
    counts: list[int] = []
    slots: dict[tuple[int, int], int] = {}

    def flush() -> None:
        for e, n in zip(exact, counts, strict=True):
            own = {s: v for (i, s), v in slots.items() if i == e.index}
            if own.get(BROKEN, 0):
                raise ValueError(f"a double's split into limbs failed in measure {e.index} (#1447)")
            if n >= HEADROOM:
                raise ValueError(
                    f"a group of {n} values exceeds the exact state's {HEADROOM} (#1447)"
                )
            mo = moments(e, own)
            value = finish(e.kind, mo, n, e.sample, e.sqrt)
            if check and (why := raises(e.kind, mo, value)):
                raise ValueError(why)
            done[e.index].append(value)

    for batch in rows.to_batches(max_chunksize=_CHUNK):
        for r in batch.to_pylist():
            code = r[CODE]
            if code is None:
                if cur is not None:
                    flush()
                cur = key_of([r[k] for k in keys])
                counts = [r[n] or 0 for n in ns]
                slots = {}
                continue
            i, rest = divmod(code, _SLOTS * _LIMBS)
            slot, limb = divmod(rest, _LIMBS)
            if i in by_index:
                if r[VALUE] is None:  # an engine `SUM` that overflowed to NULL
                    raise ValueError(f"a limb of measure {i} is NULL: its sum overflowed (#1447)")
                slots[(i, slot)] = slots.get((i, slot), 0) + (int(r[VALUE]) << (_BITS * limb))
    if cur is not None:
        flush()
    own_rows = _call("is_null", state.column(CODE))
    main = state.filter(own_rows)
    for e in exact:
        at = main.column_names.index(f"__s{e.index}")
        main = main.set_column(at, f"__s{e.index}", pa.array(done[e.index], pa.float64()))
    return pa.concat_tables([main, state.filter(_call("invert", own_rows))])
