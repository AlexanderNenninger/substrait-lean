"""The exact state of a maintained aggregate of doubles (#918 Part B).

Internal: not part of sverify's public API.

`SUM`, `AVG`, `VAR_*`, `STDDEV_*`, `COVAR_*` and `CORR` of doubles are, by
D25 and D30, functions of exact moments: integer sums over a group's values
in units of `2⁻¹⁰⁷⁴` (`Σx`, `Σy`) and `2⁻²¹⁴⁸` (`Σx²`, `Σxy`, `Σy²`), with
the counts of NaN, `+∞` and `-∞` among them. `LinearAgg.floatState`,
`varState`, `covState` and `corrState` (`SubstraitLean/IncrementalFloat.lean`)
keep them and finish as `floatSumCR`, `floatAvgCR`, `varOf`, `covOf` and
`corrOf` do; `LinearAgg.no_drift` proves that after any sequence of batches
the state finishes to the aggregate of the group's current rows. This
module holds that state for `sverify._linear`: Python `int`s per group,
written as comma-separated decimals in the state's `__e<i>` column.

It is trusted glue (`docs/proofs.md`): the engine computes each changed
row's values and weight with the checked `contrib` plan, and this module adds
them up exactly and finishes them as Lean does. CPython's `int / int` is
correctly rounded, ties to even, which is `ofExactDiv`; `sqrt_mag` is Lean's
`sqrtMag`. The engine cannot keep this state itself: splitting a double into
mantissa and exponent (`frexp`) and rounding a 2,100-bit integer need
primitives that Substrait and Ibis do not express.
"""

from __future__ import annotations

import math
from collections.abc import Sequence
from dataclasses import dataclass
from typing import Any

import numpy as np
import pyarrow as pa
import pyarrow.compute as pc

SCALE = 2**1074
"""Every finite double is a multiple of `2⁻¹⁰⁷⁴` (`FloatCode.exact`)."""

MAX_MAG = (2**53 - 1) * 2**2045
"""The largest double's magnitude in units of `2⁻¹⁰⁷⁴` (`FloatCode.maxMag`).
Lean's `scaled` of the code of `+∞` is one more, of NaN's two more."""

_HALF = 27
"""A mantissa of 53 bits splits into two halves below `2²⁷`."""

_WEIGHT = 2**8
"""Weights below this go the vectorised way: a product of two halves times a
weight is below `2⁶²`, and `_CHUNK` of them add up in `decimal128(38)`."""

_CHUNK = 2**20

_DEC = pa.decimal128(38, 0)

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


def fold(
    kind: Kind, keys: pa.Table, values: Sequence[pa.Array], weights: pa.Array
) -> dict[tuple, Moments]:
    """Each group's exact moments of `values` (one column, or a pair's two;
    rows with a NULL skipped), each counted `weights` times (negative for a
    delete)."""
    out: dict[tuple, Moments] = {}
    for start in range(0, keys.num_rows, _CHUNK):
        n = min(_CHUNK, keys.num_rows - start)
        _fold(
            kind,
            out,
            keys.slice(start, n),
            [v.slice(start, n) for v in values],
            weights.slice(start, n),
        )
    return out


def _parts(x: np.ndarray, ok: np.ndarray) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """`x = (hi · 2²⁷ + lo) · 2^shift` in units of `2⁻¹⁰⁷⁴`, where `ok`."""
    m, e = np.frexp(np.where(ok, x, 0.0))
    mant = np.ldexp(m, 53).astype(np.int64)
    return mant >> _HALF, mant & ((1 << _HALF) - 1), e.astype(np.int64) - 53 + 1074


def _fold(
    kind: Kind,
    out: dict[tuple, Moments],
    keys: pa.Table,
    values: Sequence[pa.Array],
    weights: pa.Array,
) -> None:
    xs = [pc.fill_null(v, 0.0).to_numpy(zero_copy_only=False).astype(np.float64) for v in values]
    valid = np.ones(keys.num_rows, dtype=bool)
    for v in values:
        valid &= np.asarray(v.is_valid().to_numpy(zero_copy_only=False), dtype=bool)
    w = pc.fill_null(weights, 0).to_numpy(zero_copy_only=False).astype(np.int64)
    fast = valid & (np.abs(w) < _WEIGHT)
    for x in xs:
        fast &= np.isfinite(x)
    parts = {"x": _parts(xs[0], fast)}
    if len(xs) > 1:
        parts["y"] = _parts(xs[1], fast)
    names = keys.column_names
    # Each sum on the fast rows, as terms `t · 2^c` per row at `2^shift`,
    # added per group and shift in `decimal128(38)`, then put in place.
    for j, term in enumerate(TERMS[kind]):
        if len(term) == 1:
            hi, lo, shift = parts[term]
            terms = [(_HALF, hi), (0, lo)]
        else:
            (ha, la, sa), (hb, lb, sb) = parts[term[0]], parts[term[1]]
            terms = [(2 * _HALF, ha * hb), (_HALF, ha * lb + la * hb), (0, la * lb)]
            shift = sa + sb
        tab = keys.append_column("__shift", pa.array(shift))
        cols = []
        for c, (_, t) in enumerate(terms):
            tab = tab.append_column(f"__t{c}", pa.array(np.where(fast, t * w, 0)).cast(_DEC))
            cols.append(f"__t{c}")
        tab = tab.filter(pa.array(fast))
        if not tab.num_rows:
            continue
        agg = tab.group_by([*names, "__shift"]).aggregate([(c, "sum") for c in cols])
        sums = [agg.column(f"{c}_sum").to_pylist() for c in cols]
        for i, (k, sh) in enumerate(
            zip(agg.select(names).to_pylist(), agg.column("__shift").to_pylist(), strict=True)
        ):
            part = sum(int(sums[c][i]) << terms[c][0] for c in range(len(cols)))
            acc = _at(out, kind, key_of(list(k.values())))
            acc[j] += part << sh if sh >= 0 else part >> -sh
    # The rest one at a time: large weights, NaN and infinities.
    rest = np.flatnonzero(valid & ~fast)
    if rest.size:
        rows = keys.take(pa.array(rest)).to_pylist()
        nt = len(TERMS[kind])
        for r, i in zip(rows, rest, strict=True):
            acc = _at(out, kind, key_of(list(r.values())))
            vs = [float(x[i]) for x in xs]
            wi = int(w[i])
            sv = {"x": scaled(vs[0]), "y": scaled(vs[-1])}
            for j, term in enumerate(TERMS[kind]):
                acc[j] += wi * math.prod(sv[t] for t in term)
            for v in vs:
                if math.isnan(v):
                    acc[nt] += wi
                elif v == math.inf:
                    acc[nt + 1] += wi
                elif v == -math.inf:
                    acc[nt + 2] += wi


def _at(d: dict[tuple, Moments], kind: Kind, k: tuple) -> Moments:
    if k not in d:
        d[k] = [0] * width(kind)
    return d[k]


def add(a: Moments, b: Moments) -> Moments:
    return [x + y for x, y in zip(a, b, strict=True)]


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


def extra_name(i: int) -> str:
    """The state's column for measure `i`'s exact moments."""
    return f"__e{i}"


def names(exact: Sequence[Exact]) -> list[str]:
    """The extra columns of every exact measure."""
    return [extra_name(e.index) for e in exact]


@dataclass(frozen=True)
class Exact:
    """A measure kept exactly: its index, kind and options."""

    index: int
    kind: Kind
    sample: bool = False
    sqrt: bool = False

    def value_columns(self) -> list[str]:
        """The `contrib` columns holding its values."""
        i = self.index
        return [f"__s{i}", f"__t{i}"] if self.kind in ("cov", "corr") else [f"__s{i}"]


def strip(table: pa.Table, exact: Sequence[Exact]) -> pa.Table:
    """The state's columns the engine's plans read."""
    extra = set(names(exact))
    return table.select([c for c in table.column_names if c not in extra])


def attach(
    state: pa.Table,
    keys: Sequence[str],
    exact: Sequence[Exact],
    old: dict[int, dict[tuple, Moments]],
    delta: dict[int, dict[tuple, Moments]],
    check: bool,
) -> pa.Table:
    """`state` (the engine's columns) with each exact measure's moments, the
    old ones of its group plus the change's, and its `__s` the finished
    value. With `check`, raise where the written plan raises."""
    ks = [key_of(list(r.values())) for r in state.select(list(keys)).to_pylist()]
    for e in exact:
        zero = [0] * width(e.kind)
        i = e.index
        mos = [add(old.get(i, {}).get(k, zero), delta.get(i, {}).get(k, zero)) for k in ks]
        ns = state.column(f"__n{i}").to_pylist()
        done = [finish(e.kind, mo, n or 0, e.sample, e.sqrt) for mo, n in zip(mos, ns, strict=True)]
        if check:
            for mo, v in zip(mos, done, strict=True):
                if why := raises(e.kind, mo, v):
                    raise ValueError(why)
        at = state.column_names.index(f"__s{i}")
        state = state.set_column(at, f"__s{i}", pa.array(done, pa.float64()))
        state = state.append_column(
            pa.field(extra_name(i), pa.string()),
            pa.array([",".join(map(str, mo)) for mo in mos], pa.string()),
        )
    return state


def moments_by_key(
    table: pa.Table, keys: Sequence[str], exact: Sequence[Exact]
) -> dict[int, dict[tuple, Moments]]:
    """The moments a state table holds, per measure and group."""
    ks = [key_of(list(r.values())) for r in table.select(list(keys)).to_pylist()]
    out = {}
    for e in exact:
        col = table.column(extra_name(e.index)).to_pylist()
        out[e.index] = {k: [int(x) for x in s.split(",")] for k, s in zip(ks, col, strict=True)}
    return out


def fold_contributions(
    contrib: pa.Table, keys: Sequence[str], exact: Sequence[Exact]
) -> dict[int, dict[tuple, Moments]]:
    """The moments of each exact measure in a table of contributions (the
    keys, `__n<i>` the weight a counted value has, `__s<i>` the value and
    for a pair `__t<i>` its second)."""
    k = contrib.select(list(keys))
    return {
        e.index: fold(
            e.kind,
            k,
            [contrib.column(c).combine_chunks() for c in e.value_columns()],
            contrib.column(f"__n{e.index}").combine_chunks(),
        )
        for e in exact
    }
