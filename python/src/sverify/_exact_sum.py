"""The exact state of a maintained `SUM` or `AVG` of doubles (#918 Part B).

Internal: not part of sverify's public API.

`LinearAgg.floatState` (`SubstraitLean/IncrementalFloat.lean`) keeps, per
group, the exact sum of the values as an integer in units of `2⁻¹⁰⁷⁴` and
the counts of NaN, `+∞` and `-∞` among them, and rounds once when it
finishes; `LinearAgg.fsum_no_drift` proves that after any sequence of
batches this gives `floatSumCR` (or `floatAvgCR`) of the group's current
rows. This module holds that state for `sverify._linear`: a Python `int`
per group, written as a decimal string in the state's `__e<i>` column, and
`int` counts in `__nan<i>`, `__pinf<i>`, `__ninf<i>`.

It is trusted glue (`docs/proofs.md`): the engine computes each changed
row's value and weight with the checked `contrib` plan, and this module adds
them up exactly and rounds. CPython's `int / int` is correctly rounded, ties
to even, which is `ofExact` and `ofExactDiv`. The engine cannot keep this
state itself: splitting a double into mantissa and exponent (`frexp`) and
rounding a 2,100-bit integer need primitives that Substrait and Ibis do not
express.
"""

from __future__ import annotations

import math
from collections.abc import Sequence
from typing import Any

import numpy as np
import pyarrow as pa
import pyarrow.compute as pc

SCALE = 2**1074
"""Every finite double is a multiple of `2⁻¹⁰⁷⁴` (`FloatCode.exact`)."""

_HALF = 27
"""A mantissa of 53 bits splits into two halves below `2²⁷`."""

_WEIGHT = 2**8
"""Weights below this go the vectorised way: a half times a weight is below
`2³⁴`, so `_CHUNK` rows of them add up in 64 bits."""

_CHUNK = 2**20


def extra_names(i: int) -> list[str]:
    """The state's columns for measure `i`'s exact moments."""
    return [f"__e{i}", f"__nan{i}", f"__pinf{i}", f"__ninf{i}"]


def extra_fields(i: int) -> list[pa.Field]:
    e, *counts = extra_names(i)
    return [pa.field(e, pa.string()), *(pa.field(c, pa.int64()) for c in counts)]


def exact(x: float) -> int:
    """A finite double in units of `2⁻¹⁰⁷⁴`, exactly."""
    n, d = x.as_integer_ratio()
    return n * (SCALE // d)


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
"""`[S, nan, pinf, ninf]`: the exact sum and the non-finite counts."""


def fold(keys: pa.Table, values: pa.Array, weights: pa.Array) -> dict[tuple, Moments]:
    """Each group's exact moments of `values` (NULLs skipped), each counted
    `weights` times (negative for a delete)."""
    out: dict[tuple, Moments] = {}
    for start in range(0, keys.num_rows, _CHUNK):
        n = min(_CHUNK, keys.num_rows - start)
        _fold(out, keys.slice(start, n), values.slice(start, n), weights.slice(start, n))
    return out


def _fold(out: dict[tuple, Moments], keys: pa.Table, values: pa.Array, weights: pa.Array) -> None:
    x = pc.fill_null(values, 0.0).to_numpy(zero_copy_only=False).astype(np.float64)
    valid = np.asarray(values.is_valid().to_numpy(zero_copy_only=False), dtype=bool)
    w = pc.fill_null(weights, 0).to_numpy(zero_copy_only=False).astype(np.int64)
    fin = valid & np.isfinite(x)
    small = fin & (np.abs(w) < _WEIGHT)
    # Finite values, small weights: mantissa halves times weights, added per
    # group and exponent in 64 bits, then shifted into place as `int`s.
    m, e = np.frexp(np.where(small, x, 0.0))
    mant = np.ldexp(m, 53).astype(np.int64)
    shift = e.astype(np.int64) - 53 + 1074
    hi = np.where(small, (mant >> _HALF) * w, 0)
    lo = np.where(small, (mant & ((1 << _HALF) - 1)) * w, 0)
    names = keys.column_names
    tab = (
        keys.append_column("__shift", pa.array(shift))
        .append_column("__hi", pa.array(hi))
        .append_column("__lo", pa.array(lo))
        .filter(pa.array(small))
    )
    if tab.num_rows:
        agg = tab.group_by([*names, "__shift"]).aggregate([("__hi", "sum"), ("__lo", "sum")])
        for k, sh, h, lo_ in zip(
            agg.select(names).to_pylist(),
            agg.column("__shift").to_pylist(),
            agg.column("__hi_sum").to_pylist(),
            agg.column("__lo_sum").to_pylist(),
            strict=True,
        ):
            part = (h << _HALF) + lo_
            _at(out, key_of(list(k.values())))[0] += part << sh if sh >= 0 else part >> -sh
    # The rest one at a time: large weights, NaN and infinities.
    rest = np.flatnonzero(valid & ~small)
    if rest.size:
        rows = keys.take(pa.array(rest)).to_pylist()
        for r, j in zip(rows, rest, strict=True):
            acc = _at(out, key_of(list(r.values())))
            v, wj = float(x[j]), int(w[j])
            if math.isnan(v):
                acc[1] += wj
            elif v == math.inf:
                acc[2] += wj
            elif v == -math.inf:
                acc[3] += wj
            else:
                acc[0] += wj * exact(v)


def _at(d: dict[tuple, Moments], k: tuple) -> Moments:
    if k not in d:
        d[k] = [0, 0, 0, 0]
    return d[k]


def add(a: Moments, b: Moments) -> Moments:
    return [x + y for x, y in zip(a, b, strict=True)]


def finish(mo: Moments, n: int, avg: bool) -> float | None:
    """`floatSumCR` (or `floatAvgCR`) from the moments of `n` values: NULL
    without values, the non-finite result as `nonFinite` gives it, else the
    exact sum (over `n`) rounded once. A finite sum past the largest double
    is `±∞`, as `ofExact` rounds it."""
    s, nan, pinf, ninf = mo
    if n == 0:
        return None
    if nan > 0 or (pinf > 0 and ninf > 0):
        return math.nan
    if pinf > 0:
        return math.inf
    if ninf > 0:
        return -math.inf
    try:
        return s / (n * SCALE) if avg else s / SCALE
    except OverflowError:
        return math.inf if s > 0 else -math.inf


def raises(mo: Moments, value: float | None) -> str | None:
    """Why the written plan raises where the state finishes to `value`:
    `+∞` and `-∞` together create a NaN (#257), and a finite sum past the
    largest double overflows (#575)."""
    _, nan, pinf, ninf = mo
    if nan == 0 and pinf > 0 and ninf > 0:
        return "domain error: a SUM of doubles adds +inf and -inf (#257)"
    if value is not None and math.isinf(value) and pinf == 0 and ninf == 0:
        return "overflow: a SUM of finite doubles leaves the range of doubles (#575)"
    return None


def to_columns(moments: Sequence[Moments]) -> list[pa.Array]:
    """The state's `__e`, `__nan`, `__pinf`, `__ninf` columns."""
    return [
        pa.array([str(m[0]) for m in moments], pa.string()),
        *(pa.array([m[j] for m in moments], pa.int64()) for j in (1, 2, 3)),
    ]


def of_columns(table: pa.Table, i: int) -> list[Moments]:
    """Measure `i`'s moments from the state's columns."""
    e, nan, pinf, ninf = (table.column(c).to_pylist() for c in extra_names(i))
    return [[int(a), b, c, d] for a, b, c, d in zip(e, nan, pinf, ninf, strict=True)]


def names(exact: Sequence[tuple[int, bool]]) -> list[str]:
    """The extra columns of every exact measure."""
    return [c for i, _ in exact for c in extra_names(i)]


def strip(table: pa.Table, exact: Sequence[tuple[int, bool]]) -> pa.Table:
    """The state's columns the engine's plans read."""
    extra = set(names(exact))
    return table.select([c for c in table.column_names if c not in extra])


def attach(
    state: pa.Table,
    keys: Sequence[str],
    exact: Sequence[tuple[int, bool]],
    old: dict[int, dict[tuple, Moments]],
    delta: dict[int, dict[tuple, Moments]],
    check: bool,
) -> pa.Table:
    """`state` (the engine's columns) with each exact measure's moments, the
    old ones of its group plus the change's, and its `__s` the finished
    value. With `check`, raise where the written plan raises."""
    ks = [key_of(list(r.values())) for r in state.select(list(keys)).to_pylist()]
    zero = [0, 0, 0, 0]
    for i, avg in exact:
        mos = [add(old.get(i, {}).get(k, zero), delta.get(i, {}).get(k, zero)) for k in ks]
        ns = state.column(f"__n{i}").to_pylist()
        done = [finish(mo, n or 0, avg) for mo, n in zip(mos, ns, strict=True)]
        if check:
            for mo, v in zip(mos, done, strict=True):
                if why := raises(mo, v):
                    raise ValueError(why)
        at = state.column_names.index(f"__s{i}")
        state = state.set_column(at, f"__s{i}", pa.array(done, pa.float64()))
        for f, col in zip(extra_fields(i), to_columns(mos), strict=True):
            state = state.append_column(f, col)
    return state


def moments_by_key(
    table: pa.Table, keys: Sequence[str], exact: Sequence[tuple[int, bool]]
) -> dict[int, dict[tuple, Moments]]:
    """The moments a state table holds, per measure and group."""
    ks = [key_of(list(r.values())) for r in table.select(list(keys)).to_pylist()]
    return {i: dict(zip(ks, of_columns(table, i), strict=True)) for i, _ in exact}


def fold_contributions(
    contrib: pa.Table, keys: Sequence[str], exact: Sequence[tuple[int, bool]]
) -> dict[int, dict[tuple, Moments]]:
    """The moments of each exact measure in a table of contributions (the
    keys, `__n<i>` the weight a counted value has, `__s<i>` the value)."""
    k = contrib.select(list(keys))
    return {
        i: fold(
            k,
            contrib.column(f"__s{i}").combine_chunks(),
            contrib.column(f"__n{i}").combine_chunks(),
        )
        for i, _ in exact
    }
