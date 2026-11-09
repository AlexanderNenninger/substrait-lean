"""Window functions on Polars (`polars_engine.Windows`) against an oracle.

The translation computes ranks, NTILE and aggregates over frames with
Polars's own expressions. The oracle here is the row-by-row computation it
replaced: each row's frame taken as `Frame.rows` takes it and folded as
`WinFn.valueIn` does, in Python. Both see the rows in the same order (a
stable sort by the window's keys), so ties come out alike and everything
but double sums is compared exactly. Double `SUM` and `AVG` add the frame's
own values in another order (`window_sum_algo` `RUNNING_ADD` or `TREE`,
polars-window-agg), so they are compared within the bound any two summation
orders of the frame keep: `2 γₙ Σ|x|` apart for `n` values (D25), the mean
that divided by `n` plus a rounding of each quotient.
"""

from __future__ import annotations

import datetime as dt
import json
import math
from decimal import Decimal
from functools import cmp_to_key
from typing import Any

import pyarrow as pa
import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

pl = pytest.importorskip("polars")
from sverify_polars import engine as polars_engine  # noqa: E402

pytestmark = pytest.mark.backend("polars")

# --- The oracle: `WinFn.valueIn`, row by row ------------------------------


def _key(v: Any) -> Any:
    """A value as `Value` equality sees it: one zero and one NaN."""
    if isinstance(v, float):
        return "nan" if math.isnan(v) else v + 0.0
    return v


def _le(a: Any, b: Any, desc: bool, nulls_first: bool) -> bool:
    """`SortKey.le` on one key's values: NaN above every double."""
    if a is None or b is None:
        ra = (0 if nulls_first else 1) if a is None else (1 if nulls_first else 0)
        rb = (0 if nulls_first else 1) if b is None else (1 if nulls_first else 0)
        return ra <= rb
    if isinstance(a, float):
        a, b = ((1, 0.0) if math.isnan(x) else (0, x + 0.0) for x in (a, b))
    return b <= a if desc else a <= b


def _sort_le(sort: list, a: tuple, b: tuple) -> bool:
    for c, desc, nf in sort:
        if not _le(a[c], b[c], desc, nf):
            return False
        if not _le(b[c], a[c], desc, nf):
            return True
    return True


def _frame_rows(frame: tuple, sort: list, rows: list, i: int) -> list[int]:
    """`Frame.rows`: the positions (in the partition `rows`) of row `i`'s frame."""
    rng, lo, hi = frame
    if not rng:
        lo_i = 0 if lo[0] == "unbounded" else i + (lo[1] if lo[0] == "following" else -lo[1])
        hi_i = (
            len(rows) - 1
            if hi[0] == "unbounded"
            else i + (hi[1] if hi[0] == "following" else -hi[1])
        )
        return [j for j in range(len(rows)) if lo_i <= j <= hi_i]
    x = rows[i]

    def ok(y: tuple, b: tuple[str, int], lower: bool) -> bool:
        side, k = b
        if side == "unbounded":
            return True
        if k == 0:
            return _sort_le(sort, x, y) if lower else _sort_le(sort, y, x)
        d = k if side == "following" else -k
        c, desc, nf = sort[0]
        # Dates count in days.
        vx, vy = (v.toordinal() if isinstance(v, dt.date) else v for v in (x[c], y[c]))
        if vx is None and vy is None:
            return True
        if vx is None or vy is None:
            # NULLs are at one end: `y` is in the frame only on the unbounded side.
            rx = (0 if nf else 1) if vx is None else (1 if nf else 0)
            ry = (0 if nf else 1) if vy is None else (1 if nf else 0)
            return rx < ry if lower else ry < rx
        if lower:
            return vy <= vx - d if desc else vx + d <= vy
        return vx - d <= vy if desc else vy <= vx + d

    return [j for j, y in enumerate(rows) if ok(y, lo, True) and ok(y, hi, False)]


def _fold(agg: str, vs: list) -> Any:
    """`Measure.eval` of a frame's non-NULL values, as the old translation
    folded them: doubles added in the frame's order from 0.0."""
    if agg == "count":
        return len(vs)
    if not vs:
        return None
    if agg in ("sum", "dsum"):
        return sum(vs)
    if agg == "iavg":
        q = abs(sum(vs)) // len(vs)
        return q if sum(vs) >= 0 else -q
    if agg in ("fsum", "avg"):
        acc = 0.0
        for v in vs:
            acc = acc + float(v)
        return acc / len(vs) + 0.0 if agg == "avg" else acc
    if agg in ("fmin", "fmax"):
        nums = [v for v in vs if not math.isnan(v)]
        if not nums or (agg == "fmax" and len(nums) < len(vs)):
            return math.nan
        return (min(nums) if agg == "fmin" else max(nums)) + 0.0
    return min(vs) if agg == "min" else max(vs)


def oracle(rows: list[tuple], part: list[int], sort: list, fn: dict) -> list[tuple[Any, float]]:
    """The window function `fn` of each row, in the stable sort's order, with
    the bound a double sum is checked within (0 elsewhere)."""

    def cmp(a: tuple, b: tuple) -> int:
        return (not _sort_le(sort, a, b)) - (not _sort_le(sort, b, a))

    order = sorted(range(len(rows)), key=cmp_to_key(lambda a, b: cmp(rows[a], rows[b])))
    srows = [rows[r] for r in order]
    groups: dict[tuple, list[int]] = {}
    for r, row in enumerate(srows):
        groups.setdefault(tuple(_key(row[p]) for p in part), []).append(r)
    out: list[tuple[Any, float]] = [(None, 0.0)] * len(srows)
    name = fn["fn"]
    for idx in groups.values():
        prows = [srows[r] for r in idx]
        keys = [tuple(_key(y[c]) for c, _, _ in sort) for y in prows]
        m = len(prows)
        for i, r in enumerate(idx):
            before = [keys[j] for j in range(i) if keys[j] != keys[i]]
            peers_after = sum(1 for j in range(i + 1, m) if keys[j] == keys[i])
            bound = 0.0
            if name == "rank":
                v: Any = len(before) + 1
            elif name == "dense_rank":
                v = len(set(before)) + 1
            elif name == "percent_rank":
                v = 0.0 if m <= 1 else len(before) / (m - 1)
            elif name == "cume_dist":
                v = (i + 1 + peers_after) / m
            elif name == "ntile":
                size, big = divmod(m, fn["n"])
                edge = big * (size + 1)
                v = i // (size + 1) + 1 if i < edge else (i - edge) // size + big + 1
            else:
                frame = [prows[j] for j in _frame_rows(fn["frame"], sort, prows, i)]
                vals = (
                    [y[fn["col"]] for y in frame] if fn.get("col") is not None else [1] * len(frame)
                )
                if name == "first_value":
                    v = vals[0] if vals else None
                elif name == "last_value":
                    v = vals[-1] if vals else None
                elif name == "nth_value":
                    v = vals[fn["n"] - 1] if fn["n"] <= len(vals) else None
                else:
                    xs = [x for x in vals if x is not None]
                    v = _fold(fn["agg"], xs)
                    if fn["agg"] in ("fsum", "avg") and xs and v is not None and math.isfinite(v):
                        n = len(xs)
                        gamma = n * 2.0**-53 / (1 - n * 2.0**-53)
                        bound = 2 * gamma * math.fsum(abs(float(x)) for x in xs)
                        if fn["agg"] == "avg":
                            bound = bound / n + 2.0**-52 * abs(v)
            out[r] = (v, bound)
    return out


# --- Plans ------------------------------------------------------------------

#: Column types of the test table `t(p, k, j, v)`: partition, first sort
#: key, second sort key, value.
TYPES = {
    "int": {"i64": {"nullability": "NULLABILITY_NULLABLE"}},
    "float": {"fp64": {"nullability": "NULLABILITY_NULLABLE"}},
    "date": {"date": {"nullability": "NULLABILITY_NULLABLE"}},
    "decimal": {"decimal": {"precision": 38, "scale": 2, "nullability": "NULLABILITY_NULLABLE"}},
}
ARROW = {
    "int": pa.int64(),
    "float": pa.float64(),
    "date": pa.date32(),
    "decimal": pa.decimal128(38, 2),
}
DIRECTIONS = {
    (False, True): "SORT_DIRECTION_ASC_NULLS_FIRST",
    (False, False): "SORT_DIRECTION_ASC_NULLS_LAST",
    (True, True): "SORT_DIRECTION_DESC_NULLS_FIRST",
    (True, False): "SORT_DIRECTION_DESC_NULLS_LAST",
}


def field(i: int) -> dict:
    return {"selection": {"directReference": {"structField": {"field": i}}, "rootReference": {}}}


def bound_json(b: tuple[str, int]) -> dict:
    side, k = b
    if side == "unbounded":
        return {"unbounded": {}}
    if k == 0:
        return {"currentRow": {}}
    return {side: {"offset": str(k)}}


def plan(types: list[str], part: list[int], sort: list, fn: dict) -> dict:
    """A plan of one window function over `t`, in Lean's written form."""
    w: dict[str, Any] = {
        "functionReference": 1,
        "partitions": [field(p) for p in part],
        "sorts": [{"direction": DIRECTIONS[(d, nf)], "expr": field(c)} for c, d, nf in sort],
        "arguments": [{"value": field(fn["col"])}] if fn.get("col") is not None else [],
    }
    if fn["fn"] in ("ntile", "nth_value"):
        w["arguments"].append({"value": {"literal": {"i64": str(fn["n"])}}})
    if "frame" in fn:
        rng, lo, hi = fn["frame"]
        w["boundsType"] = "BOUNDS_TYPE_RANGE" if rng else "BOUNDS_TYPE_ROWS"
        w["lowerBound"], w["upperBound"] = bound_json(lo), bound_json(hi)
    if fn.get("agg") == "iavg":
        w["outputType"] = {"i64": {"nullability": "NULLABILITY_NULLABLE"}}
    n = len(types)
    return {
        "extensions": [{"extensionFunction": {"functionAnchor": 1, "name": fn["name"]}}],
        "relations": [{"root": {
            "input": {"project": {
                "common": {"emit": {"outputMapping": [*range(n), n]}},
                "expressions": [{"windowFunction": w}],
                "input": {"read": {
                    "baseSchema": {"names": list("pkjv"), "struct": {
                        "types": [TYPES[t] for t in types],
                        "nullability": "NULLABILITY_REQUIRED"}},
                    "namedTable": {"names": ["t"]}}},
            }},
            "names": [*"pkjv", "w"],
        }}],
    }  # fmt: skip


def run(types: list[str], rows: list[tuple], part: list[int], sort: list, fn: dict) -> list:
    table = pa.table(
        {
            c: pa.array([r[i] for r in rows], type=ARROW[t])
            for i, (c, t) in enumerate(zip("pkjv", types, strict=True))
        }
    )
    got = polars_engine.run(json.dumps(plan(types, part, sort, fn)), {"t": table})
    return got.column("w").to_pylist()


def same(got: Any, want: Any, bound: float) -> bool:
    if isinstance(want, float) and isinstance(got, float):
        if math.isnan(want) or math.isnan(got):
            return math.isnan(want) and math.isnan(got)
        if math.isinf(want):
            return got == want
        return abs(got - want) <= bound and (got != 0.0 or math.copysign(1, got) == 1)
    return got == want


def check(types: list[str], rows: list[tuple], part: list[int], sort: list, fn: dict) -> None:
    want = oracle(rows, part, sort, fn)
    got = run(types, rows, part, sort, fn)
    for r, (g, (v, b)) in enumerate(zip(got, want, strict=True)):
        assert same(g, v, b), (r, g, v, b, fn)


# --- Strategies -------------------------------------------------------------

FLOATS = st.one_of(
    st.sampled_from([0.0, -0.0, math.nan, math.inf, -math.inf, 1e16, 1.0, -1.0, 0.1, 2.5]),
    st.floats(-1e6, 1e6),
)
VALUES = {
    "int": st.integers(-5, 5),
    "float": FLOATS,
    "date": st.integers(0, 6).map(lambda d: dt.date(2026, 1, 1) + dt.timedelta(days=d)),
    "decimal": st.integers(-(10**6), 10**6).map(lambda u: Decimal(u).scaleb(-2)),
}
KEYS = {"int": st.integers(0, 6), "float": FLOATS, "date": VALUES["date"]}


def bounds(rng: bool, keyed: bool) -> st.SearchStrategy:
    """A frame's two bounds; offsets of a RANGE frame only over an integer or date key."""
    offsets = st.integers(0, 3) if (keyed or not rng) else st.just(0)
    side = st.tuples(st.sampled_from(["preceding", "following"]), offsets)
    one = st.one_of(st.just(("unbounded", 0)), side)
    return st.tuples(one, one)


@st.composite
def cases(draw) -> tuple:
    key = draw(st.sampled_from(list(KEYS)))
    value = draw(st.sampled_from(list(VALUES)))
    types = ["int", "float" if key == "float" else key, "int", value]
    n = draw(st.integers(0, 14))
    rows = [
        (
            draw(st.one_of(st.none(), st.integers(0, 2))),
            draw(st.one_of(st.none(), KEYS[key])),
            draw(st.one_of(st.none(), st.integers(0, 2))),
            draw(st.one_of(st.none(), VALUES[value])),
        )
        for _ in range(n)
    ]
    part = draw(st.sampled_from([[], [0], [0, 2]]))
    nkeys = draw(st.sampled_from([0, 1, 1, 2]))
    sort = [(c, draw(st.booleans()), draw(st.booleans())) for c in [1, 2][:nkeys]]
    rng = draw(st.booleans())
    lo, hi = draw(bounds(rng, nkeys == 1 and key in ("int", "date")))
    frame = (rng, lo, hi)
    aggs = {
        "int": ["count", "sum", "iavg", "avg", "min", "max"],
        "float": ["count", "fsum", "avg", "fmin", "fmax"],
        "date": ["count", "min", "max"],
        "decimal": ["count", "dsum", "min", "max"],
    }[value]
    kind = draw(st.sampled_from(["rank", "frame", "frame", "agg", "agg", "agg"]))
    if kind == "rank":
        name = draw(st.sampled_from(["rank", "dense_rank", "percent_rank", "cume_dist", "ntile"]))
        fn: dict[str, Any] = {"fn": name, "name": name, "n": draw(st.integers(1, 5))}
    elif kind == "frame":
        name = draw(st.sampled_from(["first_value", "last_value", "nth_value"]))
        fn = {"fn": name, "name": name, "col": 3, "frame": frame, "n": draw(st.integers(1, 4))}
    else:
        agg = draw(st.sampled_from(aggs))
        name = {"fsum": "sum", "dsum": "sum", "iavg": "avg", "fmin": "min", "fmax": "max"}.get(
            agg, agg
        )
        star = agg == "count" and draw(st.booleans())
        fn = {"fn": "agg", "name": name, "agg": agg, "col": None if star else 3, "frame": frame}
    return types, rows, part, sort, fn


@settings(max_examples=400, deadline=None)
@given(cases())
def test_native_windows_match_the_row_by_row_oracle(case):
    check(*case)


# --- Cases the strategies reach rarely --------------------------------------


def test_a_moving_sum_of_doubles_sums_each_frames_own_values():
    """`[1e16, 1, 1, 1, 1]` over `ROWS 1 PRECEDING`: the frames `[1, 1]` give
    2.0, which a sliding accumulator (Polars's `rolling_sum`) would miss
    (`window_sum_algo`, polars-window-agg)."""
    rows = [(None, i, None, v) for i, v in enumerate([1e16, 1.0, 1.0, 1.0, 1.0])]
    fn = {"fn": "agg", "name": "sum", "agg": "fsum", "col": 3,
          "frame": (False, ("preceding", 1), ("preceding", 0))}  # fmt: skip
    assert run(["int", "int", "int", "float"], rows, [], [(1, False, False)], fn) == [
        1e16, 1e16, 2.0, 2.0, 2.0
    ]  # fmt: skip


@pytest.mark.parametrize("width", [1, 2, 3, 7, 8, 9, 40])
def test_block_sums_cover_frames_of_every_width(width):
    """A `ROWS` frame of `width` rows over 100 rows, summed by blocks."""
    rows = [(i % 3, i, None, float(i * i % 17) - 8.0) for i in range(100)]
    for agg in ("fsum", "fmax"):
        before, after = width // 2, width - 1 - width // 2
        fn = {"fn": "agg", "name": "sum" if agg == "fsum" else "max", "agg": agg, "col": 3,
              "frame": (False, ("preceding", before), ("following", after))}  # fmt: skip
        check(["int", "int", "int", "float"], rows, [0], [(1, False, False)], fn)


def test_an_integer_window_sum_that_leaves_64_bits_raises():
    rows = [(None, i, None, 2**62) for i in range(3)]
    fn = {"fn": "agg", "name": "sum", "agg": "sum", "col": 3,
          "frame": (False, ("preceding", 1), ("preceding", 0))}  # fmt: skip
    with pytest.raises(polars_engine.SumOverflow):
        run(["int", "int", "int", "int"], rows, [], [(1, False, False)], fn)


def test_decimal_window_sums_are_exact_near_38_digits():
    """Unscaled values near 10³⁸ sum in two limbs: a frame whose sum fits
    is exact although the running sum would leave 128 bits, and one that
    does not fit raises."""
    big = Decimal(9 * 10**37).scaleb(-2)
    cent = Decimal(1).scaleb(-2)
    rows = [(None, i, None, v) for i, v in enumerate([big] * 5 + [-big, cent])]
    types = ["int", "int", "int", "decimal"]
    own = {"fn": "agg", "name": "sum", "agg": "dsum", "col": 3,
           "frame": (False, ("preceding", 0), ("preceding", 0))}  # fmt: skip
    assert run(types, rows, [], [(1, False, False)], own) == [big] * 5 + [-big, cent]
    pairs = {**own, "frame": (False, ("preceding", 1), ("preceding", 0))}
    assert run(types, rows[4:], [], [(1, False, False)], pairs) == [
        big,
        Decimal(0).scaleb(-2),
        Decimal(f"{1 - 9 * 10**37}e-2"),
    ]  # exact: `scaleb` rounds to 28 digits
    with pytest.raises(polars_engine.SumOverflow):
        run(types, rows, [], [(1, False, False)], pairs)


def test_window_plans_stream_without_python():
    """No window function runs Python: the streaming plan has no fallback
    node and no `map_batches` (#444, polars-exec-streaming-fallback)."""
    fn = {"fn": "agg", "name": "avg", "agg": "avg", "col": 3,
          "frame": (True, ("preceding", 2), ("following", 1))}  # fmt: skip
    types = ["int", "date", "int", "float"]
    p = plan(types, [0], [(1, False, True)], fn)
    table = pa.table({c: pa.array([], type=ARROW[t]) for c, t in zip("pkjv", types, strict=True)})
    # Without guards: a guard raises from Python, as for every operator.
    lf, _ = polars_engine._translate(json.dumps(p), {"t": table}, frozenset())
    assert polars_engine.fallback_nodes(lf) == []
    assert "python" not in lf.explain(optimizations=polars_engine._OPTIMIZATIONS).lower()
