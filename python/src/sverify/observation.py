"""Postconditions that name the observation (#444, decisions D11, D12 and
D18 of `docs/core-semantics.md`).

An observation says which differences between two results a consumer
ignores: the order of the rows, the last bits of a double, the sign of a
zero, a timestamp's sub-millisecond digits, the Unicode normal form of a
string. A transformation states it in its `ensures`:

    @sv.transform(
        ensures=[
            sv.equivalent(rows="multiset", floats=sv.within(rel=1e-9)),
            _.total >= 0,
        ]
    )

An engine's result then counts as correct when it is equal, up to the
observation, to a
result the reference allows. Without `equivalent`, rows are a multiset,
doubles are within the plan's bound (`floats="plan"`) and every other value
is exact.

An observation is a product of components, each a short chain from exact
to coarse. One refines another (`a.refines(b)`) when it is at least as fine
on every
component, so refinement is a partial order (D18). Every other condition in
`ensures` must not tell results equal up to the observation apart:
`dependencies` names the components a condition reads that it ignores (D12).
"""

from __future__ import annotations

import math
import struct
import unicodedata
from collections.abc import Collection, Mapping, Sequence
from dataclasses import dataclass, field
from typing import Any, Literal

import pyarrow as pa
import pyarrow.compute as pc

Rows = Literal["sequence", "ties permuted", "multiset"]
Elements = Literal["sequence", "multiset"]
Exactness = Literal["exact", "canon"]
Precision = Literal["ns", "us", "ms", "s"]
Strings = Literal["exact", "nfc"]
Decimals = Literal["exact", "value"]
Errors = Literal["exact", "kind"]

_ROWS: tuple[str, ...] = ("sequence", "ties permuted", "multiset")
_ELEMENTS: tuple[str, ...] = ("sequence", "multiset")
_ZEROS: tuple[str, ...] = ("exact", "canon")
_PRECISIONS: tuple[str, ...] = ("ns", "us", "ms", "s")
_STRINGS: tuple[str, ...] = ("exact", "nfc")
_DECIMALS: tuple[str, ...] = ("exact", "value")
_ERRORS: tuple[str, ...] = ("exact", "kind")
#: The components in order, with their chains from fine to coarse (floats:
#: exact, then tolerances, ordered by `Within.refines`).
_COMPONENTS: tuple[tuple[str, tuple[str, ...]], ...] = (
    ("rows", _ROWS),
    ("elements", _ELEMENTS),
    ("floats", ()),
    ("zeros", _ZEROS),
    ("timestamps", _PRECISIONS),
    ("strings", _STRINGS),
    ("decimals", _DECIMALS),
    ("errors", _ERRORS),
)


@dataclass(frozen=True)
class Within:
    """A tolerance on doubles (`within`): two values are equal when they
    are within any one of the bounds given."""

    abs: float | None = None
    """At most this far apart."""
    rel: float | None = None
    """At most `rel · max(|x|, |y|)` apart."""
    ulps: int | None = None
    """At most this many units in the last place apart."""

    def __post_init__(self) -> None:
        if self.abs is None and self.rel is None and self.ulps is None:
            raise ValueError("within needs at least one of abs, rel and ulps")
        for name in ("abs", "rel", "ulps"):
            v = getattr(self, name)
            if v is not None and (not math.isfinite(v) or v < 0):
                raise ValueError(f"within's {name} must be a finite number ≥ 0, not {v!r}")

    def refines(self, other: Within) -> bool:
        """Every pair this tolerance accepts, `other` accepts: each bound
        given here is given in `other` and at least as large there."""
        for name in ("abs", "rel", "ulps"):
            mine = getattr(self, name)
            if mine is not None and (getattr(other, name) is None or getattr(other, name) < mine):
                return False
        return True

    def close(self, x: float, y: float) -> bool:
        """Whether `x` and `y` are equal up to this tolerance. NaN equals
        NaN, and an infinity only itself."""
        if math.isnan(x) or math.isnan(y):
            return math.isnan(x) and math.isnan(y)
        if x == y:
            return True
        if math.isinf(x) or math.isinf(y):
            return False
        d = abs(x - y)
        if self.abs is not None and d <= self.abs:
            return True
        if self.rel is not None and d <= self.rel * max(abs(x), abs(y)):
            return True
        return self.ulps is not None and _ulp_distance(x, y) <= self.ulps

    def __str__(self) -> str:
        parts = [f"{n}={getattr(self, n)!r}" for n in ("abs", "rel", "ulps") if getattr(self, n)]
        return f"within({', '.join(parts)})"


def _ordered_bits(x: float) -> int:
    """The bits of a double as an integer that orders as the doubles do."""
    (n,) = struct.unpack("<q", struct.pack("<d", x))
    return n if n >= 0 else -(n & 0x7FFF_FFFF_FFFF_FFFF)


def _ulp_distance(x: float, y: float) -> int:
    return abs(_ordered_bits(x) - _ordered_bits(y))


def within(abs: float | None = None, rel: float | None = None, ulps: int | None = None) -> Within:
    """A tolerance for `equivalent(floats=...)`: two doubles are equal when
    they are at most `abs` apart, at most `rel · max(|x|, |y|)` apart, or at
    most `ulps` units in the last place apart (any one suffices).

    A tolerance with smaller bounds refines one with larger bounds (D18);
    tolerances on different bounds (`abs` and `rel`) are incomparable.
    """
    return Within(abs, rel, ulps)


Floats = Literal["exact", "plan"] | Within


@dataclass(frozen=True)
class Observation:
    """What a consumer of a result observes (`equivalent`), as a product of
    components, each from exact to coarse. Use it in `ensures`."""

    rows: Rows = "multiset"
    """`"multiset"`: the order of the rows is ignored; `"sequence"`: it counts;
    `"ties permuted"`: the order counts up to permutations of rows that tie
    in the sort (an engine's run-to-run variation, `tie_order`)."""
    floats: Floats = "exact"
    """`"exact"`: the same bits; a tolerance (`within`); or `"plan"`: within
    the bound the checker computes for the plan (`Report.epsilon`, its `ε`
    per double column), whatever it is. `"plan"` is what `ensures` observes
    when it names no observation, and the default of a sink's
    `reproducible`. A double column a postcondition reads is held to its
    exact value under `"plan"` (`sv.approx` allows for the bound)."""
    zeros: Exactness = "exact"
    """`"canon"`: `-0.0` equals `0.0`, and every NaN equals every other."""
    timestamps: Precision = "ns"
    """The finest precision observed: `"us"` ignores nanoseconds, `"ms"`
    microseconds, `"s"` milliseconds."""
    strings: Strings = "exact"
    """`"nfc"`: strings equal after Unicode normalisation (NFC)."""
    decimals: Decimals = "exact"
    """`"value"`: `1.50` equals `1.5`; the scale is ignored."""
    errors: Errors = "exact"
    """`"kind"`: two errors of the same kind are equal, whatever their messages."""
    elements: Elements = "sequence"
    """`"multiset"`: the order of a list's elements is ignored (a `collect`
    or `string_agg` without an order); `"sequence"`: it counts."""
    bound: Within | None = field(default=None, compare=False)
    """With `floats="plan"`, the plan's bound as a tolerance, where the
    report knows it (`Report.observation`): printed beside `floats=plan`,
    and used by `equal`. Equality of observations ignores it. Without it,
    `equal` compares doubles under `"plan"` exactly."""

    def __post_init__(self) -> None:
        for name, allowed in _COMPONENTS:
            if name != "floats" and getattr(self, name) not in allowed:
                raise ValueError(
                    f"equivalent's {name} must be one of {', '.join(map(repr, allowed))}, "
                    f"not {getattr(self, name)!r}"
                )
        if self.floats not in ("exact", "plan") and not isinstance(self.floats, Within):
            raise ValueError(
                "equivalent's floats must be 'exact', 'plan' or sv.within(...), "
                f"not {self.floats!r}"
            )

    # -- the refinement order (D18) ------------------------------------------

    def refines(self, other: Observation) -> bool:
        """`self` observes everything `other` observes, on every component:
        equality up to `self` implies equality up to `other`."""
        return not self.coarser_than(other)

    def coarser_than(self, other: Observation) -> list[str]:
        """The components on which `self` is not as fine as `other`: what
        `self` ignores that `other` observes. Empty when `self` refines
        `other`."""

        def chain(name: str, levels: Sequence[str]) -> bool:
            return levels.index(getattr(self, name)) > levels.index(getattr(other, name))

        mine, theirs = self.floats, other.floats
        # exact refines everything; `"plan"` (the plan's ε, unknown here)
        # refines only itself; a tolerance refines a larger one.
        if mine == "exact" or mine == theirs:
            floats = False
        elif mine == "plan" or theirs != "plan" and not isinstance(theirs, Within):
            floats = True
        else:
            floats = theirs == "plan" or not mine.refines(theirs)  # type: ignore[union-attr]
        return [
            name
            for name, levels in _COMPONENTS
            if (floats if name == "floats" else chain(name, levels))
        ]

    def ignored(self) -> list[str]:
        """The components this observation ignores: where it is coarser
        than the identity, the finest observation."""
        return self.coarser_than(EXACT)

    # -- the canonical map and equality --------------------------------------

    def canonical(self, table: pa.Table) -> pa.Table:
        """`table`'s canonical representative under this observation: zeros
        and NaNs made one (`zeros="canon"`), timestamps truncated, strings
        normalised, and, for a multiset, the rows sorted. Doubles with a
        tolerance are kept as they are; `equal` compares them."""
        columns = [self._canon_column(c) for c in table.columns]
        out = pa.Table.from_arrays(columns, names=table.column_names)
        if self.rows == "multiset" and out.num_rows > 1 and out.num_columns:
            # Doubles last, so that a tolerance mostly leaves pairs aligned.
            keys = [
                n for n, c in zip(out.column_names, out.columns, strict=True) if _sortable(c.type)
            ]
            keys.sort(key=lambda n: pa.types.is_floating(out.column(n).type))
            if keys:
                order = [(k, "ascending", "at_end") for k in keys]
                out = out.take(
                    pc.call_function("sort_indices", [out], pc.SortOptions(sort_keys=order))
                )
        return out

    def _canon_column(self, c: pa.ChunkedArray) -> pa.ChunkedArray:
        t = c.type
        if pa.types.is_floating(t) and self.zeros == "canon":
            nan = pa.scalar(float("nan"), t)
            zero = pc.call_function("add", [c, pa.scalar(0.0, t)])
            return pc.call_function("if_else", [pc.call_function("is_nan", [c]), nan, zero])
        if pa.types.is_timestamp(t) and _PRECISIONS.index(self.timestamps) > _PRECISIONS.index(
            t.unit
        ):
            unit = {"us": "microsecond", "ms": "millisecond", "s": "second"}[self.timestamps]
            return pc.call_function("floor_temporal", [c], pc.RoundTemporalOptions(unit=unit))
        if pa.types.is_list(t) and self.elements == "multiset":
            return pa.chunked_array(
                [[None if v is None else sorted(v, key=_order_key) for v in c.to_pylist()]],
                type=t,
            )
        if (pa.types.is_string(t) or pa.types.is_large_string(t)) and self.strings == "nfc":
            return pa.chunked_array(
                [[None if v is None else unicodedata.normalize("NFC", v) for v in c.to_pylist()]],
                type=t,
            )
        return c

    def equal(self, a: pa.Table, b: pa.Table) -> bool:
        """Whether two results are equal up to this observation."""
        return self.difference(a, b) is None

    def difference(self, a: pa.Table, b: pa.Table) -> str | None:
        """Where two results differ up to this observation, in words; None
        when they are equal."""
        if a.column_names != b.column_names:
            return f"columns {a.column_names} and {b.column_names}"
        if a.num_rows != b.num_rows:
            return f"{a.num_rows} and {b.num_rows} rows"
        if self.decimals == "exact":
            for name in a.column_names:
                ta, tb = a.schema.field(name).type, b.schema.field(name).type
                if pa.types.is_decimal(ta) and pa.types.is_decimal(tb) and ta.scale != tb.scale:
                    return f"column {name}: scales {ta.scale} and {tb.scale}"
        # Decimals compare by value from here on (`Decimal("1.50") == Decimal("1.5")`).
        ca, cb = self.canonical(a), self.canonical(b)
        for name in ca.column_names:
            xs, ys = ca.column(name).to_pylist(), cb.column(name).to_pylist()
            for i, (x, y) in enumerate(zip(xs, ys, strict=True)):
                if not self._same(x, y):
                    return f"row {i} of column {name}: {x!r} and {y!r}"
        return None

    def _same(self, x: Any, y: Any) -> bool:
        if x is None or y is None:
            return x is None and y is None
        if isinstance(x, float) and isinstance(y, float):
            if isinstance(self.floats, Within):
                return self.floats.close(x, y)
            if self.floats == "plan" and self.bound is not None:
                return self.bound.close(x, y)
            if math.isnan(x) or math.isnan(y):
                return math.isnan(x) and math.isnan(y)
            return x == y and (self.zeros == "canon" or math.copysign(1, x) == math.copysign(1, y))
        if isinstance(x, list) and isinstance(y, list):
            return len(x) == len(y) and all(self._same(u, v) for u, v in zip(x, y, strict=True))
        if isinstance(x, dict) and isinstance(y, dict):
            return x.keys() == y.keys() and all(self._same(x[k], y[k]) for k in x)
        return x == y

    def __str__(self) -> str:
        parts = []
        for f, _levels in _COMPONENTS:
            v = getattr(self, f)
            if f == "floats" and v == "plan":
                parts.append("floats=plan")
                if self.bound is not None:
                    parts.append(f"≤ {_bound_text(self.bound)}")
            elif isinstance(v, Within):
                parts.append(f"{f}={v}")
            elif v != getattr(EXACT_MULTISET, f):
                parts.append(f"{f}={v!r}")
        return f"equivalent({', '.join(parts)})"

    def __repr__(self) -> str:
        return str(self)

    @property
    def label(self) -> str:
        return str(self)


def _bound_text(w: Within) -> str:
    """A plan's bound as `observes:` prints it: `2.0e-07` where it has only
    an absolute bound, the kinds otherwise."""
    kinds = [(n, getattr(w, n)) for n in ("abs", "rel", "ulps") if getattr(w, n) is not None]
    if [n for n, _ in kinds] == ["abs"]:
        return f"{w.abs:.1e}"
    return ", ".join(f"{n}={v:.1e}" if n != "ulps" else f"{n}={v}" for n, v in kinds)


def _order_key(v: Any) -> tuple:
    """A total order on list elements: NULLs last, NaN after numbers."""
    if v is None:
        return (2, 0)
    if isinstance(v, float) and math.isnan(v):
        return (1, 0)
    return (0, v)


def from_json(q: Mapping[str, Any] | None) -> Observation:
    """An observation as the checker writes it (a choices row's `"observation"`, D15):
    component levels, a float tolerance as `{"abs", "rel", "ulps"}`; an
    absent component is exact, rows and elements included."""
    q = dict(q or {})
    floats = q.pop("floats", "exact")
    if isinstance(floats, Mapping) and floats.get("bound") == "plan":
        # Within the plan's bound (`ObsRow.approxWithin "plan"`).
        floats = "plan"
    elif isinstance(floats, Mapping):
        floats = Within(floats.get("abs"), floats.get("rel"), floats.get("ulps"))
    known = {name for name, _ in _COMPONENTS}
    unknown = set(q) - known
    if unknown:
        raise ValueError(f"unknown components of an observation: {sorted(unknown)}")
    return Observation(
        **{"rows": "sequence", "elements": "sequence", **q, "floats": floats}  # type: ignore[arg-type]
    )


def _sortable(t: pa.DataType) -> bool:
    return not (pa.types.is_nested(t) or pa.types.is_dictionary(t) or pa.types.is_null(t))


#: The identity: every component exact, rows as a sequence.
EXACT = Observation(rows="sequence")
#: The default when `ensures` names none: rows as a multiset, values exact.
EXACT_MULTISET = Observation()
#: Rows as a multiset, doubles within the plan's bound (`Report.epsilon`),
#: other values exact: what `ensures` observes where it names no
#: observation (`Report.observation`), and what a sink's rerun must
#: reproduce by default.
PLAN_BOUND = Observation(floats="plan")


def equivalent(
    rows: Rows = "multiset",
    floats: Floats = "exact",
    *,
    zeros: Exactness = "exact",
    timestamps: Precision = "ns",
    strings: Strings = "exact",
    decimals: Decimals = "exact",
    errors: Errors = "exact",
    elements: Elements = "sequence",
) -> Observation:
    """A postcondition naming what the result's consumer observes (#444, D11).

    Put it in a transformation's `ensures` (or `sv.verify`'s). An engine's
    result is then correct when it equals, up to this observation, a result
    the reference allows. Without it, rows are a multiset, doubles are
    within the plan's bound (`floats="plan"`) and every other value is
    exact. With it, each component you leave out is exact: `floats="exact"`
    asks for the same bits, which `verify` says which engines give.

    Args:
        rows: `"multiset"` (the default) ignores the order of the rows;
            `"sequence"` observes it, and needs a plan whose result is
            sorted on a total order.
        floats: `"exact"` (the default here), the same bits; a tolerance,
            `sv.within(abs=…, rel=…, ulps=…)`, which `verify` checks
            against the plan's bound; or `"plan"`: within the bound the
            checker computes for the plan (`Report.epsilon`), what
            `ensures` observes without `equivalent`, and the default of a
            sink's `reproducible`.
        zeros: `"canon"` makes `-0.0` equal `0.0` and every NaN equal.
        timestamps: The finest precision observed: `"ms"` ignores
            microseconds and nanoseconds. Default `"ns"`, every digit.
        strings: `"nfc"` compares strings after Unicode normalisation.
        decimals: `"value"` ignores a decimal's scale (`1.50` equals `1.5`).
        errors: `"kind"` ignores an error's message.
        elements: `"multiset"` ignores the order of a list's elements, as a
            `collect` without an order leaves it.

    Returns:
        An `Observation`, for `ensures`.

    Raises:
        ValueError: A component's level is unknown.

    Examples:
        ```python
        @sv.transform(ensures=[sv.equivalent(floats=sv.within(rel=1e-9)), _.avg >= 0])
        def stats(t):
            return t.group_by("k").aggregate(avg=t.x.mean())
        ```
    """
    return Observation(rows, floats, zeros, timestamps, strings, decimals, errors, elements)


def split(ensures: Sequence[Any]) -> tuple[Observation | None, list[Any]]:
    """The observation among `ensures` (None if there is none) and the
    other conditions."""
    found = [c for c in ensures if isinstance(c, Observation)]
    if len(found) > 1:
        raise ValueError(f"ensures names {len(found)} observations; give one sv.equivalent(...)")
    return (found[0] if found else None), [c for c in ensures if not isinstance(c, Observation)]


# -- which conditions depend on what the observation ignores (D12) -----------


#: The component a column's type falls under, where an observation may coarsen it.
def _component(dtype: Any) -> str | None:
    if dtype.is_floating():
        return "floats"
    if dtype.is_timestamp():
        return "timestamps"
    if dtype.is_string():
        return "strings"
    if dtype.is_decimal():
        return "decimals"
    return None


def dependencies(
    observation: Observation,
    cond: Any,
    columns: Mapping[str, Any],
    read: Sequence[str] | None,
    open_columns: Mapping[str, str] | None = None,
    order_free: Collection[str] = (),
) -> list[str]:
    """The components `observation` ignores that `cond`, a condition of
    `ensures`, depends on (D12). Empty when the condition cannot tell
    results equal up to `observation` apart.

    Conditions on each row (Ibis and SQL conditions) and the table
    conditions (`unique`, `references`, `max_rows`, `rows_per`) ignore the
    order of the rows. A condition depends on the values of the columns it
    reads, unless the observation keeps them: doubles with a tolerance
    (only `approx` conditions allow for one), timestamps truncated, strings
    normalised, decimals without their scale. Zeros and NaNs made one
    change no comparison of the reference's, which has one of each.

    Args:
        observation: The postcondition's observation.
        cond: The condition.
        columns: The output's columns by name, with Ibis types.
        read: The columns `cond` reads; None if unknown, which counts as
            every column.
        open_columns: Output columns whose value the reference leaves open
            (D1): `"picks"` for `first` or `last` without an order (which
            row's value), `"elements"` for a `collect` without one (the
            order of the elements). A condition that reads one depends on
            that choice, unless it reads a list only through functions that
            ignore its order (`order_free`).
        order_free: The columns `cond` reads only through such functions
            (`length`, `contains`, `min`, `max`, `sum`, `sort`, …).
    """
    from sverify.contracts import Approx

    names = list(columns) if read is None else [n for n in read if n in columns]
    out: list[str] = []
    for n in names:
        why_open = (open_columns or {}).get(n)
        if why_open == "elements" and n in order_free:
            continue
        if why_open is not None and why_open not in out:
            out.append(why_open)
    ignored = set(observation.ignored()) - {"rows", "zeros", "errors", "elements"}
    for n in names:
        comp = _component(columns[n])
        if comp is None or comp not in ignored or comp in out:
            continue
        if comp == "floats" and (isinstance(cond, Approx) or observation.floats == "plan"):
            # Under the plan's bound, a run holds the columns a condition
            # reads to their exact value (`sverify.routes.observed`).
            continue
        out.append(comp)
    return out


def why(components: Sequence[str]) -> str:
    """How a report names what a condition depends on."""
    opened = [c for c in components if c in ("picks", "elements")]
    ignored = [c for c in components if c not in opened]
    parts = []
    if opened:
        names = {
            "picks": "which row FIRST or LAST picks",
            "elements": "the order of a list's elements",
        }
        parts.append(
            f"depends on {' and '.join(names[c] for c in opened)}, which the plan leaves open"
        )
    if ignored:
        parts.append(f"depends on {', '.join(ignored)}, which the observation ignores")
    return "; ".join(parts)
