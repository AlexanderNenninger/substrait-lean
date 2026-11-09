"""Sharded evaluation: run a plan on each shard of its data, then combine.

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release.

    import sverify.partition as sp

    s = sp.split(plan_json, sharded=["orders"])      # or NotShardable, saying why
    result = sp.run_sharded(plan_json, shards, sharded=["orders"], broadcast={"customers": c})

A shard holds some of the rows of each sharded table (a Delta or Iceberg
partition, a file, a worker's slice); every other table is broadcast, a copy
on each shard. `split` asks `substrait-check --shard` for the plan each shard
runs and the plan that combines their results, or raises `NotShardable` with
the reason. Lean proves the combined result is the plan's result on all the
data (`Rel.shardSplit_sound` in `SubstraitLean/Partition.lean`). A linear
plan runs on every shard and the results are concatenated (`Split.mode`
`"linear"`); an aggregate runs in two phases, each shard aggregating by the
grouping keys and the combining plan aggregating the partial rows again
(`"two_phase"`).

`run_sharded` (`sverify.engines.run_sharded`) runs the shards on Polars, in
parallel threads. It first checks the split keys (`keys=`) and the `unique=`
column sets on the data (`check_keys`, `check_unique`).

Which plans split, which are refused and why, and why a 64-bit partial sum
can fail where the total would not: docs/optimizations.md, "2. Sharded
evaluation".

`float_order="any"` splits `SUM`/`AVG` of doubles anyway: `Split.proved`
is then false, and `Split.float_bounds` says which output columns are within
a tolerance τ of Lean's value. `run_sharded(..., tolerance=True)` computes τ
for each group of `n` values from the partial rows (`group_tolerance`), with
`A` the shards' rounded `SUM(|x|)`s added up. τ is the larger of two bounds.
Lean's own split, each shard's exact sum rounded once and then the partials',
is within `A / 2⁵⁰` of the whole's one rounding, and a split mean
within `A / (n · 2⁴⁷) + 2⁻¹⁰⁷⁴` (`shard_tol_cr`, `shard_avg_tol_cr`). An
engine adding the shards in its own order is within `shard_tol_scaled` of
the reference's rounding; its `γ(n)` term covers that rounding, at most
`u = 2⁻⁵³` relatively. A group with NaN or an infinity, near overflow or with
more than 2³² values gets τ = ∞. `apriori_tolerance` gives the bound before
running, from a cap on the rows (a contract's `sv.max_rows`) and a bound on
`|x|`. The bounds and their proofs: docs/float-bounds.md, "Sharded `SUM` and
`AVG`".
"""

from __future__ import annotations

import json
import math
import struct
from collections.abc import Mapping, Sequence
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from fractions import Fraction
from typing import Any, Literal, overload

import pyarrow as pa

from sverify.engine import checker_failed, run_checker
from sverify.observation import Observation, Within

#: The table the combining plan reads the shards' results from.
PARTIALS = "__partials"

#: The engine `run_sharded` runs the shards on, through its plugin's
#: `run_tables`.
SHARD_ENGINE = "polars"

FloatOrder = Literal["exact", "any"]


class NotShardable(ValueError):
    """The plan's result would depend on how the rows are split.

    Raised by `split` and `sverify.engines.run_sharded`, with the reason, for
    example a `SUM` of doubles or a window whose `PARTITION BY` does not
    contain the split key. A subclass of `ValueError`, which is how to catch
    it from `sverify.engines.run_sharded`.
    """


@dataclass(frozen=True)
class Split:
    """A plan split for sharded evaluation, returned by `split`: the plan each
    shard runs, and the plan that combines their results into the plan's
    result on all the data (`Rel.shardSplit_sound`)."""

    mode: Literal["linear", "two_phase"]
    """`"linear"` when the shards' results are concatenated; `"two_phase"`
    when they are aggregated again (see the module docstring)."""
    proved: bool
    """False when `float_order="any"` was needed: sums of doubles then round
    as the split makes them, within the tolerance `float_bounds` locates."""
    partial: dict
    """The plan each shard runs (Lean's written form)."""
    combine: dict
    """The plan that combines the shards' results, read from `PARTIALS`."""
    float_bounds: dict | None = None
    """With split doubles, where their bound is read: `keys` (the partial
    rows' grouping columns), `measures` (per split double: `kind`, and the
    partial columns `abs`, `count`, `max`), `columns` (per output column:
    `{"key": i}`, `{"exact": true}`, `{"bounded": j}` or `{"unbounded": true}`)
    and `filters_read_doubles` (a `HAVING` reads a split double). `None` when
    the split is exact."""

    @property
    def bounded(self) -> dict[int, int]:
        """The output columns within a tolerance of Lean's value, by position,
        each with the index of its measure in `float_bounds["measures"]`."""
        if self.float_bounds is None:
            return {}
        return {
            i: c["bounded"] for i, c in enumerate(self.float_bounds["columns"]) if "bounded" in c
        }


@dataclass(frozen=True)
class Sharded:
    """`run_sharded(..., tolerance=True)`: the result, and how far its split
    doubles may be from Lean's values."""

    table: pa.Table
    """The plan's result, as `run_sharded` returns it."""
    tolerance: dict[str, list[float]] = field(default_factory=dict)
    """Per output column that holds a split double `SUM` or `AVG` (or an
    expression of one), per row: the bound τ on `|value − Lean's value|`.
    `math.inf` where no bound holds: the column is computed from a split
    double by an expression, or its group misses the bound's conditions
    (NaN, an infinity, near overflow, more than 2³² values). Other columns
    are Lean's values."""
    rows_exact: bool = True
    """False when a filter above the aggregate (`HAVING`) reads a split
    double: a group near its threshold may be kept here and dropped by Lean,
    or the reverse. The kept rows are still within `tolerance`."""


def _columns(plan: dict) -> dict[str, list[str]]:
    """Column names of the named tables a plan reads (their `baseSchema`)."""
    found: dict[str, list[str]] = {}

    def walk(node: object) -> None:
        if isinstance(node, dict):
            if "namedTable" in node:
                name = ".".join(node["namedTable"]["names"])
                found[name] = list(node.get("baseSchema", {}).get("names", []))
            for v in node.values():
                walk(v)
        elif isinstance(node, list):
            for v in node:
                walk(v)

    walk(plan)
    return found


def split(
    plan: str | dict,
    sharded: Sequence[str],
    *,
    keys: Mapping[str, Sequence[str]] | None = None,
    unique: Mapping[str, Sequence[Sequence[str]]] | None = None,
    float_order: FloatOrder = "exact",
) -> Split:
    """Split a Substrait plan for evaluation on shards of the tables `sharded`,
    each split on the columns `keys[t]` (if given). `unique[t]` lists column
    sets with no two equal rows in the whole table `t`.

    `split` only splits the plan; it does not check `keys` or `unique` on any
    data (`sverify.engines.run_sharded` does).

    Args:
        plan: A Substrait JSON plan, as a string or parsed.
        sharded: The names of the tables split across shards; every other
            table the plan reads is broadcast.
        keys: Split keys, as a mapping from sharded table name to columns:
            rows with equal values on them are always on the same shard.
            Default: none.
        unique: Keys of whole tables, as a mapping from table name to a list
            of column sets. They let windows run on each shard. Default:
            none.
        float_order: `"exact"` (the default) refuses `SUM` and `AVG` of
            doubles; `"any"` splits them anyway: the result has
            `proved=False` and `float_bounds` set.

    Returns:
        The `Split`.

    Raises:
        NotShardable: The plan's result would depend on how the rows are
            split; the message says why.
        ValueError: `keys` or `unique` name unknown columns, a key is given
            for a table that is not sharded or names no columns, or the
            checker fails on the request.
    """
    p = json.loads(plan) if isinstance(plan, str) else plan
    cols = _columns(p)

    def index(t: str, names: Sequence[str]) -> list[int]:
        missing = [n for n in names if n not in cols.get(t, [])]
        if missing:
            raise ValueError(f"the plan's table {t} has no columns {missing}")
        return [cols[t].index(n) for n in names]

    positions: dict[str, list[int]] = {}
    for t, names in (keys or {}).items():
        if t not in sharded:
            raise ValueError(f"split key for {t}, which is not sharded")
        if not names:
            raise ValueError(f"the split key of {t} names no columns")
        positions[t] = index(t, names)
    uniques = {t: [index(t, names) for names in sets] for t, sets in (unique or {}).items()}
    request = {
        "plan": p,
        "sharded": list(sharded),
        "keys": positions,
        "unique": uniques,
        "float_order": float_order,
    }
    code, out, err = run_checker(("--shard",), json.dumps(request))
    if code == 5:
        raise NotShardable(err.strip())
    if code != 0:
        raise checker_failed("--shard", err)
    j = json.loads(out)
    return Split(j["mode"], j["proved"], j["partial"], j["combine"], j.get("float_bounds"))


#: `2⁵²`: `2⁻¹⁰²²` scaled by `2¹⁰⁷⁴`, and `1 / (2u)`.
_K = 2**52
_SCALE = 2**1074


def _ceil_div(a: int, b: int) -> int:
    return -(-a // b)


def shard_tol_scaled(n: int, m: int, k: int, a: int) -> int:
    """`FloatCode.shardTolScaled` (`core/Sverify/Core/Float.lean`): the bound of a
    split double `SUM`, scaled by `2¹⁰⁷⁴` and rounded up, for `n` values in
    `k` shards of at most `m`, the shards' `SUM(|x|)`s adding up to `a`
    (scaled)."""
    num = ((m + k) * (2 * _K - n) + n * (2 * _K - (m + k))) * (
        (a + n * _K) * (2 * _K - m) + k * _K * (2 * _K - 2 * m)
    )
    return _ceil_div(num, (2 * _K - (m + k)) * (2 * _K - n) * (2 * _K - 2 * m))


def shard_avg_tol_scaled(n: int, m: int, k: int, a: int) -> int:
    """`FloatCode.shardAvgTolScaled`: the same for an `AVG` (`n ≥ 1`)."""
    num = ((m + k + 2) * (2 * _K - (n + 2)) + (n + 2) * (2 * _K - (m + k + 2))) * (
        (a + n * _K) * (2 * _K - m) + k * _K * (2 * _K - 2 * m)
    )
    return _ceil_div(num, (2 * _K - (m + k + 2)) * (2 * _K - (n + 2)) * (2 * _K - 2 * m) * n)


def shard_tol_cr(a: int) -> int:
    """`FloatCode.shardTolCR` (`SubstraitLean/Partition.lean`): the bound of a
    split double `SUM` that Lean computes (each shard's exact sum rounded
    once, then the partials'), scaled: `a / 2⁵⁰`."""
    return a // 2**50


def shard_avg_tol_cr(n: int, a: int) -> int:
    """`FloatCode.shardAvgTolCR`: the same for an `AVG` of `n ≥ 1` values,
    whose split sum is divided natively: `a / (n · 2⁴⁷) + 1`."""
    return a // (n * 2**47) + 1


def _up(q: Fraction) -> float:
    """The smallest double at least `q`."""
    f = float(q)
    return f if Fraction(f) >= q else math.nextafter(f, math.inf)


def _scaled(x: float) -> int:
    """A finite double times `2¹⁰⁷⁴`, an integer."""
    return int(Fraction(x) * _SCALE)


def group_tolerance(
    kind: str, counts: Sequence[int], abs_sums: Sequence[Any], maxima: Sequence[Any]
) -> float:
    """τ for one group of one split double, from its partial rows: each
    shard's `COUNT(x)`, `SUM(|x|)` and `MAX(|x|)` (`floatSplit_sum`,
    `floatSplit_avg`). `math.inf` when the bound's conditions fail."""
    parts = [(c, a, x) for c, a, x in zip(counts, abs_sums, maxima, strict=True) if c]
    n = sum(c for c, _, _ in parts)
    if n == 0:
        return 0.0
    if n > 2**32 or any(
        a is None or x is None or not math.isfinite(a) or not math.isfinite(x) for _, a, x in parts
    ):
        return math.inf
    bs = max(_scaled(x) for _, _, x in parts)
    if n * (bs + 2 * _K) > 2**2096:
        return math.inf
    m = max(c for c, _, _ in parts)
    k = len(parts)
    a = sum(_scaled(a) for _, a, _ in parts)
    if kind == "sum":
        tol = max(shard_tol_scaled(n, m, k, a), shard_tol_cr(a))
    else:
        tol = max(shard_avg_tol_scaled(n, m, k, a), shard_avg_tol_cr(n, a))
    return _up(Fraction(tol, _SCALE))


def apriori_tolerance(
    kind: Literal["sum", "avg"], max_rows: int, bound: float, shards: int
) -> float:
    """τ before running: a split double `SUM` or `AVG` of at most `max_rows`
    values (a contract's `sv.max_rows`), each `|x| ≤ bound`, over `shards`
    shards, is within it of Lean's value (`sharded_near_of_bound`,
    `sharded_avg_near_of_bound` in `float-bounds/FloatBounds/Shard.lean`).

    `(γ(N + k) + γ(N)) · (N·(B + t) + k·t)` for a `SUM` and
    `(γ(N + k + 2) + γ(N + 2)) · (B + t + k·t)` for an `AVG`, with `N` the
    rows, `k = min(N, shards)`, `B` the bound and `t = 2⁻¹⁰²²`.
    """
    if max_rows < 0 or shards < 1 or not bound >= 0:
        raise ValueError("apriori_tolerance needs max_rows ≥ 0, shards ≥ 1 and bound ≥ 0")
    if max_rows == 0:
        return 0.0
    if math.isinf(bound) or max_rows > 2**32:
        return math.inf
    big_n, k = max_rows, min(max_rows, shards)
    u = Fraction(1, 2**53)
    t = Fraction(1, 2**1022)

    def gamma(j: int) -> Fraction:
        return j * u / (1 - j * u)

    b = Fraction(bound)
    if big_n * (b + 2 * t) > 2**1021:
        return math.inf
    # D25: Lean's own split (`shardTolCR`), with `SUM(|x|)` at most
    # `N · B · (1 + u)`, against an engine's order (`Shard.lean`).
    if kind == "sum":
        q = (gamma(big_n + k) + gamma(big_n)) * (big_n * (b + t) + k * t)
        q = max(q, big_n * b * (1 + u) / 2**50)
    else:
        q = (gamma(big_n + k + 2) + gamma(big_n + 2)) * (b + t + k * t)
        q = max(q, b * (1 + u) / 2**47 + Fraction(1, 2**1074))
    return _up(q)


def _canon(v: Any) -> Any:
    """A grouping key's value as Lean compares it: one zero, one NaN, other
    doubles by their bits."""
    if isinstance(v, float):
        if math.isnan(v):
            return ("f", "nan")
        return ("f", struct.pack("<d", v + 0.0))
    return v


def tolerances(s: Split, partials: pa.Table, result: pa.Table) -> Sharded:
    """τ per row of `result` for the split doubles of `s`, from the shards'
    partial rows (`run_sharded(..., tolerance=True)`)."""
    fb = s.float_bounds
    if fb is None:
        return Sharded(result)
    k: int = fb["keys"]
    cols = partials.column_names
    keys = [partials.column(cols[i]).to_pylist() for i in range(k)]
    groups: dict[tuple, list[int]] = {}
    for r, key in enumerate(zip(*keys, strict=True) if k else ([()] * partials.num_rows)):
        groups.setdefault(tuple(map(_canon, key)), []).append(r)
    if not groups:
        groups[()] = []
    per_group: list[dict[tuple, float]] = []
    for meas in fb["measures"]:
        counts = partials.column(cols[meas["count"]]).to_pylist()
        abs_sums = partials.column(cols[meas["abs"]]).to_pylist()
        maxima = partials.column(cols[meas["max"]]).to_pylist()
        per_group.append(
            {
                g: group_tolerance(
                    meas["kind"],
                    [counts[r] for r in rows],
                    [abs_sums[r] for r in rows],
                    [maxima[r] for r in rows],
                )
                for g, rows in groups.items()
            }
        )
    out_cols = fb["columns"]
    key_at = {c["key"]: i for i, c in enumerate(out_cols) if "key" in c}
    rows_of = (
        list(zip(*(result.column(key_at[i]).to_pylist() for i in range(k)), strict=True))
        if k and all(i in key_at for i in range(k))
        else None
    )
    tol: dict[str, list[float]] = {}
    for i, c in enumerate(out_cols):
        name = result.column_names[i]
        if "unbounded" in c:
            tol[name] = [math.inf] * result.num_rows
        elif "bounded" in c:
            by_group = per_group[c["bounded"]]
            if k == 0:
                tol[name] = [by_group[()]] * result.num_rows
            elif rows_of is None:
                # The output does not keep every grouping key: the largest τ
                # of any group bounds each row.
                worst = max(by_group.values(), default=0.0)
                tol[name] = [worst] * result.num_rows
            else:
                tol[name] = [by_group.get(tuple(map(_canon, key)), math.inf) for key in rows_of]
    return Sharded(result, tol, not fb["filters_read_doubles"])


def _key_value(v: Any) -> Any:
    """A key value compared as Lean compares values: doubles by their bits
    (so NaN equals itself and -0.0 differs from 0.0)."""
    return ("f", struct.pack("<d", v)) if isinstance(v, float) else v


def check_keys(shards: Sequence[Mapping[str, pa.Table]], keys: Mapping[str, Sequence[str]]) -> None:
    """Raise unless rows with equal split keys, in any of the keyed tables,
    are on the same shard (`Sharding.keyDisj`)."""
    owner: dict[tuple, int] = {}
    for i, shard in enumerate(shards):
        for t, names in keys.items():
            columns = [shard[t].column(n).to_pylist() for n in names]
            for key in zip(*columns, strict=True):
                k = tuple(map(_key_value, key))
                j = owner.setdefault(k, i)
                if j != i:
                    raise ValueError(
                        f"split key {key} (columns {list(names)} of {t}) is on shards {j} and {i}"
                    )


def check_unique(
    tables: Mapping[str, Sequence[pa.Table]], unique: Mapping[str, Sequence[Sequence[str]]]
) -> None:
    """Raise unless no two rows of a table (all its pieces together) agree
    on any of its `unique` column sets."""
    for t, sets in unique.items():
        for names in sets:
            seen: set[tuple] = set()
            for piece in tables[t]:
                columns = [piece.column(n).to_pylist() for n in names]
                for key in zip(*columns, strict=True):
                    k = tuple(map(_key_value, key))
                    if k in seen:
                        raise ValueError(f"{t} has two rows with {list(names)} = {key}")
                    seen.add(k)


@overload
def run_sharded(
    plan: str | dict,
    shards: Sequence[Mapping[str, pa.Table]],
    *,
    sharded: Sequence[str],
    broadcast: Mapping[str, pa.Table] | None = None,
    keys: Mapping[str, Sequence[str]] | None = None,
    unique: Mapping[str, Sequence[Sequence[str]]] | None = None,
    reproducible: Observation | None = None,
    max_workers: int | None = None,
    tolerance: Literal[False] = False,
    float_order: FloatOrder | None = None,
) -> pa.Table: ...


@overload
def run_sharded(
    plan: str | dict,
    shards: Sequence[Mapping[str, pa.Table]],
    *,
    sharded: Sequence[str],
    broadcast: Mapping[str, pa.Table] | None = None,
    keys: Mapping[str, Sequence[str]] | None = None,
    unique: Mapping[str, Sequence[Sequence[str]]] | None = None,
    reproducible: Observation | None = None,
    max_workers: int | None = None,
    tolerance: Literal[True],
    float_order: FloatOrder | None = None,
) -> Sharded: ...


def run_sharded(
    plan: str | dict,
    shards: Sequence[Mapping[str, pa.Table]],
    *,
    sharded: Sequence[str],
    broadcast: Mapping[str, pa.Table] | None = None,
    keys: Mapping[str, Sequence[str]] | None = None,
    unique: Mapping[str, Sequence[Sequence[str]]] | None = None,
    reproducible: Observation | None = None,
    max_workers: int | None = None,
    tolerance: bool = False,
    float_order: FloatOrder | None = None,
) -> pa.Table | Sharded:
    """The plan's result on all the data, computed shard by shard on Polars.
    This is `sverify.engines.run_sharded`.

    Each shard maps every table of `sharded` to its rows on that shard;
    `broadcast` holds the other tables. The result equals the plan's on the
    concatenated shards, as a bag (row order is not kept). `SUM` and `AVG`
    of doubles round as the split makes them, so they are split only where
    `reproducible` accepts doubles within a tolerance: within the proved
    bound τ, which `tolerance=True` reports, or within a stated tolerance
    that every row's τ meets.

    Before running, the split keys and `unique` column sets are checked on
    the data.

    Args:
        plan: A Substrait JSON plan, as a string or parsed.
        shards: One mapping per shard, from each table of `sharded` to its
            rows on that shard.
        sharded: The names of the tables split across shards.
        broadcast: The other tables the plan reads, each the same on every
            shard. Default: none.
        keys: Split keys, as a mapping from sharded table name to columns:
            rows with equal values on them are always on the same shard.
            Default: none.
        unique: Keys of whole tables, as a mapping from table name to a list
            of column sets. They let windows run on each shard. Default:
            none.
        reproducible: What the result must match, as `sv.equivalent(...)`
            states it, the type `Report.run` and the sinks take. Its
            `floats` decides the doubles: `"exact"` refuses `SUM` and `AVG`
            of doubles; `"plan"` splits them within the proved bound τ;
            `sv.within(...)` splits them and raises where a row's τ exceeds
            the tolerance. Default None: exact.
        max_workers: The number of threads running shards in parallel.
            Default: `ThreadPoolExecutor`'s default.
        tolerance: Return a `Sharded`: the result, with the tolerance τ of
            each split double per row (see the module docstring). Default:
            False.
        float_order: Deprecated: `"any"` is `reproducible=sv.equivalent(floats="plan")`.

    Returns:
        The plan's result, as an Arrow table, or with `tolerance=True` a
        `Sharded` holding it.

    Raises:
        ValueError: The plan's result would depend on how the rows are
            split (`sverify.partition.NotShardable`, a `ValueError`, saying
            why); there are no shards; a shard's tables are not exactly
            `sharded`; rows with equal split keys are on two shards; a
            `unique` column set has two equal rows; `keys` or `unique`
            name unknown columns; or a row's τ exceeds the tolerance
            `reproducible` states.
    """
    from sverify import profiles

    plugin = profiles.find(SHARD_ENGINE)
    run_tables = plugin.run_tables if plugin is not None else None
    if run_tables is None:
        raise ImportError(f"run_sharded runs on {SHARD_ENGINE}: install sverify[{SHARD_ENGINE}]")
    floats = _floats(reproducible, float_order)

    if not shards:
        raise ValueError("run_sharded needs at least one shard")
    for k, shard in enumerate(shards):
        if set(shard) != set(sharded):
            raise ValueError(f"shard {k} has tables {sorted(shard)}, expected {sorted(sharded)}")
    order: FloatOrder = "exact" if floats == "exact" else "any"
    s = split(plan, sharded, keys=keys, unique=unique, float_order=order)
    common = dict(broadcast or {})
    if keys:
        check_keys(shards, keys)
    if unique:
        pieces = {
            t: [shard[t] for shard in shards] if t in sharded else [common[t]] for t in unique
        }
        check_unique(pieces, unique)

    def run(shard: Mapping[str, pa.Table]) -> pa.Table:
        return run_tables(s.partial, {**common, **shard})

    with ThreadPoolExecutor(max_workers=max_workers) as pool:
        parts = list(pool.map(run, shards))
    partials = pa.concat_tables(parts)
    result = run_tables(s.combine, {PARTIALS: partials})
    if not tolerance and not isinstance(floats, Within):
        return result
    out = tolerances(s, partials, result)
    if isinstance(floats, Within):
        _check_within(out, floats)
    return out if tolerance else result


def _floats(reproducible: Observation | None, float_order: FloatOrder | None) -> Any:
    """The doubles `run_sharded` must match: `"exact"`, `"plan"` or a
    `Within`, from `reproducible` or the deprecated `float_order`."""
    if float_order is not None:
        import warnings

        if reproducible is not None:
            raise TypeError("run_sharded takes reproducible= or float_order=, not both")
        warnings.warn(
            "run_sharded(float_order=...) is deprecated; write "
            "reproducible=sv.equivalent(floats='plan') for 'any'",
            DeprecationWarning,
            stacklevel=3,
        )
        return "exact" if float_order == "exact" else "plan"
    return "exact" if reproducible is None else reproducible.floats


def _check_within(sharded: Sharded, w: Within) -> None:
    """Raise where a row's proved bound τ exceeds the tolerance `w`: the
    split's value is then not known to be within `w` of Lean's."""
    for col, taus in sharded.tolerance.items():
        values = sharded.table.column(col).to_pylist()
        for i, (tau, v) in enumerate(zip(taus, values, strict=True)):
            if v is None or tau == 0:
                continue
            # The smallest magnitude Lean's value may have, for `rel` and
            # `ulps` (both scale with it).
            low = max(abs(v) - tau, 0.0) if math.isfinite(v) else math.inf
            allowed = max(
                w.abs or 0.0,
                (w.rel or 0.0) * low,
                (w.ulps or 0) * math.ulp(low) if math.isfinite(low) else 0.0,
            )
            if not tau <= allowed:
                raise ValueError(
                    f"run_sharded: {col!r} in row {i} is within {tau:.3g} of Lean's value, "
                    f"which {w} does not cover; state a looser tolerance, or "
                    "floats='plan' to accept the proved bound"
                )
