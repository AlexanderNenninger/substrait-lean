"""Sharded evaluation: run a plan on each shard of its data, then combine.

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release.

    import sverify.partition as sp

    s = sp.split(plan_json, sharded=["orders"])      # or NotShardable, saying why
    result = sp.run_sharded(plan_json, shards, sharded=["orders"], broadcast={"customers": c})

A shard holds some of the rows of each sharded table (a Delta or Iceberg
partition, a file, a worker's slice); every other table is broadcast, a copy
on each shard. `substrait-check --shard` splits the plan into the plan each
shard runs and the plan that combines their results, and Lean proves the
combined result is the plan's result on all the data (`Rel.shardSplit_sound`
in `SubstraitLean/Partition.lean`):

* A **linear** plan (filters, projections, sorts, unions, and joins whose
  other side is broadcast) runs on every shard; the results are concatenated.
* An **aggregate** of `COUNT`, integer `SUM`, `MIN` and `MAX` (`MIN` and
  `MAX` also `DISTINCT`), under such a plan, runs in **two phases**: each
  shard aggregates by the grouping keys, then the partial rows are grouped
  again and combined (`COUNT` by `SUM`). Filters, projections and sorts above
  the aggregate run after combining.

**Split keys** (`keys={"orders": ["region"]}`) say that rows with equal values
on those columns are always on the same shard, as a Delta or Iceberg
partition column guarantees. `run_sharded` checks it on the data. With them:

* an aggregate whose `GROUP BY` contains the key, and a `DISTINCT` whose
  columns do, run on each shard and are concatenated, whatever their
  measures (except `SUM`/`AVG` of doubles, which add in row order);
* `COUNT(DISTINCT k)` and `SUM(DISTINCT k)` of the key itself run in two
  phases;
* a join of two sharded tables whose condition equates their keys
  (co-partitioned: `ON r.k = s.k`, inner, left, semi or anti) runs on each
  shard;
* a window whose `PARTITION BY` contains the key runs on each shard, when
  `unique=` columns show that its `PARTITION BY` and `ORDER BY` columns have
  no ties (Lean breaks ties by row order, which sharding does not keep).
  `run_sharded` checks `unique` on the data too.

Refused, with the reason: `SUM`/`AVG` of doubles (floating-point addition is
not associative, so the rounding would depend on the split), other
`DISTINCT` aggregates, `DISTINCT` without the key, other windows, `FETCH`,
and joins of sharded tables that are not co-partitioned. `float_order="any"` splits `SUM`/`AVG` of
doubles anyway: the result is then `Split.proved = False`, the sums of
doubles round as the split makes them, and the rest of the plan is still
what Lean computes.

Partial integer sums are checked to fit in 64 bits like any `SUM`, so a
partial sum can fail where the total would not (a shard of large positive
values next to one of large negative values); the result is then an error,
never a wrong answer. With values of one sign that cannot happen
(`inI64_partial`).

Shards run on Polars (`sverify.polars_engine`), in parallel threads.
"""

from __future__ import annotations

import json
import struct
from collections.abc import Mapping, Sequence
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from typing import Any, Literal

import pyarrow as pa

from sverify.engine import run_checker

#: The table the combining plan reads the shards' results from.
PARTIALS = "__partials"

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
    as the split makes them."""
    partial: dict
    """The plan each shard runs (Lean's written form)."""
    combine: dict
    """The plan that combines the shards' results, read from `PARTIALS`."""


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
            doubles; `"any"` splits them anyway, and the result has
            `proved=False`.

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
        raise ValueError(f"substrait-check --shard failed: {err.strip()}")
    j = json.loads(out)
    return Split(j["mode"], j["proved"], j["partial"], j["combine"])


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


def run_sharded(
    plan: str | dict,
    shards: Sequence[Mapping[str, pa.Table]],
    *,
    sharded: Sequence[str],
    broadcast: Mapping[str, pa.Table] | None = None,
    keys: Mapping[str, Sequence[str]] | None = None,
    unique: Mapping[str, Sequence[Sequence[str]]] | None = None,
    float_order: FloatOrder = "exact",
    max_workers: int | None = None,
) -> pa.Table:
    """The plan's result on all the data, computed shard by shard on Polars.
    This is `sverify.engines.run_sharded`.

    Each shard maps every table of `sharded` to its rows on that shard;
    `broadcast` holds the other tables. The result equals the plan's on the
    concatenated shards, as a bag (row order is not kept), unless
    `float_order="any"` was needed: sums of doubles then round as the split
    makes them.

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
        float_order: `"exact"` (the default) refuses `SUM` and `AVG` of
            doubles; `"any"` splits them anyway, and the result is not
            proved equal.
        max_workers: The number of threads running shards in parallel.
            Default: `ThreadPoolExecutor`'s default.

    Returns:
        The plan's result, as an Arrow table.

    Raises:
        ValueError: The plan's result would depend on how the rows are
            split (`sverify.partition.NotShardable`, a `ValueError`, saying
            why); there are no shards; a shard's tables are not exactly
            `sharded`; rows with equal split keys are on two shards; a
            `unique` column set has two equal rows; or `keys` or `unique`
            name unknown columns.
    """
    from sverify import polars_engine

    if not shards:
        raise ValueError("run_sharded needs at least one shard")
    for k, shard in enumerate(shards):
        if set(shard) != set(sharded):
            raise ValueError(f"shard {k} has tables {sorted(shard)}, expected {sorted(sharded)}")
    s = split(plan, sharded, keys=keys, unique=unique, float_order=float_order)
    common = dict(broadcast or {})
    if keys:
        check_keys(shards, keys)
    if unique:
        pieces = {
            t: [shard[t] for shard in shards] if t in sharded else [common[t]] for t in unique
        }
        check_unique(pieces, unique)

    def run(shard: Mapping[str, pa.Table]) -> pa.Table:
        return polars_engine.run(s.partial, {**common, **shard})

    with ThreadPoolExecutor(max_workers=max_workers) as pool:
        parts = list(pool.map(run, shards))
    return polars_engine.run(s.combine, {PARTIALS: pa.concat_tables(parts)})
