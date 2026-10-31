"""Sharded evaluation: run a plan on each shard of its data, then combine.

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
* An **aggregate** of `COUNT`, integer `SUM`, `MIN` and `MAX`, under such a
  plan, runs in **two phases**: each shard aggregates by the grouping keys,
  then the partial rows are grouped again and combined (`COUNT` by `SUM`).
  Filters, projections and sorts above the aggregate run after combining.

Refused, with the reason: `SUM`/`AVG` of doubles (floating-point addition is
not associative, so the rounding would depend on the split), `DISTINCT`
aggregates, `DISTINCT`, windows, `FETCH`, and joins of two sharded tables.

Partial integer sums are checked to fit in 64 bits like any `SUM`, so a
partial sum can fail where the total would not (a shard of large positive
values next to one of large negative values); the result is then an error,
never a wrong answer. With values of one sign that cannot happen
(`inI64_partial`).

Shards run on Polars (`sverify.polars_engine`), in parallel threads.
"""

from __future__ import annotations

import json
from collections.abc import Mapping, Sequence
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from typing import Literal

import pyarrow as pa

from sverify.engine import run_checker

#: The table the combining plan reads the shards' results from.
PARTIALS = "__partials"


class NotShardable(ValueError):
    """The plan's result would depend on how the rows are split."""


@dataclass(frozen=True)
class Split:
    mode: Literal["linear", "two_phase"]
    partial: dict
    """The plan each shard runs (Lean's written form)."""
    combine: dict
    """The plan that combines the shards' results, read from `PARTIALS`."""


def split(plan: str | dict, sharded: Sequence[str]) -> Split:
    """Split a Substrait plan for evaluation on shards of the tables `sharded`."""
    p = json.loads(plan) if isinstance(plan, str) else plan
    code, out, err = run_checker(("--shard",), json.dumps({"plan": p, "sharded": list(sharded)}))
    if code == 5:
        raise NotShardable(err.strip())
    if code != 0:
        raise ValueError(f"substrait-check --shard failed: {err.strip()}")
    j = json.loads(out)
    return Split(j["mode"], j["partial"], j["combine"])


def run_sharded(
    plan: str | dict,
    shards: Sequence[Mapping[str, pa.Table]],
    *,
    sharded: Sequence[str],
    broadcast: Mapping[str, pa.Table] | None = None,
    max_workers: int | None = None,
) -> pa.Table:
    """The plan's result on all the data, computed shard by shard on Polars.

    Each shard maps every table of `sharded` to its rows on that shard;
    `broadcast` holds the other tables. The result equals the plan's on the
    concatenated shards, as a bag (row order is not kept)."""
    from sverify import polars_engine

    if not shards:
        raise ValueError("run_sharded needs at least one shard")
    for k, shard in enumerate(shards):
        if set(shard) != set(sharded):
            raise ValueError(f"shard {k} has tables {sorted(shard)}, expected {sorted(sharded)}")
    s = split(plan, sharded)
    common = dict(broadcast or {})

    def run(shard: Mapping[str, pa.Table]) -> pa.Table:
        return polars_engine.run(s.partial, {**common, **shard})

    with ThreadPoolExecutor(max_workers=max_workers) as pool:
        parts = list(pool.map(run, shards))
    return polars_engine.run(s.combine, {PARTIALS: pa.concat_tables(parts)})
