"""Balance CI's shards by recorded durations (docs/build-performance.md).

Maintainer tooling (`sverify_dev`): not in the wheel.

CI splits the `core` tests three ways (`SVERIFY_SHARD`, `tests/_suite.py`)
and oracle A's replay four ways (`--shard`, `sverify_dev.oracle`). Without a
table, the tests go by a hash of their node id and the files round-robin,
which leaves shards unequal. This reads the durations a run records,
`$SVERIFY_TEST_TIMINGS` (one line per test phase) and `$SVERIFY_SLT_TIMINGS`
(one line per replayed file, and the benchmarks shard 1 runs), and writes
each item's shard: longest first, to the shard with the least so far. A test
or file the table doesn't list keeps the old rule, so the table only needs
refreshing when the shards drift apart.

    uv run python -m sverify_dev.shard_durations --tests t1.jsonl t2.jsonl t3.jsonl
    uv run python -m sverify_dev.shard_durations --slt s1.jsonl s2.jsonl s3.jsonl s4.jsonl
"""

from __future__ import annotations

import argparse
import json
from collections import defaultdict
from collections.abc import Iterable
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
TESTS = ROOT / "python" / "tests" / "shards.json"
ORACLE = ROOT / "python" / "tools" / "sverify_dev" / "oracle_shards.json"


def read(paths: Iterable[Path], key: str) -> dict[str, float]:
    """Each item's total recorded seconds (a test's phases summed)."""
    total: dict[str, float] = defaultdict(float)
    for path in paths:
        for line in path.read_text().splitlines():
            if line.strip():
                r = json.loads(line)
                total[r[key]] += r["s"]
    return dict(total)


def balance(durations: dict[str, float], n: int, fixed: dict[int, float] | None = None) -> dict:
    """Longest first, each to the least loaded shard (1-based), from the
    loads `fixed` gives some shards already."""
    loads = [0.0] * n
    for i, s in (fixed or {}).items():
        loads[i - 1] += s
    shard: dict[str, int] = {}
    for name, s in sorted(durations.items(), key=lambda kv: (-kv[1], kv[0])):
        i = min(range(n), key=lambda k: (loads[k], k))
        loads[i] += s
        shard[name] = i + 1
    return {"n": n, "loads": [round(x, 1) for x in loads], "shard": dict(sorted(shard.items()))}


def write(path: Path, table: dict) -> None:
    path.write_text(json.dumps(table, indent=0, sort_keys=True) + "\n")
    print(
        f"{path.relative_to(ROOT)}: {len(table['shard'])} items, estimated loads {table['loads']} s"
    )


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument("--tests", type=Path, nargs="*", default=[], help="$SVERIFY_TEST_TIMINGS files")
    ap.add_argument("--min-s", type=float, default=0.05, help="the shortest test the table lists")
    ap.add_argument("--slt", type=Path, nargs="*", default=[], help="$SVERIFY_SLT_TIMINGS files")
    a = ap.parse_args(argv)
    if a.tests:
        # Tests under `--min-s` stay with the hash: they add about the same to
        # every shard, and the table stays small.
        tests = read(a.tests, "test")
        write(TESTS, balance({t: s for t, s in tests.items() if s >= a.min_s}, 3))
    if a.slt:
        from sverify_dev.oracle import BENCHMARKS_TIMING

        files = read(a.slt, "file")
        bench = files.pop(BENCHMARKS_TIMING, 0.0)
        write(ORACLE, balance(files, 4, {1: bench}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
