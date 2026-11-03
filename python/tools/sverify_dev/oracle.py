"""Oracle A in CI (#242): the lift checked against DuckDB, at a bounded cost.

Maintainer tooling (`sverify_dev`): not in the wheel, and not part of sverify's
API.

Oracle A runs DuckDB's SQL natively and compares it with `Rel.eval` on the
plan the lift (`sverify.sql_lift`) writes for it. Two sources of queries:

* **The benchmarks** (`sverify_dev.lift`): the 54 queries of #229, each
  compared with the stage it reached when `benchmarks.json` was written.
* **The sqllogictest replay** (`sverify_dev.slt`): a fixed sample of the test
  files whose ledger (`characterization/duckdb/<area>.json`) has a query that
  agrees or disagrees, replayed and compared query by query with the ledger.

A query that agreed and no longer does fails the check, and so does a new
disagreement: a query the ledger has refused (or does not have) that is now
lifted and disagrees. Changes for the better are printed and do not fail: the
ledgers are refreshed by the full replay (`python -m sverify_dev.slt`), and
the benchmarks' baseline with `--write`.

It replays every file the ledgers decided a query of (about 1,000 of DuckDB's
4,800; `--files n` takes the `n` whose names hash lowest), with tables
condensed past `slt.MAX_ROWS` rows, so CI's cost stays bounded.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from collections import Counter
from collections.abc import Iterable, Mapping, Sequence
from pathlib import Path

from sverify_dev import slt

#: The benchmark queries' stages (`lift.STAGES`) when last written.
BENCHMARKS = slt.REPO / "characterization" / "oracle-a" / "benchmarks.json"

#: The classes of a replayed query that oracle A decided.
DECIDED = ("agree", "disagree")


def _key(r: Mapping) -> tuple[str, int, str]:
    return r["file"], r["line"], r["sql"]


def skipped_files(out: Path = slt.LEDGER) -> dict[str, str]:
    """The files the ledgers' replay skipped as a whole, with the reason."""
    found: dict[str, str] = {}
    for p in sorted(out.glob("*.json")):
        if p.name == "probes.json" or p.name.startswith("fuzz__"):
            continue
        found.update(json.loads(p.read_text()).get("skipped_files", {}))
    return found


def newly_skipped(skips: Mapping[str, str], before: Mapping[str, str]) -> list[str]:
    """The files skipped as a whole this run (`skips`, with the reason) that
    the ledgers compared (not in `before`): a skip there could hide a
    regression, so the gate fails on it (#407)."""
    return [
        f"{f}: compared -> skipped ({why[:150]})"
        for f, why in sorted(skips.items())
        if f not in before
    ]


def ledger(out: Path = slt.LEDGER) -> dict[tuple[str, int, str], str]:
    """Each replayed query's class, by file, line and SQL, from the ledgers."""
    found: dict[tuple[str, int, str], str] = {}
    for p in sorted(out.glob("*.json")):
        # Not the replay's: the probes (#310) and the fuzzer's findings.
        if p.name == "probes.json" or p.name.startswith("fuzz__"):
            continue
        for r in json.loads(p.read_text()).get("results", []):
            found[_key(r)] = r["cls"]
    return found


def sample(known: Mapping[tuple[str, int, str], str], n: int) -> list[str]:
    """The test files with a decided query, or the `n` whose names hash
    lowest (all for `n` = 0)."""
    files = sorted({f for (f, _, _), cls in known.items() if cls in DECIDED})
    files = sorted(files, key=lambda f: hashlib.sha256(f.encode()).hexdigest())
    return files[:n] if n else files


def compare(
    before: Mapping[str, str], after: Mapping[str, str], what: Iterable[str]
) -> tuple[list[str], list[str]]:
    """Regressions and improvements from `before` to `after` (classes or
    stages by query), over the queries `what`."""
    worse, better = [], []
    for q in what:
        b, a = before.get(q), after.get(q)
        if a == b or a is None:
            continue
        if b == "agree" or a == "disagree" or a == "oracle A":
            worse.append(f"{q}: {b} -> {a}")
        elif a == "agree":
            better.append(f"{q}: {b} -> {a}")
    return worse, better


def check_benchmarks(write: bool) -> tuple[list[str], list[str]]:
    """Oracle A (and C) on the benchmarks against `benchmarks.json`."""
    from sverify_dev import lift

    stages = {q: c.stage for q, c in lift.score().items()}
    agree = sum(s == "agree" for s in stages.values())
    print(f"benchmarks: {agree} of {len(stages)} agree")
    if write:
        BENCHMARKS.parent.mkdir(parents=True, exist_ok=True)
        BENCHMARKS.write_text(json.dumps(stages, indent=1, sort_keys=True) + "\n")
        return [], []
    before = json.loads(BENCHMARKS.read_text()) if BENCHMARKS.exists() else {}
    return compare(before, stages, sorted(stages))


def check_replay(files: int, jobs: int) -> tuple[list[str], list[str]]:
    """The replay of the sampled files against the ledgers."""
    known = ledger()
    chosen = sample(known, files)
    base = slt.fetch() / "test" / "sql"
    now: dict[str, str] = {}
    before: dict[str, str] = {}
    skipped: Counter[str] = Counter()
    skips: dict[str, str] = {}
    for rel, results, skip in slt.replay_files([(str(base / f), f) for f in chosen], jobs):
        if skip:
            # Not compared this run (a crash, a timeout): say so.
            skipped[skip.split(":")[0]] += 1
            skips[rel] = skip
        for r in results:
            q = f"{r['file']}:{r['line']}"
            now[q] = r["cls"]
            before[q] = known.get(_key(r), "new")
    decided = sum(c in DECIDED for c in now.values())
    print(f"replay: {len(chosen)} files, {len(now)} queries, {decided} decided by oracle A")
    if skipped:
        print(f"replay: {sum(skipped.values())} files not compared: {dict(skipped)}")
    worse, better = compare(before, now, sorted(now))
    return worse + newly_skipped(skips, skipped_files()), better


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument(
        "--files", type=int, default=0, help="replay only this many files (default: all decided)"
    )
    parser.add_argument("--jobs", type=int, default=2, help="processes (default 2)")
    parser.add_argument(
        "--write", action="store_true", help="write the benchmarks' baseline and skip the replay"
    )
    args = parser.parse_args(argv)
    worse, better = check_benchmarks(args.write)
    if not args.write:
        w, b = check_replay(args.files, args.jobs)
        worse, better = worse + w, better + b
    for line in better:
        print(f"better: {line}")
    for line in worse:
        print(f"WORSE: {line}")
    if worse:
        print(
            f"{len(worse)} queries regressed or newly disagree: a wrong lift or profile, "
            "or a ledger to refresh (python -m sverify_dev.slt <area>)"
        )
        sys.exit(1)
    print("oracle A: no regressions")


if __name__ == "__main__":
    main()
