"""Measure sverify-dbt on public dbt projects (#1487): how many models it
reads, how many declared tests it proves, and what `sverify_proved` saves.

Maintainers' tooling like `sverify_dbt.replay` (not in the wheel). Each
project is fetched at a pinned commit into a temporary directory (never
vendored), given a DuckDB profile, built with dbt, checked with sverify-dbt,
and written up as one JSON record:

    uv run python scripts/measure.py jaffle_shop            # prints the record
    uv run python scripts/measure.py --list

The numbers are in `docs/dbt-measurements.md`. Run a large project on homelab
(`homelab-run --detach`), not on the laptop.
"""

from __future__ import annotations

import argparse
import collections
import json
import sys
import tempfile
import time
from pathlib import Path
from typing import Any

from sverify_dbt import check
from sverify_dbt.manifest import load
from sverify_dbt.replay import Source, _dbt, _statuses, extract, normalize

#: The projects: the repository, a pinned commit, the dbt project's directory
#: in it, and the `dbt build` arguments that load its data on DuckDB; None for
#: a project with no data to load, which is compiled only. (jaffle_shop is
#: the classic project: its successor, dbt-labs/jaffle-shop, needs dbt 2.)
PROJECTS: dict[str, tuple[Source, list[str] | None]] = {
    "jaffle_shop": (
        Source(
            "jaffle_shop",
            "https://github.com/dbt-labs/jaffle_shop",
            "",
            "fd7bfacae4f497ff044a6a0275268676bf1b64c3",
            ".",
            "Apache-2.0",
        ),
        [],  # its seeds are the data: `dbt build` loads them
    ),
    # BigQuery; GitLab's dbt project went private, and Mattermost's is gone.
    "calitp": (
        Source(
            "calitp",
            "https://github.com/Cal-ITP/data-infra",
            "",
            "546e3548a1b594b7f52728ce46311f2d45a0dc82",
            "warehouse",
            "AGPL-3.0",
        ),
        None,
    ),
}
TOP = 10


def _run_results(project: Path) -> dict[str, float]:
    """Seconds dbt spent on each node of its last run."""
    path = project / "target" / "run_results.json"
    if not path.exists():
        return {}
    data = json.loads(path.read_text(encoding="utf-8"))["results"]
    return {r["unique_id"]: float(r["execution_time"]) for r in data}


def measure(name: str) -> dict[str, Any]:
    source, build_args = PROJECTS[name]
    with tempfile.TemporaryDirectory() as tmp:
        project = extract(source, Path(tmp) / name)
        _dbt(project, "deps")
        started = time.monotonic()
        if build_args is None:
            _dbt(project, "compile")
        else:
            _dbt(project, "build", *build_args)
        build_seconds = time.monotonic() - started
        times = _run_results(project)
        statuses = _statuses(project / "target" / "run_results.json")
        if build_args is not None:
            _dbt(project, "docs", "generate", "--no-compile")
        proj = load(project)
        result = check(proj, counterexamples=0)

    models = result.models
    refused = collections.Counter(normalize(m.refused) for m in models if m.refused)
    skippable = {t.name for t in result.skippable if t.name}
    test_ids = list(proj.tests)
    declared = len(test_ids)
    by_name = {t.name: uid for uid, t in proj.tests.items()}
    skipped_uids = [by_name[n] for n in skippable if n in by_name]
    test_seconds = sum(times.get(uid, 0.0) for uid in test_ids)
    skipped_seconds = sum(times.get(uid, 0.0) for uid in skipped_uids)
    return {
        "project": name,
        "repo": source.repo,
        "commit": source.commit,
        "dbt": result.dbt_version,
        "models": {
            "total": len(models),
            "read": sum(1 for m in models if not m.refused),
            "refused": sum(1 for m in models if m.refused),
            "top_refusals": refused.most_common(TOP),
        },
        "tests": {
            "declared": declared,
            "proved": len(result.proved_tests),
            "skippable": len(skippable),
            "not_proved": sum(1 for m in models for t in m.tests if t.status == "not proved"),
            "not_checked": sum(1 for m in models for t in m.tests if t.status == "not checked"),
            "dbt_failed": sum(1 for s in statuses.values() if s in ("fail", "error")),
        },
        "savings": {
            "test_queries_skipped": len(skipped_uids),
            "of_test_queries": declared,
            "test_seconds_skipped": round(skipped_seconds, 2),
            "test_seconds_total": round(test_seconds, 2),
            "build_seconds": round(build_seconds, 1),
            "warehouse": "DuckDB, in process",
        },
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("project", nargs="?", choices=sorted(PROJECTS))
    parser.add_argument("--list", action="store_true")
    args = parser.parse_args(argv)
    if args.list or not args.project:
        for name, (src, _) in PROJECTS.items():
            print(f"{name}  {src.repo}@{src.commit[:12]}")
        return 0
    print(json.dumps(measure(args.project), indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
