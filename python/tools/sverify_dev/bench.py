"""How long a check takes, cold and warm, by stage (#745, #825).

Maintainer tooling (`sverify_dev`): not in the wheel, and not part of sverify's
API.

    python -m sverify_dev.bench [--notebooks] [--json FILE] [--budgets]

For every catalogue query with a contract (`catalogue/queries/*.toml`) it
times `sverify.verify` twice: cold, with the checker's process stopped, this
process's memo cleared and an empty proof cache (`sverify._proof_cache`),
as a new `sverify check` meets a transform; and warm, the same with the
cache the cold pass filled, as the next `check` of an unchanged transform
does. It times `sverify check` end to end on a small pipeline the same two
ways, and with `--notebooks` it runs each tour notebook twice in a process
of its own. Each time is split by stage (`sverify._stages`): `lift`,
`checker`, `counterexamples`, `plan` and `other`, the rest.

The report is Markdown, written to stdout and, in GitHub Actions, to the
job's summary. `--budgets` fails (exit 1) past `BUDGETS`.
"""

from __future__ import annotations

import argparse
import json
import os
import statistics
import subprocess
import sys
import tempfile
import textwrap
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[3]
STAGES = ("lift", "checker", "counterexamples", "plan", "other")

#: Budgets in seconds (#745, #825): the median catalogue transform cold, the
#: slowest cold, every transform warm, and `sverify check` warm end to end.
#: They are for CI's `ubuntu-latest` runner, about twice as slow as a recent
#: laptop. On the runner, with #825, the first three were 0.09 s, a few
#: seconds and 0.15 s, and `sverify check` warm 1.05 s, most of it Python's
#: imports.
BUDGETS = {
    "typical_cold": 2.0,
    "slowest_cold": 30.0,
    "slowest_warm": 1.0,
    "cli_warm": 3.0,
}
#: Runs of `sverify check` per measurement; the fastest counts, so that a
#: noisy runner does not fail the budget.
CLI_RUNS = 3


@dataclass
class Run:
    """One timed run: its total and each stage's share."""

    seconds: float
    stages: dict[str, float] = field(default_factory=dict)
    hits: dict[str, int] = field(default_factory=dict)
    error: str | None = None

    @property
    def slowest_stage(self) -> str:
        return max(self.stages, key=lambda s: self.stages[s]) if self.stages else "-"

    def to_json(self) -> dict[str, Any]:
        out: dict[str, Any] = {
            "seconds": round(self.seconds, 4),
            "stages": {k: round(v, 4) for k, v in self.stages.items()},
            "hits": self.hits,
        }
        if self.error is not None:
            out["error"] = self.error
        return out


def _new_process() -> None:
    """Forget what this process knows, as a new process would."""
    from sverify import engine

    engine._CHECKER.close()
    engine._run_checker.cache_clear()


def _timed(fn: Any) -> Run:
    from sverify import _stages

    with _stages.timing() as t:
        start = time.perf_counter()
        error = None
        try:
            fn()
        except Exception as e:  # noqa: BLE001 - the report shows it
            error = f"{type(e).__name__}: {str(e).splitlines()[0] if str(e) else ''}"
        total = time.perf_counter() - start
    stages = {s: t.seconds.get(s, 0.0) for s in STAGES if s != "other"}
    stages["other"] = max(0.0, total - sum(stages.values()))
    return Run(total, stages, dict(t.hits), error)


def catalogue_cases() -> list[tuple[str, Any]]:
    """Each catalogue query with a contract, as a function that verifies it."""
    sys.path.insert(0, str(ROOT / "python" / "tools"))
    import sverify
    from sverify_dev import catalogue as C

    schemas = C.load_schemas()
    cases = []
    for q in C.load_queries():
        if q.requires is None or q.ensures is None or q.not_expressible is not None:
            continue

        def run(q: Any = q) -> None:
            query = C.build(q, schemas, "native")
            requires, ensures = C.contract(q, schemas, "native")
            tables = C.tables(schemas, q.dataset, "native") if isinstance(query, str) else None
            sverify.verify(query, requires=requires, ensures=ensures, tables=tables)

        cases.append((q.id, run))
    return cases


def bench_catalogue() -> dict[str, dict[str, Run]]:
    """Each case cold, then each warm."""
    cases = catalogue_cases()
    cold: dict[str, Run] = {}
    for name, run in cases:
        _new_process()
        cold[name] = _timed(run)
    warm: dict[str, Run] = {}
    for name, run in cases:
        _new_process()
        warm[name] = _timed(run)
    return {name: {"cold": cold[name], "warm": warm[name]} for name, _ in cases}


PIPELINE = """
import pyarrow as pa
import sverify as sv
from ibis import _
from sverify.io import StaticSource

orders = StaticSource(
    pa.table({"id": [1, 2, 3], "customer": ["a", "b", "a"], "amount": [30, 5, 50]}),
    name="orders",
)


@sv.transform(
    requires={"orders": [_.amount >= 0, _.amount < 1000, sv.unique("id")]},
    ensures=[_.amount > 10, sv.unique("id")],
)
def paid(orders):
    return orders.filter(orders.amount > 10)


p = orders.pipe(paid)
"""


def _process(argv: list[str], env: dict[str, str], cwd: Path | None = None) -> Run:
    start = time.perf_counter()
    out = subprocess.run(argv, env=env, cwd=cwd, capture_output=True, text=True)
    total = time.perf_counter() - start
    error = None if out.returncode == 0 else (out.stderr or out.stdout).strip()[-300:]
    return Run(total, error=error)


def bench_cli(cache: Path) -> dict[str, Run]:
    """`sverify check` on `PIPELINE`, cold (an empty cache) and warm, end to
    end: the fastest of `CLI_RUNS` runs each."""
    with tempfile.TemporaryDirectory() as d:
        path = Path(d) / "pipeline.py"
        path.write_text(textwrap.dedent(PIPELINE))
        env = {**os.environ}
        env.pop("PYTHONDONTWRITEBYTECODE", None)
        argv = [sys.executable, "-m", "sverify.cli", "check", str(path)]
        # Once for Python's bytecode caches, which a user's second run has.
        _process(argv, {**env, "SVERIFY_CACHE": "off"})
        cold, warm = [], []
        for i in range(CLI_RUNS):
            run_env = {**env, "SVERIFY_CACHE_DIR": str(cache / f"cli-{i}")}
            cold.append(_process(argv, run_env))
            warm.append(_process(argv, run_env))
        return {"cold": min(cold, key=_seconds), "warm": min(warm, key=_seconds)}


def _seconds(run: Run) -> float:
    return run.seconds if run.error is None else float("inf")


NOTEBOOK_RUNNER = """
import json, runpy, sys, time
from sverify import _stages
with _stages.timing() as t:
    start = time.perf_counter()
    runpy.run_path(sys.argv[1], run_name="__main__")
    total = time.perf_counter() - start
with open(sys.argv[2], "w") as f:
    json.dump({"total": total, **t.to_json()}, f)
"""


def bench_notebooks(cache: Path) -> dict[str, dict[str, Run]]:
    """Each tour notebook run headless, cold and then warm."""
    out: dict[str, dict[str, Run]] = {}
    env = {**os.environ, "SVERIFY_CACHE_DIR": str(cache / "notebooks")}
    env.pop("PYTHONDONTWRITEBYTECODE", None)
    for nb in sorted((ROOT / "notebooks").glob("[0-9]*.py")):
        runs = {}
        for kind in ("cold", "warm"):
            with tempfile.NamedTemporaryFile(suffix=".json") as f:
                argv = [sys.executable, "-c", NOTEBOOK_RUNNER, str(nb), f.name]
                run = _process(argv, env, cwd=nb.parent)
                if run.error is None:
                    data = json.loads(Path(f.name).read_text())
                    stages = {s: data["seconds"].get(s, 0.0) for s in STAGES if s != "other"}
                    stages["other"] = max(0.0, data["total"] - sum(stages.values()))
                    run = Run(run.seconds, stages, data["hits"])
                runs[kind] = run
        out[nb.stem] = runs
    return out


def _fmt(x: float) -> str:
    return f"{x:.2f}"


def _row(name: str, runs: dict[str, Run]) -> str:
    cold, warm = runs["cold"], runs["warm"]
    stages = " | ".join(_fmt(cold.stages.get(s, 0.0)) for s in STAGES)
    note = f" ({cold.error})" if cold.error else ""
    return (
        f"| {name}{note} | {_fmt(cold.seconds)} | {_fmt(warm.seconds)} | {stages} | "
        f"{cold.slowest_stage} |"
    )


def summary(results: dict[str, Any]) -> dict[str, float]:
    """The numbers `BUDGETS` bounds."""
    cat = results["catalogue"]
    cold = [r["cold"].seconds for r in cat.values()]
    warm = [r["warm"].seconds for r in cat.values()]
    out = {
        "typical_cold": statistics.median(cold),
        "slowest_cold": max(cold),
        "slowest_warm": max(warm),
    }
    if "cli" in results:
        out["cli_warm"] = results["cli"]["warm"].seconds
    return out


def report(results: dict[str, Any], top: int = 15) -> str:
    head = (
        "| | cold (s) | warm (s) | "
        + " | ".join(STAGES)
        + " (cold, s) | slowest stage |\n|---|---|---|"
        + "---|" * len(STAGES)
        + "---|"
    )
    lines = ["## Check times (#745, #825)", ""]
    nums = summary(results)
    lines.append("| | seconds | budget |")
    lines.append("|---|---|---|")
    for k, v in nums.items():
        lines.append(f"| {k.replace('_', ' ')} | {_fmt(v)} | {_fmt(BUDGETS[k])} |")
    cat = results["catalogue"]
    slow = sorted(cat.items(), key=lambda kv: -kv[1]["cold"].seconds)
    lines += ["", f"### Catalogue: the {min(top, len(slow))} slowest of {len(slow)}", "", head]
    lines += [_row(name, runs) for name, runs in slow[:top]]
    total = {k: sum(r[k].seconds for r in cat.values()) for k in ("cold", "warm")}
    lines.append(f"| all {len(cat)} | {_fmt(total['cold'])} | {_fmt(total['warm'])} |")
    if "cli" in results:
        lines += ["", "### `sverify check`, end to end", "", "| | cold (s) | warm (s) |"]
        lines += ["|---|---|---|"]
        c = results["cli"]
        lines.append(f"| one transform | {_fmt(c['cold'].seconds)} | {_fmt(c['warm'].seconds)} |")
    if "notebooks" in results:
        lines += ["", "### Tour notebooks, run whole", "", head]
        lines += [_row(name, runs) for name, runs in results["notebooks"].items()]
    return "\n".join(lines) + "\n"


def over_budget(results: dict[str, Any]) -> list[str]:
    return [
        f"{k.replace('_', ' ')}: {v:.2f} s over its budget of {BUDGETS[k]:.2f} s"
        for k, v in summary(results).items()
        if v > BUDGETS[k]
    ]


def to_json(results: dict[str, Any]) -> dict[str, Any]:
    def runs(d: dict[str, Run]) -> dict[str, Any]:
        return {k: v.to_json() for k, v in d.items()}

    out: dict[str, Any] = {"summary": summary(results), "budgets": BUDGETS}
    out["catalogue"] = {k: runs(v) for k, v in results["catalogue"].items()}
    if "cli" in results:
        out["cli"] = runs(results["cli"])
    if "notebooks" in results:
        out["notebooks"] = {k: runs(v) for k, v in results["notebooks"].items()}
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--notebooks", action="store_true", help="also run the tour notebooks")
    parser.add_argument("--no-cli", action="store_true", help="skip `sverify check` end to end")
    parser.add_argument("--json", type=Path, help="write the times as JSON to this file")
    parser.add_argument("--budgets", action="store_true", help="exit 1 past the budgets")
    args = parser.parse_args(argv)
    with tempfile.TemporaryDirectory(prefix="sverify-bench-") as d:
        cache = Path(d)
        os.environ["SVERIFY_CACHE_DIR"] = str(cache / "catalogue")
        os.environ.pop("SVERIFY_CACHE", None)
        results: dict[str, Any] = {"catalogue": bench_catalogue()}
        if not args.no_cli:
            results["cli"] = bench_cli(cache)
        if args.notebooks:
            results["notebooks"] = bench_notebooks(cache)
    text = report(results)
    print(text)
    if summary_file := os.environ.get("GITHUB_STEP_SUMMARY"):
        with open(summary_file, "a") as f:
            f.write(text)
    if args.json is not None:
        args.json.write_text(json.dumps(to_json(results), indent=2) + "\n")
    if args.budgets and (over := over_budget(results)):
        for line in over:
            print(f"::error::{line}" if os.environ.get("GITHUB_ACTIONS") else line)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
