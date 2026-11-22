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
import re
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Any

import yaml

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
TOP = 40


def _run_results(project: Path) -> dict[str, float]:
    """Seconds dbt spent on each node of its last run."""
    path = project / "target" / "run_results.json"
    if not path.exists():
        return {}
    data = json.loads(path.read_text(encoding="utf-8"))["results"]
    return {r["unique_id"]: float(r["execution_time"]) for r in data}


#: `dbt_utils.get_column_values` asks the warehouse for the values of a column
#: at compile time, and the warehouse here has no data: the stub answers with
#: one placeholder value, so the models that pivot on it still compile.
_STUB = """{% macro duckdb__get_column_values(table, column, order_by='count(*) desc',
    max_records=none, default=none, where=none) %}
  {{ return(['placeholder']) }}
{% endmacro %}
"""


def _stub_column_values(project: Path) -> None:
    (project / "macros").mkdir(exist_ok=True)
    (project / "macros" / "sverify_measure_stub.sql").write_text(_STUB, encoding="utf-8")
    path = project / "dbt_project.yml"
    config = yaml.safe_load(path.read_text(encoding="utf-8"))
    name = config["name"]
    config["dispatch"] = [
        *config.get("dispatch", []),
        {"macro_namespace": "dbt_utils", "search_order": [name, "dbt_utils"]},
    ]
    path.write_text(yaml.safe_dump(config), encoding="utf-8")


def _compile(project: Path, limit: int = 150) -> list[str]:
    """`dbt compile`, leaving out each model whose compilation asks the
    warehouse for data it does not have here (`dbt_utils.get_column_values`
    on a table nothing built), until the rest compile. The models left out,
    each with its descendants: an ephemeral model compiles inside the models
    that read it."""
    left_out: list[str] = []
    for _ in range(limit):
        args = ["compile", "--exclude", *(f"{n}+" for n in left_out)] if left_out else ["compile"]
        done = subprocess.run(
            [str(Path(sys.executable).with_name("dbt")), *args, "--profiles-dir", str(project)],
            cwd=project,
            check=False,
            capture_output=True,
            text=True,
        )
        if done.returncode == 0:
            break
        text = done.stdout + done.stderr
        found = re.search(r"(?:Compilation|Database|Parsing|Runtime) Error in model (\w+)", text)
        if not found or found[1] in left_out:
            print(
                "dbt compile stopped:",
                *text.strip().splitlines()[-12:],
                sep="\n  ",
                file=sys.stderr,
            )
            break
        left_out.append(found[1])
    return left_out


_CASCADE = re.compile(r"^ref\(.*?\) could not be read \(")
CLASSES = (
    "read",
    "needs the warehouse's column types",
    "doesn't compile under dbt-duckdb",
    "dialect (the SQL is not DuckDB's)",
    "other refusal",
)


def _word(status: str) -> str:
    """A test status as one word, `not_proved`: sverify-dbt spells it with a
    space before its 0.x renames and with an underscore after."""
    return status.replace(" ", "_")


def classify(refusal: str | None) -> str:
    """The class of a model's refusal, by its root cause: a model that reads
    a refused model is refused for that model's reason."""
    if refusal is None:
        return CLASSES[0]
    root = refusal
    while _CASCADE.match(root):
        root = _CASCADE.sub("", root, count=1)
    if "no column types" in root:
        return CLASSES[1]
    if "no compiled SQL" in root:
        return CLASSES[2]
    if "does not parse" in root or "unknown function" in root or "DuckDB SQL here has no" in root:
        return CLASSES[3]
    return CLASSES[4]


def apply_types(project: Path, types: Path, origins: set[str]) -> int:
    """Give the project's sources the column types in `types` (a sources YAML
    whose columns say where each type comes from: `catalog`, `declared` or
    `inferred`), for the columns whose origin is in `origins`. The number of
    columns typed."""
    wanted: dict[tuple[str, str], list[dict[str, Any]]] = {}
    for src in yaml.safe_load(types.read_text(encoding="utf-8")).get("sources", []):
        for table in src.get("tables", []):
            cols = [c for c in table.get("columns", []) if c.get("origin") in origins]
            wanted[(src["name"], table["name"])] = cols
    typed = 0
    for path in sorted(project.rglob("*.y*ml")):
        if "dbt_packages" in path.parts or "target" in path.parts:
            continue
        try:
            data = yaml.safe_load(path.read_text(encoding="utf-8"))
        except yaml.YAMLError:
            continue
        if not isinstance(data, dict) or not isinstance(data.get("sources"), list):
            continue
        changed = False
        for src in data["sources"]:
            for table in src.get("tables") or []:
                cols = wanted.get((src.get("name"), table.get("name")))
                if not cols:
                    continue
                have = {c["name"]: c for c in table.get("columns") or []}
                for c in cols:
                    have.setdefault(c["name"], {"name": c["name"]})["data_type"] = c["data_type"]
                    typed += 1
                table["columns"] = list(have.values())
                changed = True
        if changed:
            path.write_text(yaml.safe_dump(data, sort_keys=False), encoding="utf-8")
    return typed


def measure(
    name: str, types: Path | None = None, origins: frozenset[str] = frozenset()
) -> dict[str, Any]:
    source, build_args = PROJECTS[name]
    with tempfile.TemporaryDirectory() as tmp:
        project = extract(source, Path(tmp) / name)
        _dbt(project, "deps")
        typed = apply_types(project, types, set(origins)) if types else 0
        started = time.monotonic()
        left_out: list[str] = []
        if build_args is None:
            _stub_column_values(project)
            left_out = _compile(project)
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
    classes = {m.unique_id: classify(m.refused) for m in models}
    model_classes = collections.Counter(classes.values())
    test_classes: collections.Counter[str] = collections.Counter()
    for m in models:
        for t in m.tests:
            test_classes[classes[m.unique_id] if m.refused else f"read, {_word(t.status)}"] += 1
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
        "source_columns_typed": {"origins": sorted(origins), "columns": typed},
        "models": {
            "total": len(models),
            "read": sum(1 for m in models if not m.refused),
            "refused": sum(1 for m in models if m.refused),
            "left_out_of_compile": len(left_out),
            "by_class": {c: model_classes.get(c, 0) for c in CLASSES},
            "top_refusals": refused.most_common(TOP),
        },
        "tests": {
            "declared": declared,
            "by_class": dict(sorted(test_classes.items())),
            "on_sources_or_seeds": declared - sum(test_classes.values()),
            "proved": len(result.proved_tests),
            "skippable": len(skippable),
            "not_proved": sum(
                1 for m in models for t in m.tests if _word(t.status) == "not_proved"
            ),
            "not_checked": sum(
                1 for m in models for t in m.tests if _word(t.status) == "not_checked"
            ),
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
    parser.add_argument("--types", type=Path, help="a sources YAML with column types to apply")
    parser.add_argument(
        "--origins",
        nargs="+",
        default=["catalog", "declared", "inferred"],
        help="which origins of the types file to apply",
    )
    args = parser.parse_args(argv)
    if args.list or not args.project:
        for name, (src, _) in PROJECTS.items():
            print(f"{name}  {src.repo}@{src.commit[:12]}")
        return 0
    print(json.dumps(measure(args.project, args.types, frozenset(args.origins)), indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
