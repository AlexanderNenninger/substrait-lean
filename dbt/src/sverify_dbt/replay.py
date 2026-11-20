"""Replay dbt test projects others wrote through sverify-dbt (#859).

Maintainers' tooling, not part of sverify-dbt's API: `python -m
sverify_dbt.replay`.

dbt packages ship integration projects: seeds, models that call each macro
and the tests that check them, run by the package's own CI on each adapter.
For each source (`SOURCES`, at a pinned release tag) this module copies the
project, points it at a DuckDB file, runs `dbt deps`, `dbt build` and `dbt
docs generate --no-compile` (for the column types), then `sverify_dbt.check`,
and records every test of the project:

* `proved`, `not proved` or `not checked`: what `check` says, with its
  reason;
* `refused`: `check` does not read the model the test is on; `construct`
  is its reason;
* `input`: a test on a seed or a source, which `check` takes as a
  precondition of the models downstream;

beside `dbt`, the test's status in dbt's own run (`pass`, `fail`, `error`,
`skipped`, `warn`). A test sverify-dbt proves that fails in dbt's run is
`unsound`: a soundness bug, fixed first.

`--write` rewrites the ledgers `dbt/replay/<source>.json`, keeping each
entry's `issue`; `--check` exits 1 on an `unsound` entry or an outcome that
changed, and CI turns that into a warning (gates report and never block).
"""

from __future__ import annotations

import argparse
import collections
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[3]
LEDGERS = ROOT / "dbt" / "replay"
CACHE = Path(os.environ.get("SVERIFY_DBT_REPLAY", Path.home() / ".cache/sverify/dbt-replay"))
OUTCOMES = ("proved", "not proved", "not checked", "refused", "input")
_READ = ("proved", "not proved")


@dataclass(frozen=True)
class Source:
    name: str
    repo: str
    tag: str
    project: str
    """The integration project's directory in the repository."""
    license: str


SOURCES = {
    s.name: s
    for s in (
        Source(
            "dbt-utils",
            "https://github.com/dbt-labs/dbt-utils",
            "1.4.1",
            "integration_tests",
            "Apache-2.0",
        ),
        Source(
            "dbt-expectations",
            "https://github.com/metaplane/dbt-expectations",
            "0.10.10",
            "integration_tests",
            "Apache-2.0",
        ),
    )
}


def extract(source: Source, dest: Path) -> Path:
    """The source's repository at its tag, copied to `dest`, with a DuckDB
    profile; the integration project's directory."""
    clone = CACHE / f"{source.name}-{source.tag}"
    if not (clone / ".git").exists():
        clone.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(
            ["git", "-c", "advice.detachedHead=false", "clone", "-q", "--depth", "1"]
            + ["--branch", source.tag, source.repo, str(clone)],
            check=True,
        )
    shutil.copytree(clone, dest, ignore=shutil.ignore_patterns(".git"))
    project = dest / source.project
    name = re.search(r"^profile:\s*['\"]?([\w-]+)", (project / "dbt_project.yml").read_text(), re.M)
    assert name, f"{source.name}: no profile in dbt_project.yml"
    (project / "profiles.yml").write_text(
        f"{name[1]}:\n  target: duckdb\n  outputs:\n"
        f'    duckdb: {{type: duckdb, path: "{project / "replay.duckdb"}", threads: 4}}\n'
    )
    return project


def _dbt(project: Path, *args: str) -> None:
    """A dbt command in `project`; a failing build is part of the record."""
    exe = Path(sys.executable).with_name("dbt")
    subprocess.run(
        [str(exe), *args, "--profiles-dir", str(project), "--project-dir", str(project), "-q"],
        cwd=project,
        check=False,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )


def run(source: Source) -> dict[str, Any]:
    """Build the source's project with dbt, check it with sverify-dbt, and
    the record of each test."""
    from sverify_dbt import check
    from sverify_dbt.manifest import load

    with tempfile.TemporaryDirectory() as tmp:
        project = extract(source, Path(tmp) / source.name)
        _dbt(project, "deps")
        _dbt(project, "build")
        statuses = _statuses(project / "target" / "run_results.json")
        _dbt(project, "docs", "generate", "--no-compile")
        proj = load(project)
        result = check(proj, counterexamples=0)
    return _records(proj, result, statuses)


def _statuses(path: Path) -> dict[str, str]:
    if not path.exists():
        return {}
    return {r["unique_id"]: r["status"] for r in json.loads(path.read_text())["results"]}


def _records(proj: Any, result: Any, statuses: dict[str, str]) -> dict[str, Any]:
    checked = {t.test: (t, m) for m in result.models for t in m.tests if t.test}
    refused = {m.unique_id: m.refused for m in result.models if m.refused}
    out = {}
    for uid, test in sorted(proj.tests.items()):
        rec: dict[str, Any] = {"test": test.short}
        if uid in checked and checked[uid][1].refused:
            t, m = checked[uid]
            rec.update(model=m.name, outcome="refused", construct=normalize(m.refused))
        elif uid in checked:
            t, m = checked[uid]
            rec.update(model=m.name, outcome=t.status)
            if t.why:
                rec["why"] = normalize(t.why)
        elif test.on in refused:
            rec.update(
                model=proj.relations[test.on].name,
                outcome="refused",
                construct=normalize(refused[test.on] or ""),
            )
        elif test.kind is None:
            rec.update(
                outcome="not checked", why="a singular test: sverify-dbt reads generic tests"
            )
        elif test.on in proj.relations and not proj.relations[test.on].is_model:
            rec.update(outcome="input")
        else:
            rec.update(outcome="not checked", why="not on a model sverify-dbt reports")
        rec["dbt"] = statuses.get(uid, "not run")
        if rec["outcome"] == "proved" and rec["dbt"] in ("fail", "warn"):
            rec["unsound"] = True
        out[uid.split(".", 2)[-1]] = rec
    return out


def normalize(text: str, limit: int = 160) -> str:
    """A reason without the project's own names and numbers; issue numbers
    (`#177`) stay."""
    text = (text.strip().splitlines() or [""])[0]
    text = re.sub(r"'[^']*'|\"[^\"]*\"|`[^`]*`", "…", text)
    text = re.sub(r"(?<!#)\b\d+(\.\d+)?\b", "N", text)
    return text[:limit]


# -- the ledgers -------------------------------------------------------------------

CONSTRUCTS = LEDGERS / "constructs.json"


def waits_on(reason: str) -> dict[str, Any]:
    """The issue a refusal or a test not checked waits on: the one it names,
    or the one `constructs.json` gives, or its design reason."""
    if m := re.search(r"#(\d+)", reason):
        return {"issue": int(m[1])}
    if CONSTRUCTS.exists():
        for c in json.loads(CONSTRUCTS.read_text())["constructs"]:
            if c["match"] in reason:
                return {k: c[k] for k in ("issue", "design") if k in c}
    return {}


def ledger(source: Source, results: dict[str, Any]) -> dict[str, Any]:
    for r in results.values():
        reason = r.get("construct") or (r.get("why") if r["outcome"] == "not checked" else None)
        if reason:
            r.update(waits_on(reason))
    counts = collections.Counter(r["outcome"] for r in results.values())
    return {
        "source": source.name,
        "repo": source.repo,
        "tag": source.tag,
        "project": source.project,
        "license": source.license,
        "summary": {k: counts.get(k, 0) for k in OUTCOMES},
        "unsound": sum(1 for r in results.values() if r.get("unsound")),
        "results": results,
    }


def changes(fresh: dict[str, Any], stored: dict[str, Any]) -> list[str]:
    out = [f"unsound: {k}: {r['test']}" for k, r in fresh["results"].items() if r.get("unsound")]
    old = stored.get("results", {})

    def key(r: dict[str, Any]) -> tuple:
        # dbt's own status counts where sverify-dbt reads the test: tests on
        # models sverify refuses include some over random() data, whose
        # status changes between runs.
        return r.get("outcome"), r.get("dbt") if r.get("outcome") in _READ else None

    for k in sorted(fresh["results"].keys() | old.keys()):
        a, b = old.get(k, {}), fresh["results"].get(k, {})
        if key(a) != key(b):
            out.append(
                f"{k}: {a.get('outcome')}/{a.get('dbt')} -> {b.get('outcome')}/{b.get('dbt')}"
            )
    return out


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("sources", nargs="*", default=list(SOURCES))
    ap.add_argument("--write", action="store_true", help="rewrite the ledgers")
    ap.add_argument("--check", action="store_true", help="compare with the ledgers")
    args = ap.parse_args(argv)
    found = []
    for name in args.sources:
        source = SOURCES[name]
        fresh = ledger(source, run(source))
        print(f"{name} {source.tag}: {json.dumps(fresh['summary'])}, unsound {fresh['unsound']}")
        path = LEDGERS / f"{name}.json"
        stored = json.loads(path.read_text()) if path.exists() else {}
        found += [f"{name}: {c}" for c in changes(fresh, stored)]
        if args.write:
            LEDGERS.mkdir(parents=True, exist_ok=True)
            path.write_text(json.dumps(fresh, indent=2, ensure_ascii=False) + "\n")
    if args.check and found:
        print("\n".join(found), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
