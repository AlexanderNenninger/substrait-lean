"""Replay dbt test projects others wrote through sverify-dbt (#859).

Maintainers' tooling, not part of sverify-dbt's API and not in its wheel
(`pyproject.toml` excludes it): `python -m sverify_dbt.replay` from this
repository.

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
`unsound`: a soundness bug, fixed first. An enforced contract's constraints
are recorded too (`kind: constraint`), beside dbt's build of the model.

`--write` rewrites the ledgers `dbt/replay/<source>.json`, keeping each
entry's `issue`; `--check` exits 1 on an outcome that changed or an entry
waiting on a closed issue (asked of `gh`, skipped without it), which CI
turns into a warning. Either exits 2 on an `unsound` entry, read from the
fresh run, never from a ledger, so re-recording cannot hide it: CI fails on
it, since a wrong proof is a correctness bug.
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
from collections.abc import Callable
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
    commit: str
    """The tag's commit: the replay fetches it, so a moved tag changes nothing."""
    project: str
    """The integration project's directory in the repository."""
    license: str
    kind: str = "package"
    """`package`: a hub package's integration project, cloned at `commit`.
    `suite`: the pytest classes of an installed test suite (`project` is its
    import package), whose release `tag` must be the one installed.
    `repo-suite`: the pytest classes of a test suite that ships in no wheel,
    cloned at `commit` (`project` is its directory, `folders` the ones read)."""
    folders: tuple[str, ...] = ()
    """For a `repo-suite`, the directories under `project` whose classes are
    replayed: those whose projects carry tests or contracts."""


SOURCES = {
    s.name: s
    for s in (
        Source(
            "dbt-utils",
            "https://github.com/dbt-labs/dbt-utils",
            "1.4.1",
            "49b932cb1f6fd0f7dfbf9048512db6415f570b20",
            "integration_tests",
            "Apache-2.0",
        ),
        Source(
            "dbt-expectations",
            "https://github.com/metaplane/dbt-expectations",
            "0.10.10",
            "f93478ca00b48347073f6a39217ac18bf6685820",
            "integration_tests",
            "Apache-2.0",
        ),
        Source(
            "dbt-core",
            "https://github.com/dbt-labs/dbt-core",
            "v1.12.6",
            "78d8367e143e753fe53c553af478708d23ccf5cc",
            "tests/functional",
            "Apache-2.0",
            kind="repo-suite",
            folders=(
                "constraints",
                "contracts",
                "data_tests",
                "incremental_schema_tests",
                "primary_keys",
                "schema_tests",
                "sources",
            ),
        ),
        Source(
            "dbt-tests-adapter",
            "https://github.com/dbt-labs/dbt-adapters",
            "1.20.0",
            "",
            "dbt.tests.adapter",
            "Apache-2.0",
            kind="suite",
        ),
    )
}


def _clone(source: Source) -> Path:
    """The source's repository at its commit, cloned once into the cache."""
    clone = CACHE / f"{source.name}-{source.commit[:12]}"
    git = ["git", "-C", str(clone)]
    if not (clone / ".git").exists():
        clone.mkdir(parents=True, exist_ok=True)
        subprocess.run([*git, "init", "-q"], check=True)
        subprocess.run(
            [*git, "fetch", "-q", "--depth", "1", source.repo, source.commit], check=True
        )
        subprocess.run(
            [*git, "-c", "advice.detachedHead=false", "checkout", "-q", "FETCH_HEAD"], check=True
        )
    head = subprocess.run([*git, "rev-parse", "HEAD"], capture_output=True, text=True, check=True)
    if head.stdout.strip() != source.commit:
        raise SystemExit(f"{source.name}: {clone} is at {head.stdout.strip()}, not {source.commit}")
    return clone


def extract(source: Source, dest: Path) -> Path:
    """The source's repository at its commit, copied to `dest`, with a DuckDB
    profile; the integration project's directory."""
    clone = _clone(source)
    shutil.copytree(clone, dest, ignore=shutil.ignore_patterns(".git"))
    project = dest / source.project
    name = re.search(
        r"^profile:\s*['\"]?([\w-]+)",
        (project / "dbt_project.yml").read_text(encoding="utf-8"),
        re.M,
    )
    assert name, f"{source.name}: no profile in dbt_project.yml"
    (project / "profiles.yml").write_text(
        f"{name[1]}:\n  target: duckdb\n  outputs:\n"
        f'    duckdb: {{type: duckdb, path: "{project / "replay.duckdb"}", threads: 4}}\n',
        encoding="utf-8",
    )
    return project


def _dbt(project: Path, *args: str, quiet: bool = False) -> None:
    """A dbt command in `project`; a failing build is part of the record, and
    its last lines are printed, for CI's log."""
    exe = Path(sys.executable).with_name("dbt")
    done = subprocess.run(
        [str(exe), *args, "--profiles-dir", str(project), "--project-dir", str(project)],
        cwd=project,
        check=False,
        capture_output=True,
        text=True,
    )
    if done.returncode != 0 and not quiet:
        tail = (done.stdout + done.stderr).strip().splitlines()[-15:]
        print(
            f"dbt {' '.join(args)} exited {done.returncode} in {project.name}:", *tail, sep="\n  "
        )


def run(source: Source) -> dict[str, Any]:
    """Build the source's project with dbt, check it with sverify-dbt, and
    the record of each test."""
    if source.kind in ("suite", "repo-suite"):
        return _run_suite(source)
    with tempfile.TemporaryDirectory() as tmp:
        project = extract(source, Path(tmp) / source.name)
        _dbt(project, "deps")
        packages = _packages(project / "package-lock.yml")
        results = _replay(project)
    return {"packages": packages, "results": results}


def _replay(project: Path, quiet: bool = False) -> dict[str, Any]:
    """`dbt build` and `docs generate` in `project`, then the record of its tests."""
    from sverify_dbt import check
    from sverify_dbt.manifest import load

    _dbt(project, "build", quiet=quiet)
    statuses = _statuses(project / "target" / "run_results.json")
    _dbt(project, "docs", "generate", "--no-compile", quiet=quiet)
    proj = load(project)
    result = check(proj, counterexamples=0)
    return _records(proj, result, statuses)


def _run_suite(source: Source) -> dict[str, Any]:
    """Every distinct project of an installed pytest suite, built and checked
    one after the other; the classes it cannot read are listed beside."""
    import importlib
    import importlib.metadata

    from sverify_dbt import replay_suites
    from sverify_dbt.manifest import ProjectError

    if source.kind == "suite":
        installed = importlib.metadata.version(source.name)
        if installed != source.tag:
            raise SystemExit(f"{source.name} {installed} is installed, not {source.tag}")
        package = source.project
        roots = [(Path(importlib.import_module(package).__path__[0]), package)]
    else:
        clone = _clone(source)
        sys.path.insert(0, str(clone))  # `tests.functional...` imports from the clone
        package = source.project.replace("/", ".")
        roots = [(clone / source.project / f, f"{package}.{f}") for f in source.folders]
    cases, unextracted = [], {}
    for root, pkg in roots:
        found, missed = replay_suites.projects(root, pkg)
        cases += found
        unextracted |= missed
    results: dict[str, Any] = {}
    with tempfile.TemporaryDirectory() as tmp:
        for case in cases:
            if not case.has_tests:
                continue  # nothing to check: no build, no `docs generate`
            project = Path(tmp) / re.sub(r"\W", "_", case.name)
            replay_suites.write(case, project)
            label = case.name.removeprefix(package + ".")
            try:
                records = _replay(project, quiet=True)
            except (ProjectError, ValueError) as e:
                unextracted[case.name] = f"not replayed: {normalize(str(e))}"
                continue
            except Exception as e:  # noqa: BLE001 - one project's crash must not end the replay
                # A sverify-dbt bug: listed, to be fixed.
                unextracted[case.name] = f"crashed: {type(e).__name__}: {normalize(str(e))}"
                continue
            for key, rec in records.items():
                results[f"{label}::{key}"] = rec
    return {"packages": [], "results": results, "unextracted": dict(sorted(unextracted.items()))}


def _packages(lock: Path) -> list[str]:
    """The hub packages `dbt deps` resolved (`package-lock.yml`), as
    `package@version`: the projects state ranges, so a new release changes
    what the replay runs."""
    import yaml

    if not lock.exists():
        return []
    entries = yaml.safe_load(lock.read_text(encoding="utf-8")).get("packages") or []
    return sorted(f"{e['package']}@{e['version']}" for e in entries if "package" in e)


def _statuses(path: Path) -> dict[str, str]:
    if not path.exists():
        return {}
    return {
        r["unique_id"]: r["status"] for r in json.loads(path.read_text(encoding="utf-8"))["results"]
    }


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
    # An enforced contract's constraints, beside dbt's own build of the model,
    # which enforces them: a model dbt fails is a contract its data breaks.
    for m in result.models:
        if not m.enforced:
            continue
        for c in m.constraints:
            rec = {"test": c.label, "model": m.name, "kind": "constraint"}
            if m.refused:
                rec.update(outcome="refused", construct=normalize(m.refused))
            else:
                rec.update(outcome=c.status.replace("_", " "))
                if c.why:
                    rec["why"] = normalize(c.why)
            rec["dbt"] = statuses.get(m.unique_id, "not run")
            out[f"{m.unique_id.split('.', 2)[-1]}::{c.label}"] = rec
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
        for c in json.loads(CONSTRUCTS.read_text(encoding="utf-8"))["constructs"]:
            if c["match"] in reason:
                return {k: c[k] for k in ("issue", "design") if k in c}
    return {}


def ledger(source: Source, run: dict[str, Any]) -> dict[str, Any]:
    results = run["results"]
    for r in results.values():
        reason = r.get("construct") or (r.get("why") if r["outcome"] == "not checked" else None)
        if reason:
            r.update(waits_on(reason))
    counts = collections.Counter(r["outcome"] for r in results.values())
    return {
        "source": source.name,
        "repo": source.repo,
        "tag": source.tag,
        "commit": source.commit,
        "packages": run["packages"],
        "project": source.project,
        "license": source.license,
        "summary": {k: counts.get(k, 0) for k in OUTCOMES},
        "unsound": sum(1 for r in results.values() if r.get("unsound")),
        "results": results,
        **({"unextracted": run["unextracted"]} if run.get("unextracted") else {}),
    }


def changes(fresh: dict[str, Any], stored: dict[str, Any]) -> list[str]:
    out = [f"unsound: {k}: {r['test']}" for k, r in fresh["results"].items() if r.get("unsound")]
    if fresh["packages"] != stored.get("packages"):
        # Another release of a dependency: the outcomes below are of other code.
        out.append(f"packages: {stored.get('packages')} -> {fresh['packages']}")
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


def _gh_state(number: int) -> str | None:
    """The state of issue `number` (`OPEN`, `CLOSED`), or None without `gh`."""
    try:
        out = subprocess.run(
            ["gh", "issue", "view", str(number), "--json", "state", "--jq", ".state"],
            capture_output=True,
            text=True,
            timeout=30,
            check=True,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    return out.stdout.strip() or None


def closed_issues(
    ledgers: dict[str, dict[str, Any]], state: Callable[[int], str | None] = _gh_state
) -> list[str]:
    """The entries that wait on an issue that is closed: the refusal has
    another reason now, or the issue's fix has landed."""
    waiting: dict[int, list[str]] = {}
    for name, led in ledgers.items():
        for key, r in led["results"].items():
            if "issue" in r:
                waiting.setdefault(r["issue"], []).append(f"{name}: {key}")
    out = []
    for number, entries in sorted(waiting.items()):
        found = state(number)
        if found is None:
            print("closed-issue check skipped: gh unavailable", file=sys.stderr)
            break
        if found == "CLOSED":
            out.append(
                f"#{number} is closed; {len(entries)} entries wait on it, such as {entries[0]}"
            )
    return out


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("sources", nargs="*", default=list(SOURCES))
    ap.add_argument("--write", action="store_true", help="rewrite the ledgers")
    ap.add_argument("--check", action="store_true", help="compare with the ledgers")
    args = ap.parse_args(argv)
    found = []
    unsound = []
    for name in args.sources:
        source = SOURCES[name]
        fresh = ledger(source, run(source))
        print(f"{name} {source.tag}: {json.dumps(fresh['summary'])}, unsound {fresh['unsound']}")
        path = LEDGERS / f"{name}.json"
        stored = json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}
        found += [f"{name}: {c}" for c in changes(fresh, stored)]
        unsound += [
            f"{name}: {k}: {r['test']}" for k, r in fresh["results"].items() if r.get("unsound")
        ]
        if args.write:
            LEDGERS.mkdir(parents=True, exist_ok=True)
            path.write_text(
                json.dumps(fresh, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
            )
    if args.check:
        found += closed_issues(
            {
                n: json.loads((LEDGERS / f"{n}.json").read_text(encoding="utf-8"))
                for n in args.sources
            }
        )
    if unsound:
        print("unsound, a proof dbt's own run contradicts:", *unsound, sep="\n  ", file=sys.stderr)
        return 2
    if args.check and found:
        print("\n".join(found), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
