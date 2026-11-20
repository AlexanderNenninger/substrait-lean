"""The engine release canary (#2053, ruling 198, D70, conditions K1 to K6).

Maintainer tooling (`sverify_dev`): not in the wheel, and not part of sverify's
API. `.github/workflows/engine-canary.yml` runs it; it is no required check and
no part of `qa` (K4), and it files nothing upstream (K6).

    python -m sverify_dev.canary poll [--engine E --version V]
    python -m sverify_dev.canary drift --engine E --old FILE --new FILE
    python -m sverify_dev.canary collect --engine E --version V --drift FILE... [--suite-exit N ...]
    python -m sverify_dev.canary report --engine E --version V --results FILE [--post]

`poll` (K1) compares each engine's latest PyPI release with the versions its
profile was probed at (`version` and `alsoProbed` of `engines/<engine>/Sverify/…/Tables.lean`)
and prints the matrix of engines with a release nobody has probed. It stops in
seconds when nothing is new, and skips a version that already has its issue. By hand,
`--engine` and `--version` name the one to run.

The heavy job (K2) probes the ledger, probes every fact, and runs the engine's
suite and the `outside-repo` set unpinned. `drift` compares a probe file with its
recording and classes each difference (K3): an outcome that changes from a raise to
a value (the engine raises less) or from a value to a raise (it raises more) is
error-side, since no guarantee rests on an engine raising (D70), and any other
change of a recorded value is value-side. A value-side drift inside the probed range
is a bug. `report` writes one issue per engine version, updated in place.

Snowflake behaviour is recorded privately; its canary, if any, runs in the private
repository, and nothing here names it (K5).
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import urllib.request
from collections.abc import Callable, Iterable
from pathlib import Path
from typing import Any

REPO = Path(__file__).resolve().parents[3]

#: The engines the public canary covers: the PyPI package of each, and the module of its
#: profile table (`Profile.<engine>.table`).
ENGINES: dict[str, dict[str, str]] = {
    "duckdb": {"package": "duckdb", "tables": "engines/duckdb/Sverify/DuckDB/Tables.lean"},
    "polars": {"package": "polars", "tables": "engines/polars/Sverify/Polars/Tables.lean"},
    "spark": {"package": "pyspark", "tables": "engines/spark/Sverify/Spark/Tables.lean"},
}

#: The probes of each engine the heavy job compares with their recording.
PROBES: dict[str, list[str]] = {
    "duckdb": ["engines/duckdb/replay/probes.json"],
    "polars": ["engines/polars/probes/probes.json", "engines/polars/probes/probes-streaming.json"],
    "spark": ["engines/spark/probes/probes.json"],
}

Json = dict[str, Any]


# --- the probed versions (K1) -------------------------------------------------------------


def probed(engine: str, root: Path = REPO) -> list[str]:
    """The versions `engine`'s facts were probed at: the table's `version`, then its
    `alsoProbed` (the checker's `profiles.<engine>.versions`)."""
    text = (root / ENGINES[engine]["tables"]).read_text()
    version = re.search(r'^\s*version := "([^"]+)"', text, re.M)
    if version is None:
        raise ValueError(f"no `version :=` in {ENGINES[engine]['tables']}")
    also = re.search(r"^\s*alsoProbed := \[([^\]]*)\]", text, re.M)
    return [version.group(1), *(re.findall(r'"([^"]+)"', also.group(1)) if also else [])]


def _key(version: str) -> tuple[int, ...]:
    return tuple(int(p) for p in version.split("."))


def is_release(version: str) -> bool:
    """A final release (`2.0.1`), not a pre-release or a development build."""
    return re.fullmatch(r"\d+(\.\d+)*", version) is not None


def pypi_latest(package: str) -> str:
    """The latest final release of `package` on PyPI."""
    url = f"https://pypi.org/pypi/{package}/json"
    with urllib.request.urlopen(url, timeout=30) as r:  # noqa: S310 - a fixed https URL
        info = json.load(r)
    releases = [v for v, files in info["releases"].items() if is_release(v) and files]
    return max(releases, key=_key)


def new_releases(
    latest: Callable[[str], str] = pypi_latest, root: Path = REPO
) -> list[dict[str, str]]:
    """The engines whose latest release is newer than every probed version."""
    out = []
    for engine, spec in ENGINES.items():
        have = probed(engine, root)
        version = latest(spec["package"])
        if version not in have and _key(version) > max(map(_key, have)):
            out.append({"engine": engine, "version": version})
    return out


def title(engine: str, version: str) -> str:
    return f"Engine release canary: {engine} {version}"


def issue_number(engine: str, version: str) -> int | None:
    """The issue of this engine version (open or closed), if the canary filed one."""
    search = f'"{title(engine, version)}" in:title'
    cmd = ["gh", "issue", "list", "--state", "all", "--search", search, "--json", "number,title"]
    out = subprocess.run(cmd, check=True, capture_output=True, text=True).stdout
    for i in json.loads(out):
        if i["title"] == title(engine, version):
            return i["number"]
    return None


# --- drift (K2, K3) -----------------------------------------------------------------------

#: The fields that name a probe: a row of the probe file is the same row when they agree.
IDENTITY = ("settings", "construct", "function", "option", "sql", "setup", "name", "probe", "id")
#: The fields whose change is a drift; the examples of a probe say why, and are not compared.
VALUES = ("matching", "observed", "verdict", "result", "outcome")


def _is_error(outcome: Any) -> bool:
    return isinstance(outcome, str) and outcome.lstrip().lower().startswith("error")


def classify(old: Any, new: Any) -> str:
    """`error-side` where a raise became a value or a value a raise (D70: no guarantee rests on
    an engine raising); `value-side` where one value became another."""
    if _is_error(old) != _is_error(new):
        return "error-side"
    return "value-side"


def _rows(doc: Any) -> dict[str, Json]:
    rows = doc.get("probes", []) if isinstance(doc, dict) else doc
    out: dict[str, Json] = {}
    for r in rows:
        ident = json.dumps({k: r[k] for k in IDENTITY if k in r}, sort_keys=True)
        out[ident] = r
    return out


def drift(old: Any, new: Any) -> list[Json]:
    """The rows of `new` whose values differ from `old`'s, each with its class."""
    before, after = _rows(old), _rows(new)
    found: list[Json] = []
    for ident, r in after.items():
        p = before.get(ident)
        what = json.loads(ident)
        if p is None:
            found.append(
                {
                    "row": what,
                    "old": None,
                    "new": "a row the recording lacks",
                    "class": "value-side",
                }
            )
            continue
        for f in VALUES:
            if p.get(f) != r.get(f):
                cls = classify(p.get(f), r.get(f)) if f == "observed" else "value-side"
                found.append(
                    {"row": what, "field": f, "old": p.get(f), "new": r.get(f), "class": cls}
                )
    for ident in before.keys() - after.keys():
        gone = "a row the probe no longer has"
        found.append(
            {"row": json.loads(ident), "old": "recorded", "new": gone, "class": "value-side"}
        )
    return found


# --- ledger (K2) --------------------------------------------------------------------------

#: The upstream-bug ledger's project of each engine (`upstream/bugs/<id>.json`).
PROJECT = {"duckdb": "duckdb", "polars": "polars", "spark": "spark"}


def ledger(engine: str, version: str, root: Path = REPO) -> list[Json]:
    """The bugs of the engine whose fix is named for this release (`fixed_in`): a patch release
    exists to fix bugs, so a fixed `DD-n` is the likeliest drift, and the ledger wants the
    release the fix landed in."""
    out = []
    for path in sorted((root / "upstream" / "bugs").glob("*.json")):
        bug = json.loads(path.read_text())
        if bug.get("project") != PROJECT[engine]:
            continue
        fixed = str(bug.get("fixed_in", ""))
        if re.match(rf"{re.escape(version)}(\s|$)", fixed):
            out.append({"id": bug["id"], "status": bug.get("status"), "fixed_in": fixed})
    return out


# --- the issue (K3) -----------------------------------------------------------------------


def _cell(x: Any) -> str:
    text = json.dumps(x, ensure_ascii=False) if not isinstance(x, str) else x
    return text.replace("|", "\\|").replace("\n", " ")[:160]


def body(engine: str, version: str, results: Json) -> str:
    """The issue's text: one section per step, each drift classed, and the verdict."""
    have = results.get("probed") or probed(engine)
    drifts: list[Json] = results.get("drift", [])
    value = [d for d in drifts if d["class"] == "value-side"]
    lines = [
        f"{engine} {version} is not among the probed versions ({', '.join(have)}). "
        "The canary ran the ledger, the fact probes, the engine's suite and the `outside-repo` "
        f"set unpinned ([run]({results.get('run_url', '')})).",
        "",
        "## Ledger",
        "",
    ]
    bugs = results.get("ledger", [])
    lines += [f"- {b['id']} ({b['status']}): fixed in {b['fixed_in']}" for b in bugs] or [
        "No bug of the ledger names this release."
    ]
    lines += ["", "## Fact probes", ""]
    if drifts:
        lines += ["| row | field | recorded | now | class |", "|---|---|---|---|---|"]
        lines += [
            f"| {_cell(d['row'])} | {d.get('field', '')} | {_cell(d['old'])} | "
            f"{_cell(d['new'])} | {d['class']} |"
            for d in drifts
        ]
    else:
        lines += ["No probe differs from its recording."]
    for step, name in (("suite", "The engine's suite"), ("outside", "The `outside-repo` set")):
        r = results.get(step, {})
        lines += ["", f"## {name}", "", f"exit {r.get('exit', 'not run')}"]
        if r.get("summary"):
            lines += ["", "```", r["summary"], "```"]
    failed = [s for s in ("suite", "outside") if results.get(s, {}).get("exit") not in (0, None)]
    lines += ["", "## Verdict", ""]
    if value or failed:
        lines += [
            f"Value-side drift: {len(value)} probe row(s); failing step(s): "
            f"{', '.join(failed) or 'none'}. {engine} {version} is inside the package's range "
            "(D70), so users run on it today with a warning: this is a bug (K3). Each row needs a "
            "lowering that reads the engine only where the versions agree, and its input added "
            "to the fact's probe (the ruling's K2 amendment)."
        ]
    else:
        lines += [
            f"No value-side drift. Adding {version} to the probed versions is one line: "
            f'`alsoProbed := [..., "{version}"]` in `{ENGINES[engine]["tables"]}`, with '
            "`uv.lock` moved when it is the pin."
        ]
    lines += ["", "Raises that appear or disappear are error-side (D70)."]
    return "\n".join(lines) + "\n"


def post(engine: str, version: str, text: str) -> None:
    """Create the engine version's issue, or edit it in place."""
    n = issue_number(engine, version)
    if n is None:
        subprocess.run(
            [
                "gh",
                "issue",
                "create",
                "--title",
                title(engine, version),
                "--body",
                text,
                "--label",
                "engines",
            ],
            check=True,
        )
    else:
        subprocess.run(["gh", "issue", "edit", str(n), "--body", text], check=True)


def _tail(path: Path | None, lines: int = 20) -> str:
    if path is None or not path.is_file():
        return ""
    return "\n".join(path.read_text(errors="replace").splitlines()[-lines:])


def collect(  # noqa: PLR0913 - one argument per step of the heavy job
    engine: str,
    version: str,
    drifts: Iterable[Path],
    suite: tuple[int | None, Path | None],
    outside: tuple[int | None, Path | None],
    run_url: str = "",
    root: Path = REPO,
) -> Json:
    """The heavy job's results, as `body` reads them."""
    found: list[Json] = []
    for f in drifts:
        found += json.loads(f.read_text())
    return {
        "probed": probed(engine, root),
        "run_url": run_url,
        "ledger": ledger(engine, version, root),
        "drift": found,
        "suite": {"exit": suite[0], "summary": _tail(suite[1])},
        "outside": {"exit": outside[0], "summary": _tail(outside[1])},
    }


# --- command line -------------------------------------------------------------------------


def _matrix(include: Iterable[dict[str, str]]) -> str:
    return json.dumps({"include": list(include)}, separators=(",", ":"))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = parser.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("poll", help="the engines with a release nobody has probed")
    p.add_argument("--engine", choices=sorted(ENGINES))
    p.add_argument("--version")
    p.add_argument("--no-issues", action="store_true", help="do not look for an existing issue")
    d = sub.add_parser("drift", help="the rows of a probe file that differ from its recording")
    d.add_argument("--engine", required=True, choices=sorted(ENGINES))
    d.add_argument("--old", type=Path, required=True)
    d.add_argument("--new", type=Path, required=True)
    c = sub.add_parser("collect", help="the heavy job's results, as one JSON file")
    c.add_argument("--engine", required=True, choices=sorted(ENGINES))
    c.add_argument("--version", required=True)
    c.add_argument("--drift", type=Path, action="append", default=[])
    c.add_argument("--suite-exit", type=int)
    c.add_argument("--suite-log", type=Path)
    c.add_argument("--outside-exit", type=int)
    c.add_argument("--outside-log", type=Path)
    c.add_argument("--run-url", default="")
    r = sub.add_parser("report", help="the issue of one engine version")
    r.add_argument("--engine", required=True, choices=sorted(ENGINES))
    r.add_argument("--version", required=True)
    r.add_argument("--results", type=Path, required=True)
    r.add_argument("--post", action="store_true")
    args = parser.parse_args(argv)
    if args.cmd == "poll":
        if args.engine or args.version:
            if not (args.engine and args.version):
                parser.error("--engine and --version go together")
            todo = [{"engine": args.engine, "version": args.version}]
        else:
            todo = new_releases()
            if not args.no_issues:
                todo = [t for t in todo if issue_number(t["engine"], t["version"]) is None]
        print(_matrix(todo))
    elif args.cmd == "drift":
        found = drift(json.loads(args.old.read_text()), json.loads(args.new.read_text()))
        print(json.dumps(found, indent=1))
    elif args.cmd == "collect":
        out = collect(
            args.engine, args.version, args.drift, (args.suite_exit, args.suite_log),
            (args.outside_exit, args.outside_log), args.run_url,
        )  # fmt: skip
        print(json.dumps(out, indent=1))
    else:
        results = json.loads(args.results.read_text())
        text = body(args.engine, args.version, results)
        if args.post:
            post(args.engine, args.version, text)
        else:
            sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
