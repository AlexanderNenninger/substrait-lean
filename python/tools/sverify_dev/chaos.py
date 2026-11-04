"""The chaos suite's ledger (`python/tests/chaos/`): one JSON line per
scenario, and a Markdown summary of the failures, grouped by signature.

Maintainer tooling (`sverify_dev`): not in the wheel, and not part of sverify's
API.

Each chaos test appends a record to the ledger as soon as it finishes
(`SVERIFY_CHAOS_LEDGER`, default `~/.cache/substrait-lean/chaos/<date>-<branch>-<sha>.jsonl`,
outside the run's checkout so that it survives `homelab_qa.sh`'s cleanup or
an OOM kill). A record holds the run id, commit, time, test, fault point,
setup, outcome (`recovered`, `wrong-result`, `double-applied`, `lost-change`,
`stuck`, `unclear-error`, or `not-reached`), the invariant that failed,
where it raised, and the head of the traceback. A failure's signature is
its outcome, where it raised and the test family; `known.json` beside the
tests maps the filed ones to their issues.

    uv run python -m sverify_dev.chaos path       # this run's ledger
    uv run python -m sverify_dev.chaos run-id
    uv run python -m sverify_dev.chaos summarize <ledger.jsonl>... [--follow SECONDS]

`summarize` reads partial files (a run still going: the last line may be
cut) and several files (runs side by side); `--follow` prints the summary
again every so many seconds, as `tail -f` would.
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
import os
import subprocess
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any

REPO = Path(__file__).resolve().parents[3]
KNOWN = REPO / "python" / "tests" / "chaos" / "known.json"
OUTCOMES = (
    "recovered",
    "wrong-result",
    "double-applied",
    "lost-change",
    "stuck",
    "unclear-error",
    "not-reached",
)
FAILED = {"wrong-result", "double-applied", "lost-change", "stuck", "unclear-error"}


def _git(*args: str) -> str:
    try:
        out = subprocess.run(
            ["git", *args], cwd=REPO, capture_output=True, text=True, check=True, timeout=10
        )
    except (OSError, subprocess.SubprocessError):
        return "unknown"
    return out.stdout.strip() or "unknown"


def commit() -> str:
    return os.environ.get("SVERIFY_CHAOS_COMMIT") or _git("rev-parse", "--short=12", "HEAD")


def branch() -> str:
    name = os.environ.get("SVERIFY_CHAOS_BRANCH") or _git("rev-parse", "--abbrev-ref", "HEAD")
    return name.replace("/", "-")


def run_id() -> str:
    """This run's id: `SVERIFY_CHAOS_RUN`, else the time, branch and commit."""
    if run := os.environ.get("SVERIFY_CHAOS_RUN"):
        return run
    now = dt.datetime.now(dt.UTC).strftime("%Y%m%dT%H%M%SZ")
    return f"{now}-{branch()}-{commit()}"


def ledger_path(run: str | None = None) -> Path:
    """Where this run's records go: `SVERIFY_CHAOS_LEDGER`, else a file
    named after the run under `~/.cache/substrait-lean/chaos/`."""
    if path := os.environ.get("SVERIFY_CHAOS_LEDGER"):
        return Path(path)
    return Path.home() / ".cache" / "substrait-lean" / "chaos" / f"{run or run_id()}.jsonl"


def append(path: Path, record: dict[str, Any]) -> None:
    """Append `record` as one line, in one write to a file opened for
    appending, so the workers of a run share the file."""
    path.parent.mkdir(parents=True, exist_ok=True)
    line = (json.dumps(record, sort_keys=True, default=str) + "\n").encode()
    fd = os.open(path, os.O_WRONLY | os.O_APPEND | os.O_CREAT, 0o644)
    try:
        os.write(fd, line)
    finally:
        os.close(fd)


def read(paths: list[Path]) -> list[dict[str, Any]]:
    """The records of the ledgers, skipping a line cut short (a run that is
    still writing, or was killed)."""
    out = []
    for path in paths:
        for line in path.read_text().splitlines():
            try:
                out.append(json.loads(line))
            except json.JSONDecodeError:
                continue
    return out


def signature(record: dict[str, Any]) -> str:
    return f"{record['outcome']} @ {record.get('where') or '?'} ({record.get('family', '?')})"


def load_known(path: Path = KNOWN) -> list[dict[str, Any]]:
    return json.loads(path.read_text()) if path.exists() else []


def known_issue(record: dict[str, Any], known: list[dict[str, Any]]) -> int | None:
    """The issue of the known signature `record` hits, if any. An entry may
    also name a substring of the test id (`match`) it is limited to."""
    sig = signature(record)
    for k in known:
        if k["signature"] == sig and k.get("match", "") in record.get("test", ""):
            return int(k["issue"])
    return None


def _repro(r: dict[str, Any]) -> str:
    fault = r.get("fault") or {}
    at = f"{fault.get('point')} {fault.get('when', '')} #{fault.get('nth', 1)}" if fault else "-"
    return f"`pytest -m chaos '{r['test']}'` (fault: {at})"


def summarize(paths: list[Path], known: list[dict[str, Any]] | None = None) -> str:
    """The ledgers as Markdown: counts by outcome per run, then one row per
    failure signature, with how many scenarios hit it and the smallest
    repro, new signatures first."""
    known = load_known() if known is None else known
    records = read(paths)
    runs = sorted({r.get("run", "?") for r in records})
    lines = [f"## Chaos summary: {len(records)} scenario(s), {len(runs)} run(s)", ""]
    lines += ["| run | commit | " + " | ".join(OUTCOMES) + " |"]
    lines += ["|---|---|" + "---|" * len(OUTCOMES)]
    for run in runs:
        rs = [r for r in records if r.get("run", "?") == run]
        counts = Counter(r["outcome"] for r in rs)
        lines.append(
            f"| {run} | {rs[0].get('commit', '?')} | "
            + " | ".join(str(counts.get(o, 0)) for o in OUTCOMES)
            + " |"
        )
    groups: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for r in records:
        if r["outcome"] in FAILED:
            groups[signature(r)].append(r)
    lines += ["", "## Failures by signature", ""]
    if not groups:
        lines.append("None: every scenario reached recovered.")
    else:
        lines += ["| status | signature | scenarios | by run | invariant | repro |"]
        lines += ["|---|---|---|---|---|---|"]
        rows = []
        for sig, rs in groups.items():
            issue = known_issue(rs[0], known)
            status = f"known #{issue}" if issue else "NEW"
            by_run = ", ".join(f"{n}" for _, n in sorted(Counter(r["run"] for r in rs).items()))
            best = min(rs, key=lambda r: (r.get("duration", 0), len(r["test"])))
            invariant = (best.get("invariant") or "").replace("|", "/")
            rows.append(
                (issue is not None, -len(rs), status, sig, len(rs), by_run, invariant, best)
            )
        for _, _, status, sig, n, by_run, invariant, best in sorted(rows, key=lambda x: x[:2]):
            sig_md = sig.replace("|", "/")
            lines.append(
                f"| {status} | `{sig_md}` | {n} | {by_run} | {invariant} | {_repro(best)} |"
            )
        lines += ["", "### First error of each signature", ""]
        for sig, rs in groups.items():
            best = min(rs, key=lambda r: (r.get("duration", 0), len(r["test"])))
            lines += [f"`{sig}`", "", "```", (best.get("error") or "").strip()[:1200], "```", ""]
    hit = {known_issue(rs[0], known) for rs in groups.values()}
    missing = [k for k in known if int(k["issue"]) not in hit]
    if missing and records:
        lines += ["", "Known signatures this run did not hit (fixed, or not run): "]
        lines += [f"- #{k['issue']}: `{k['signature']}`" for k in missing]
    return "\n".join(lines) + "\n"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="python -m sverify_dev.chaos", description=__doc__)
    sub = parser.add_subparsers(dest="cmd", required=True)
    sub.add_parser("path", help="print this run's ledger path")
    sub.add_parser("run-id", help="print this run's id")
    s = sub.add_parser("summarize", help="print the Markdown summary of ledgers")
    s.add_argument("ledgers", nargs="+", type=Path)
    s.add_argument("--known", type=Path, default=KNOWN)
    s.add_argument("--follow", type=float, metavar="SECONDS", default=None)
    args = parser.parse_args(argv)
    if args.cmd == "path":
        print(ledger_path())
        return 0
    if args.cmd == "run-id":
        print(run_id())
        return 0
    known = load_known(args.known)
    while True:
        existing = [p for p in args.ledgers if p.exists()]
        print(summarize(existing, known), flush=True)
        if args.follow is None:
            return 0
        time.sleep(args.follow)


if __name__ == "__main__":
    sys.exit(main())
