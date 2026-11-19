"""The nightly fuzz run on the AWS spot runners (#747): batches, a ledger of
distinct mismatches, a report and a repro per mismatch.

Maintainer tooling (`sverify_dev`): not in the wheel, and not part of sverify's
API. `.github/workflows/fuzz.yml` runs it; it works the same on homelab.

A batch is one fuzzer for a time budget with one seed, in a process of its
own (`batch`):

- `core`: `sverify_dev.fuzz`, random queries against Lean on DuckDB and the
  engines of `sverify.engine.ENGINES`;
- `duckdb:<target>`: `sverify_dev.duckdb_fuzz`, DuckDB's own SQL against
  `Rel.eval`, one of its targets;
- `hypothesis:<i>/<n>`: the Hypothesis tests of `python/tests` (the
  `hypothesis` marker, no Spark, no chaos), shard `i` of `n`, with
  `SVERIFY_EXAMPLES` times their examples and the seed as `--hypothesis-seed`.

Every batch runs under a wall-time limit and a memory watchdog over its
process tree; the checker keeps its own cap (`SVERIFY_CHECKER_MEMORY_MB`,
4096 by default, #1074). A batch over either limit is stopped and recorded,
and the others go on, so a spot reclaim or a runaway loses one batch.

`merge` folds the batches' findings into the ledger: one entry per
signature (the fuzzer and oracle, the query's shape with its literals
blanked, and the class of the differing values), with the first and last
night it was seen, a count, its seeds and one example. `report` prints the
night's findings, new ones first, for triage; nothing is filed anywhere.
`repro` prints the one command that reproduces a ledger entry.

`merge`, `report` and `repro` use the standard library only, so they run on
any Python 3.12 without installing sverify.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
import re
import signal
import subprocess
import sys
import time
import xml.etree.ElementTree as ET
from collections.abc import Iterable, Sequence
from pathlib import Path
from typing import Any

PYTHON_DIR = Path(__file__).resolve().parents[2]
"""`python/`: where the batches run."""

#: Examples per Hypothesis test, as a multiple of each test's own count.
EXAMPLES = "3"


# --- batches ------------------------------------------------------------------------


def command(suite: str, seed: int, seconds: float, out: Path) -> tuple[list[str], dict[str, str]]:
    """The process a batch runs, and the environment it adds."""
    py = sys.executable
    if suite == "core":
        return [
            py,
            "-m",
            "sverify_dev.fuzz",
            "--budget",
            str(seconds),
            "--seed",
            str(seed),
            "--json",
            str(out / "core.json"),
        ], {}
    if suite.startswith("duckdb:"):
        target = suite.split(":", 1)[1]
        return [
            py,
            "-m",
            "sverify_dev.duckdb_fuzz",
            target,
            "--budget",
            str(seconds),
            "--seed",
            str(seed),
            "--out",
            str(out / "duckdb"),
        ], {}
    if suite.startswith("hypothesis:"):
        shard = suite.split(":", 1)[1]
        return [
            py,
            "-m",
            "pytest",
            "-m",
            "hypothesis and not spark and not chaos",
            "-p",
            "no:cacheprovider",
            "-q",
            "-n",
            "2",
            f"--hypothesis-seed={seed}",
            f"--junitxml={out / 'junit.xml'}",
            "tests",
        ], {"SVERIFY_SHARD": shard, "SVERIFY_EXAMPLES": EXAMPLES, "SVERIFY_PROFILE": "ci"}
    raise SystemExit(f"unknown suite {suite!r}")


def _tree_rss_mb(root: int) -> int:
    """The resident memory of `root` and its descendants, in MB (Linux)."""
    children: dict[int, list[int]] = {}
    rss: dict[int, int] = {}
    for stat in Path("/proc").glob("[0-9]*/stat"):
        try:
            fields = stat.read_text().rsplit(")", 1)[1].split()
        except OSError:
            continue
        pid = int(stat.parent.name)
        children.setdefault(int(fields[1]), []).append(pid)
        rss[pid] = int(fields[21]) * os.sysconf("SC_PAGE_SIZE")
    total, todo = 0, [root]
    while todo:
        pid = todo.pop()
        total += rss.get(pid, 0)
        todo.extend(children.get(pid, []))
    return total // 2**20


def batch(suite: str, seed: int, seconds: float, out: Path, timeout: float, rss_mb: int) -> dict:
    """Run one batch; record and return how it ended."""
    out.mkdir(parents=True, exist_ok=True)
    argv, env = command(suite, seed, seconds, out)
    start = time.monotonic()
    peak, status = 0, "ok"
    with open(out / "log.txt", "w") as log:
        proc = subprocess.Popen(
            argv,
            cwd=PYTHON_DIR,
            env={**os.environ, **env},
            stdout=log,
            stderr=subprocess.STDOUT,
            start_new_session=True,
        )
        while proc.poll() is None:
            if sys.platform.startswith("linux"):
                peak = max(peak, _tree_rss_mb(proc.pid))
            if peak > rss_mb:
                status = "memory"
            elif time.monotonic() - start > timeout:
                status = "timeout"
            if status != "ok":
                os.killpg(proc.pid, signal.SIGKILL)
                proc.wait()
                break
            time.sleep(2)
    if status == "ok" and proc.returncode not in (0, 1):
        status = f"exit {proc.returncode}"
    record = {
        "suite": suite,
        "seed": seed,
        "seconds": seconds,
        "status": status,
        "elapsed": round(time.monotonic() - start),
        "peak_rss_mb": peak,
        "date": dt.date.today().isoformat(),
    }
    (out / "batch.json").write_text(json.dumps(record, indent=1))
    return record


# --- findings and signatures ----------------------------------------------------------

_LITERAL = re.compile(r"'(?:[^']|'')*'|\b\d+(?:\.\d+)?(?:e[+-]?\d+)?\b", re.IGNORECASE)


def shape(sql: str) -> str:
    """A query with its literals blanked and its spacing normalised."""
    return " ".join(_LITERAL.sub("?", sql).split())


def value_class(text: str) -> str:
    """The class of the values a mismatch shows: an error, NaN, an infinity,
    NULL, a negative zero, or plain values."""
    t = text.lower()
    for cls, marks in (
        ("error", ("raises", "error", "exception")),
        ("nan", ("nan",)),
        ("inf", ("inf",)),
        ("null", ("none", "null")),
        ("negzero", ("-0.0",)),
    ):
        if any(m in t for m in marks):
            return cls
    return "value"


def signature(kind: str, sql_or_node: str, values: str) -> list[str]:
    return [kind, sql_or_node, value_class(values)]


def sig_id(sig: Sequence[str]) -> str:
    return hashlib.sha256("\x1f".join(sig).encode()).hexdigest()[:12]


def findings(batch_dir: Path) -> list[dict[str, Any]]:
    """The findings of one batch's directory, each with its signature and
    the command that reproduces it."""
    meta = json.loads((batch_dir / "batch.json").read_text())
    suite, seed, seconds = meta["suite"], meta["seed"], meta["seconds"]
    found: list[dict[str, Any]] = []
    if (path := batch_dir / "core.json").exists():
        for f in json.loads(path.read_text()):
            found.append(
                {
                    "sig": signature(f"core:{f['oracle']}", shape(f["sql"]), f["detail"]),
                    "example": f,
                    "repro": "cd python && uv run python -m sverify_dev.fuzz --replay {file}",
                }
            )
    for ledger in sorted((batch_dir / "duckdb").rglob("*.json")):
        target = suite.split(":", 1)[1]
        for r in json.loads(ledger.read_text()).get("results", []):
            if r.get("cls") != "disagree":
                continue
            found.append(
                {
                    "sig": signature(
                        f"duckdb:{target}", shape(r["sql"]), f"{r.get('lean')} {r.get('duckdb')}"
                    ),
                    "example": r,
                    "repro": f"cd python && uv run python -m sverify_dev.duckdb_fuzz {target} "
                    f"--seed {seed} --budget {seconds:g} --out /tmp/fuzz",
                }
            )
    if (path := batch_dir / "junit.xml").exists():
        for case in ET.parse(path).getroot().iter("testcase"):
            fail = case.find("failure")
            if fail is None:
                fail = case.find("error")
            if fail is None:
                continue
            node = f"{case.get('classname', '').replace('.', '/')}.py::{case.get('name', '')}"
            node = re.sub(r"\[.*\]$", "", node)
            message = fail.get("message") or ""
            found.append(
                {
                    "sig": [
                        f"hypothesis:{fail.get('type') or fail.tag}",
                        node,
                        value_class(message),
                    ],
                    "example": {"node": node, "message": message[:2000]},
                    "repro": f"cd python && SVERIFY_EXAMPLES={EXAMPLES} SVERIFY_PROFILE=ci "
                    f"uv run pytest '{node}' --hypothesis-seed={seed} -p no:cacheprovider",
                }
            )
    for f in found:
        f.update(suite=suite, seed=seed, date=meta["date"])
    return found


# --- the ledger ----------------------------------------------------------------------


def merge(ledger: dict[str, Any], batch_dirs: Iterable[Path]) -> tuple[dict[str, Any], list[dict]]:
    """The ledger with the batches' findings folded in, and the night's
    findings (each marked `new` when its signature is not in the ledger yet)."""
    entries: dict[str, Any] = dict(ledger.get("entries", {}))
    night: list[dict] = []
    batches: list[dict] = []
    for d in batch_dirs:
        if not (d / "batch.json").exists():
            continue
        batches.append(json.loads((d / "batch.json").read_text()))
        for f in findings(d):
            key = sig_id(f["sig"])
            new = key not in entries
            e = entries.setdefault(
                key,
                {
                    "signature": f["sig"],
                    "first_seen": f["date"],
                    "count": 0,
                    "seeds": [],
                    "example": f["example"],
                    "repro": f["repro"],
                    "suite": f["suite"],
                },
            )
            e["last_seen"] = f["date"]
            e["count"] += 1
            if f["seed"] not in e["seeds"]:
                e["seeds"] = (e["seeds"] + [f["seed"]])[-5:]
            night.append({**f, "id": key, "new": new})
    return {"version": 1, "entries": dict(sorted(entries.items())), "last_batches": batches}, night


def report(night: list[dict], batches: list[dict]) -> str:
    """The night's findings for triage, new signatures first, in Markdown."""
    by_id: dict[str, dict] = {}
    for f in night:
        by_id.setdefault(f["id"], f)
    lost = [b for b in batches if b["status"] != "ok"]
    new = [f for f in by_id.values() if f["new"]]
    lines = [
        "# Nightly fuzz",
        "",
        f"{len(batches)} batches ({len(lost)} stopped), {len(by_id)} distinct signatures, "
        f"{len(new)} new.",
        "",
    ]
    if lost:
        lines += ["Stopped batches:", ""]
        lines += [
            f"- `{b['suite']}` seed {b['seed']}: {b['status']} after {b['elapsed']} s, "
            f"peak {b['peak_rss_mb']} MB"
            for b in lost
        ]
        lines.append("")
    for title, group in (
        ("New", new),
        ("Seen before", [f for f in by_id.values() if not f["new"]]),
    ):
        if not group:
            continue
        lines += [f"## {title}", ""]
        for f in sorted(group, key=lambda f: f["sig"]):
            lines += [
                f"- `{f['id']}` {' | '.join(f['sig'])} (seed {f['seed']})",
                f"  repro: `python3 python/tools/sverify_dev/fuzz_nightly.py repro "
                f"fuzz-ledger.json {f['id']}`",
            ]
        lines.append("")
    return "\n".join(lines)


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = parser.add_subparsers(dest="cmd", required=True)
    b = sub.add_parser("batch", help="run one batch")
    b.add_argument("suite")
    b.add_argument("--seed", type=int, required=True)
    b.add_argument("--seconds", type=float, default=1200)
    b.add_argument("--out", type=Path, required=True)
    b.add_argument("--timeout", type=float, help="wall-time limit (default seconds * 1.5 + 300)")
    b.add_argument("--rss-mb", type=int, default=7168, help="memory limit of the batch's tree")
    m = sub.add_parser("merge", help="fold batch directories into the ledger; print the report")
    m.add_argument("--ledger", type=Path, required=True, help="read if it exists, then written")
    m.add_argument("--report", type=Path, required=True)
    m.add_argument("dirs", type=Path, nargs="*")
    r = sub.add_parser("repro", help="the command that reproduces a ledger entry")
    r.add_argument("ledger", type=Path)
    r.add_argument("id")
    args = parser.parse_args(argv)

    if args.cmd == "batch":
        timeout = args.timeout or args.seconds * 1.5 + 300
        print(
            json.dumps(batch(args.suite, args.seed, args.seconds, args.out, timeout, args.rss_mb))
        )
    elif args.cmd == "merge":
        old = json.loads(args.ledger.read_text()) if args.ledger.exists() else {}
        dirs = sorted({p.parent for d in args.dirs for p in d.rglob("batch.json")})
        new, night = merge(old, dirs)
        args.ledger.write_text(json.dumps(new, indent=1) + "\n")
        args.report.write_text(report(night, new["last_batches"]) + "\n")
        print(args.report.read_text())
    else:
        entry = json.loads(args.ledger.read_text())["entries"][args.id]
        if "{file}" in entry["repro"]:
            path = Path(f"fuzz-{args.id}.json").resolve()
            path.write_text(json.dumps(entry["example"], indent=1))
            print(entry["repro"].format(file=path))
        else:
            print(entry["repro"])


if __name__ == "__main__":
    main()
