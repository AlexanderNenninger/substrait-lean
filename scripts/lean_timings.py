#!/usr/bin/env python3
"""Per-module Lean build time and memory, and the budget that guards them.

`docs/build-performance.md` has the method. In short: Lake runs `lean` from
the sysroot it finds through `LEAN_SYSROOT`, so `sysroot` makes a copy of the
toolchain's sysroot (symbolic links) whose `bin/lean` is this script. Each
module Lake compiles then runs under `os.wait4`, which gives its exact CPU
time and peak RSS, and one JSON line per module goes to `$LEAN_TIMINGS`. The
build itself is unchanged: same arguments, same outputs, same exit status.

    python3 scripts/lean_timings.py sysroot /tmp/lean-sysroot
    LEAN_SYSROOT=/tmp/lean-sysroot LEAN_TIMINGS=timings.jsonl lake build
    python3 scripts/lean_timings.py report timings.jsonl
    python3 scripts/lean_timings.py check timings.jsonl   # against the budget
    python3 scripts/lean_timings.py replay timings.jsonl --out isolated.jsonl

`replay` runs each recorded module again, one at a time, with its outputs
thrown away: the isolated numbers, free of the parallel build's contention.
Only the standard library is used, so CI runs it before any `uv` setup.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import tempfile
import time
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
BUDGET = REPO / "scripts" / "lean-budget.json"
# A module's ceiling is this factor over its measured numbers ...
FACTOR = 1.5
# ... and never below these floors, so a small module's noise fails nothing.
FLOOR_CPU_S = 30.0
FLOOR_RSS_MB = 1536


def _real_lean() -> str:
    real = os.environ.get("LEAN_TIMINGS_REAL")
    if real:
        return real
    prefix = subprocess.run(
        ["lean", "--print-prefix"], capture_output=True, text=True, check=True
    ).stdout
    return str(Path(prefix.strip()) / "bin" / "lean")


# --- the wrapper ------------------------------------------------------------


def run_lean(args: list[str]) -> int:
    """Run the real `lean` on `args`; record the module if it is a compile."""
    real = _real_lean()
    log = os.environ.get("LEAN_TIMINGS")
    if not log or "--setup" not in args:
        os.execv(real, [real, *args])
    start = time.time()
    proc = subprocess.Popen([real, *args])
    _, status, usage = os.wait4(proc.pid, 0)
    end = time.time()
    code = os.waitstatus_to_exitcode(status)
    setup = json.loads(Path(args[args.index("--setup") + 1]).read_text())
    rss = usage.ru_maxrss // (1024 if sys.platform == "darwin" else 1)  # to KB
    record = {
        "module": setup["name"],
        "imports": sorted(setup.get("importArts", {})),
        "options": setup.get("options", {}),
        "cpu_s": round(usage.ru_utime + usage.ru_stime, 2),
        "wall_s": round(end - start, 2),
        "rss_mb": rss // 1024,
        "start": round(start, 2),
        "end": round(end, 2),
        "exit": code,
        "argv": args,
        "setup": setup,
        "lean_path": os.environ.get("LEAN_PATH", ""),
    }
    with open(log, "a") as f:  # one short write per line: appends don't interleave
        f.write(json.dumps(record) + "\n")
    return code


def make_sysroot(dest: Path) -> None:
    real_root = Path(
        subprocess.run(
            ["lean", "--print-prefix"], capture_output=True, text=True, check=True
        ).stdout.strip()
    )
    dest.mkdir(parents=True, exist_ok=True)
    for entry in real_root.iterdir():
        if entry.name != "bin" and not (dest / entry.name).exists():
            (dest / entry.name).symlink_to(entry)
    (dest / "bin").mkdir(exist_ok=True)
    for exe in (real_root / "bin").iterdir():
        link = dest / "bin" / exe.name
        if exe.name != "lean" and not link.exists():
            link.symlink_to(exe)
    wrapper = dest / "bin" / "lean"
    wrapper.write_text(
        "#!/bin/sh\n"
        f"LEAN_TIMINGS_REAL={real_root / 'bin' / 'lean'} "
        f'exec {sys.executable} {Path(__file__).resolve()} run -- "$@"\n'
    )
    wrapper.chmod(0o755)
    print(dest)


# --- reading the records ----------------------------------------------------


def load(paths: list[Path]) -> dict[str, dict]:
    """The last record of each module (a rebuild replaces an earlier one)."""
    records: dict[str, dict] = {}
    for path in paths:
        for line in path.read_text().splitlines():
            if line.strip():
                r = json.loads(line)
                records[r["module"]] = r
    return records


def critical_path(records: dict[str, dict], key: str) -> tuple[float, list[str]]:
    """The longest import chain by `key`: a lower bound on a parallel build."""
    best: dict[str, tuple[float, list[str]]] = {}

    def visit(m: str) -> tuple[float, list[str]]:
        if m not in best:
            r = records[m]
            prev = max(
                (visit(i) for i in r["imports"] if i in records), default=(0.0, [])
            )
            best[m] = (prev[0] + r[key], [*prev[1], m])
        return best[m]

    sys.setrecursionlimit(10000)
    return max((visit(m) for m in records), default=(0.0, []))


def report(paths: list[Path], top: int, key: str) -> None:
    records = load(paths)
    rows = sorted(records.values(), key=lambda r: -r[key])
    total_cpu = sum(r["cpu_s"] for r in rows)
    span = max(r["end"] for r in rows) - min(r["start"] for r in rows) if rows else 0
    print(
        f"{len(rows)} modules, CPU {total_cpu:.0f} s, span {span:.0f} s, "
        f"peak RSS {max((r['rss_mb'] for r in rows), default=0)} MB\n"
    )
    print("| module | CPU s | wall s | RSS MB |\n|---|---:|---:|---:|")
    for r in rows[:top]:
        print(
            f"| {r['module']} | {r['cpu_s']:.1f} | {r['wall_s']:.1f} | {r['rss_mb']} |"
        )
    print("\nBy RSS:\n\n| module | RSS MB | CPU s |\n|---|---:|---:|")
    for r in sorted(records.values(), key=lambda r: -r["rss_mb"])[:top]:
        print(f"| {r['module']} | {r['rss_mb']} | {r['cpu_s']:.1f} |")
    length, chain = critical_path(records, key)
    print(f"\nCritical path by {key}: {length:.0f} s, {len(chain)} modules")
    for m in chain:
        print(f"  {records[m][key]:7.1f}  {m}")


# --- the budget -------------------------------------------------------------


def peaks(paths: list[Path]) -> dict[str, dict]:
    """Each module's highest CPU time and RSS over several measurements."""
    out: dict[str, dict] = {}
    for path in paths:
        for m, r in load([path]).items():
            o = out.setdefault(m, {"cpu_s": 0.0, "rss_mb": 0})
            o["cpu_s"] = max(o["cpu_s"], r["cpu_s"])
            o["rss_mb"] = max(o["rss_mb"], r["rss_mb"])
    return out


def ceilings(records: dict[str, dict]) -> dict[str, dict[str, float]]:
    return {
        m: {
            "cpu_s": round(max(FLOOR_CPU_S, FACTOR * r["cpu_s"])),
            "rss_mb": round(max(FLOOR_RSS_MB, FACTOR * r["rss_mb"])),
        }
        for m, r in sorted(records.items())
    }


def _shown(path: Path) -> str:
    try:
        return str(path.resolve().relative_to(REPO))
    except ValueError:
        return str(path)


def check(paths: list[Path], budget_path: Path) -> int:
    budget = json.loads(budget_path.read_text())
    default = budget["default"]
    over = []
    records = load(paths)
    for m, r in sorted(records.items()):
        ceiling = budget["modules"].get(m, default)
        for key in ("cpu_s", "rss_mb"):
            if r[key] > ceiling[key]:
                over.append(f"{m}: {key} {r[key]} over its ceiling {ceiling[key]}")
    print(f"lean budget: {len(records)} modules built, {len(over)} over their ceilings")
    for line in over:
        print(
            f"::error title=Lean build budget::{line}"
            if os.environ.get("GITHUB_ACTIONS")
            else line
        )
    if over:
        print(
            f"A module over its ceiling: make it cheaper (docs/build-performance.md), "
            f"or raise its line in {_shown(budget_path)} in the same PR and say why."
        )
    return 1 if over else 0


def write_budget(paths: list[Path], budget_path: Path) -> None:
    budget = {
        "comment": "Per-module ceilings of the Lean build: 1.5x the highest measured CPU time "
        "and peak RSS, at least 30 s and 1536 MB (docs/build-performance.md). "
        "Modules not listed get `default`.",
        "default": {"cpu_s": 60, "rss_mb": 2560},
        "modules": ceilings(peaks(paths)),
    }
    budget_path.write_text(json.dumps(budget, indent=1) + "\n")


# --- isolated numbers -------------------------------------------------------


def replay(paths: list[Path], out: Path, modules: list[str]) -> None:
    """Compile each recorded module again, alone, its outputs discarded."""
    records = load(paths)
    chosen = modules or sorted(records, key=lambda m: records[m]["start"])
    real = _real_lean()
    with tempfile.TemporaryDirectory() as tmp, open(out, "a") as f:
        for m in chosen:
            r = records[m]
            argv = list(r["argv"])
            for flag in ("-o", "-i", "-c", "-b"):
                if flag in argv:
                    argv[argv.index(flag) + 1] = str(Path(tmp) / f"out{flag}")
            # The setup file as it was then: a later build may have rewritten it.
            setup = Path(tmp) / "setup.json"
            setup.write_text(json.dumps(r["setup"]))
            argv[argv.index("--setup") + 1] = str(setup)
            start = time.time()
            proc = subprocess.Popen(
                [real, *argv],
                env={**os.environ, "LEAN_PATH": r["lean_path"]},
                stdout=subprocess.DEVNULL,
            )
            _, status, usage = os.wait4(proc.pid, 0)
            end = time.time()
            rss = usage.ru_maxrss // (1024 if sys.platform == "darwin" else 1)
            rec = {
                **r,
                "cpu_s": round(usage.ru_utime + usage.ru_stime, 2),
                "wall_s": round(end - start, 2),
                "rss_mb": rss // 1024,
                "start": round(start, 2),
                "end": round(end, 2),
                "exit": os.waitstatus_to_exitcode(status),
            }
            f.write(json.dumps(rec) + "\n")
            f.flush()
            print(f"{rec['wall_s']:7.1f} s {rec['rss_mb']:6d} MB  {m}", flush=True)


def main() -> int:
    if len(sys.argv) > 1 and sys.argv[1] == "run":
        return run_lean(sys.argv[3:] if sys.argv[2:3] == ["--"] else sys.argv[2:])
    p = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    sub = p.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser(
        "sysroot", help="make a sysroot whose `lean` records each module"
    )
    s.add_argument("dir", type=Path)
    s = sub.add_parser("report", help="tables by time and RSS, and the critical path")
    s.add_argument("logs", type=Path, nargs="+")
    s.add_argument("--top", type=int, default=25)
    s.add_argument("--key", choices=["cpu_s", "wall_s"], default="wall_s")
    s = sub.add_parser("check", help="fail on a module over its ceiling")
    s.add_argument("logs", type=Path, nargs="+")
    s.add_argument("--budget", type=Path, default=BUDGET)
    s = sub.add_parser("write-budget", help="write ceilings from measured records")
    s.add_argument("logs", type=Path, nargs="+")
    s.add_argument("--budget", type=Path, default=BUDGET)
    s = sub.add_parser("replay", help="compile recorded modules again, one at a time")
    s.add_argument("logs", type=Path, nargs="+")
    s.add_argument("--out", type=Path, required=True)
    s.add_argument("--module", action="append", default=[])
    a = p.parse_args()
    if a.cmd == "sysroot":
        make_sysroot(a.dir)
    elif a.cmd == "report":
        report(a.logs, a.top, a.key)
    elif a.cmd == "check":
        return check(a.logs, a.budget)
    elif a.cmd == "write-budget":
        write_budget(a.logs, a.budget)
    elif a.cmd == "replay":
        replay(a.logs, a.out, a.module)
    return 0


if __name__ == "__main__":
    sys.exit(main())
