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
    python3 scripts/lean_timings.py calibrate timings.jsonl  # before the build
    python3 scripts/lean_timings.py check timings.jsonl   # against the budget
    python3 scripts/lean_timings.py replay timings.jsonl --out isolated.jsonl

`calibrate` compiles `scripts/lean-calibration.lean` and records its CPU
time in the log. The budget's CPU ceilings are in units of that time, so they
hold on any runner: the same module's CPU time differs by about 2x between
CI's runner types (#1865). RSS doesn't depend on the runner and stays in MB.

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
CALIBRATION = REPO / "scripts" / "lean-calibration.lean"
# A module's ceiling is this factor over its highest measured numbers ...
FACTOR = 1.5
# ... and never below these floors, so a small module's noise fails nothing.
# CPU is in calibrations (`cpu_cal`): one is 7 to 14 s of CPU on CI's runners.
FLOOR_CPU_CAL = 3.0
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


def _cpu_model() -> str:
    try:
        for line in Path("/proc/cpuinfo").read_text().splitlines():
            if line.startswith("model name"):
                return line.split(":", 1)[1].strip()
    except OSError:
        pass
    return subprocess.run(
        ["uname", "-m"], check=False, capture_output=True, text=True
    ).stdout.strip()


def calibrate(log: Path, runs: int = 3) -> float:
    """Compile the calibration file `runs` times; record its fastest CPU time."""
    real = _real_lean()
    times = []
    for _ in range(runs):
        proc = subprocess.Popen([real, str(CALIBRATION)], stdout=subprocess.DEVNULL)
        _, status, usage = os.wait4(proc.pid, 0)
        if os.waitstatus_to_exitcode(status) != 0:
            raise SystemExit(f"lean failed on {CALIBRATION}")
        times.append(round(usage.ru_utime + usage.ru_stime, 2))
    record = {"calibration": min(times), "runs": times, "cpu_model": _cpu_model()}
    with open(log, "a") as f:
        f.write(json.dumps(record) + "\n")
    print(f"calibration: {min(times)} s of CPU (runs {times}) on {record['cpu_model']}")
    return min(times)


# --- reading the records ----------------------------------------------------


def load(paths: list[Path]) -> dict[str, dict]:
    """The last record of each module (a rebuild replaces an earlier one). A
    log with a calibration gives its records `cpu_cal`, their CPU time in
    calibrations."""
    records: dict[str, dict] = {}
    for path in paths:
        lines = [
            json.loads(line) for line in path.read_text().splitlines() if line.strip()
        ]
        cal = next((r["calibration"] for r in lines if "calibration" in r), None)
        for r in lines:
            if "module" in r:
                if cal:
                    r["cpu_cal"] = round(r["cpu_s"] / cal, 3)
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
    """Each module's highest calibrated CPU time and RSS over several
    measurements, each log divided by its own calibration (several runner
    types, so the ceiling covers the one where the module is relatively slowest)."""
    out: dict[str, dict] = {}
    for path in paths:
        records = load([path])
        if any("cpu_cal" not in r for r in records.values()):
            raise SystemExit(f"{path} has no calibration: record it with `calibrate`")
        for m, r in records.items():
            o = out.setdefault(m, {"cpu_cal": 0.0, "rss_mb": 0})
            o["cpu_cal"] = max(o["cpu_cal"], r["cpu_cal"])
            o["rss_mb"] = max(o["rss_mb"], r["rss_mb"])
    return out


def ceilings(records: dict[str, dict]) -> dict[str, dict[str, float]]:
    return {
        m: {
            "cpu_cal": round(max(FLOOR_CPU_CAL, FACTOR * r["cpu_cal"]), 1),
            "rss_mb": round(max(FLOOR_RSS_MB, FACTOR * r["rss_mb"])),
        }
        for m, r in sorted(records.items())
    }


def _shown(path: Path) -> str:
    try:
        return str(path.resolve().relative_to(REPO))
    except ValueError:
        return str(path)


def check(paths: list[Path], budget_path: Path) -> list[tuple[str, str, float, float]]:
    """The modules over their ceilings, as (module, key, value, ceiling).
    The budget is a target, not a gate: each is reported, in the job summary
    and as a warning, and the PR body explains it (docs/build-performance.md)."""
    budget = json.loads(budget_path.read_text())
    default = budget["default"]
    over = []
    records = load(paths)
    if records and any("cpu_cal" not in r for r in records.values()):
        print("lean budget: no calibration in the log, so CPU time is not checked")
    for m, r in sorted(records.items()):
        ceiling = budget["modules"].get(m, default)
        for key in ("cpu_cal", "rss_mb"):
            if key in r and key in ceiling and r[key] > ceiling[key]:
                over.append((m, key, r[key], ceiling[key]))
    print(f"lean budget: {len(records)} modules built, {len(over)} over their ceilings")
    for m, key, value, ceiling in over:
        line = f"{m}: {key} {value} over its ceiling {ceiling}"
        print(
            f"::warning title=Lean build budget::{line}"
            if os.environ.get("GITHUB_ACTIONS")
            else line
        )
    if over:
        print(
            f"A module over its ceiling: make it cheaper (docs/build-performance.md), "
            f"or raise its line in {_shown(budget_path)} and say why in the PR body."
        )
        summary = os.environ.get("GITHUB_STEP_SUMMARY")
        if summary:
            rows = [
                f"| `{m}` | {key} | {value} | {ceiling} |"
                for m, key, value, ceiling in over
            ]
            with open(summary, "a") as f:
                f.write(
                    "\n### Modules over their ceilings\n\n"
                    "| module | measure | value | ceiling |\n|---|---|---:|---:|\n"
                    + "\n".join(rows)
                    + "\n"
                )
    return over


def write_budget(paths: list[Path], budget_path: Path) -> None:
    budget = {
        "comment": "Per-module ceilings of the Lean build: 1.5x the highest measured CPU time "
        "and peak RSS, at least 3 calibrations and 1536 MB. CPU is `cpu_cal`, CPU time "
        "divided by the run's calibration (scripts/lean-calibration.lean), so it holds on "
        "any runner (docs/build-performance.md). Modules not listed get `default`.",
        "default": {"cpu_cal": 6.0, "rss_mb": 2560},
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
    s = sub.add_parser("calibrate", help="record the calibration's CPU time in a log")
    s.add_argument("log", type=Path)
    s.add_argument("--runs", type=int, default=3)
    s = sub.add_parser("report", help="tables by time and RSS, and the critical path")
    s.add_argument("logs", type=Path, nargs="+")
    s.add_argument("--top", type=int, default=25)
    s.add_argument("--key", choices=["cpu_s", "wall_s"], default="wall_s")
    s = sub.add_parser("check", help="report the modules over their ceilings")
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
    elif a.cmd == "calibrate":
        calibrate(a.log, a.runs)
    elif a.cmd == "report":
        report(a.logs, a.top, a.key)
    elif a.cmd == "check":
        check(a.logs, a.budget)
    elif a.cmd == "write-budget":
        write_budget(a.logs, a.budget)
    elif a.cmd == "replay":
        replay(a.logs, a.out, a.module)
    return 0


if __name__ == "__main__":
    sys.exit(main())
