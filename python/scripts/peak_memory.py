"""Run a command and report its wall time and peak memory (#183's Windows trial).

    uv run --with psutil python python/scripts/peak_memory.py --out m.json -- lake build

Every second it sums the resident memory of the command's process tree and
keeps the largest single process. It writes `{"seconds", "peak_tree_mb",
"peak_process_mb", "peak_process", "exit"}` to `--out` and exits with the
command's status. Unlike `/usr/bin/time`, it works on Windows.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import time

import psutil


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--out", required=True)
    ap.add_argument("command", nargs=argparse.REMAINDER)
    args = ap.parse_args()
    cmd = args.command[1:] if args.command[:1] == ["--"] else args.command
    start = time.monotonic()
    proc = subprocess.Popen(cmd)
    root = psutil.Process(proc.pid)
    tree = one = 0
    name = ""
    while proc.poll() is None:
        total = 0
        try:
            procs = [root, *root.children(recursive=True)]
        except psutil.NoSuchProcess:
            procs = []
        for p in procs:
            try:
                rss = p.memory_info().rss
            except psutil.Error:
                continue
            total += rss
            if rss > one:
                one, name = rss, p.name()
        tree = max(tree, total)
        time.sleep(1)
    result = {
        "seconds": round(time.monotonic() - start),
        "peak_tree_mb": tree >> 20,
        "peak_process_mb": one >> 20,
        "peak_process": name,
        "exit": proc.returncode,
    }
    with open(args.out, "w") as f:
        json.dump(result, f)
    print(json.dumps(result))
    return proc.returncode


if __name__ == "__main__":
    raise SystemExit(main())
