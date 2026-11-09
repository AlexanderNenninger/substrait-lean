#!/usr/bin/env python3
"""Compare two substrait-check binaries' speed on recorded requests.

`docs/build-performance.md` ("The checker's speed") has the method. Both
binaries answer the requests of `tests/checker-speed/requests.jsonl.gz`
through `--serve`, interleaved, request by request, for several rounds; each
request's time is its fastest round. The comparison reports, as warnings, a
request that takes at least `--min-ms` on the base and more than `--max-ratio`
times as long on the head, and the whole set taking more than `--max-total`
times as long. It never fails: the targets are for the PR body to explain.
Measured on CI runners, the same binary against itself stays within 1.12 per
request and 1.03 at the 95th percentile.

    python3 scripts/checker_speed.py BASE_BIN HEAD_BIN

Only the standard library is used, so CI runs it before any `uv` setup.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import os
import select
import subprocess
import sys
import time
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
REQUESTS = REPO / "tests" / "checker-speed" / "requests.jsonl.gz"
TIMEOUT = 120


class Serve:
    """One `substrait-check --serve` process."""

    def __init__(self, path: str) -> None:
        self.path = path
        self.start()

    def start(self) -> None:
        self.p = subprocess.Popen(
            [self.path, "--serve"], stdin=subprocess.PIPE, stdout=subprocess.PIPE
        )

    def read(self, n: int, deadline: float) -> bytes:
        assert self.p.stdout is not None
        buf = b""
        fd = self.p.stdout.fileno()
        while len(buf) < n:
            left = deadline - time.monotonic()
            if left <= 0 or not select.select([fd], [], [], left)[0]:
                raise TimeoutError
            chunk = os.read(fd, n - len(buf))
            if not chunk:
                raise RuntimeError("the checker exited")
            buf += chunk
        return buf

    def ask(self, flags: list[str], stdin: str) -> tuple[float, str]:
        """The answer's time in seconds and a digest of the answer."""
        assert self.p.stdin is not None
        data = stdin.encode()
        t0 = time.perf_counter()
        deadline = time.monotonic() + TIMEOUT
        try:
            self.p.stdin.write(f"{' '.join(flags) or '-'} {len(data)}\n".encode() + data)
            self.p.stdin.flush()
            line = b""
            while not line.endswith(b"\n"):
                line += self.read(1, deadline)
            code, m, k = map(int, line.split())
            body = self.read(m + k, deadline) if m + k else b""
        except (TimeoutError, RuntimeError, BrokenPipeError) as e:
            self.p.kill()
            self.p.wait()
            self.start()
            return time.perf_counter() - t0, f"{type(e).__name__}"
        return (
            time.perf_counter() - t0,
            f"{code}:{hashlib.sha1(body[:m]).hexdigest()[:12]}",
        )

    def close(self) -> None:
        self.p.kill()
        self.p.wait()


def load(path: Path) -> list[dict]:
    with gzip.open(path, "rt") as f:
        return [json.loads(line) for line in f if line.strip()]


def replay(base: str, head: str, reqs: list[dict], rounds: int) -> list[dict]:
    """Each request's fastest time and answer on both binaries."""
    servers = {"base": Serve(base), "head": Serve(head)}
    for s in servers.values():  # start-up and first allocation
        s.ask(reqs[0]["flags"], reqs[0]["stdin"])
    out = [{"id": r["id"], "flags": r["flags"], "base": [], "head": []} for r in reqs]
    for rnd in range(rounds):
        order = ["base", "head"] if rnd % 2 == 0 else ["head", "base"]
        for r, o in zip(reqs, out):
            for name in order:
                dt, answer = servers[name].ask(r["flags"], r["stdin"])
                o[name].append(dt)
                o[name + "_answer"] = answer
    for s in servers.values():
        s.close()
    return [{**o, "base": min(o["base"]), "head": min(o["head"])} for o in out]


def verdict(
    rows: list[dict], max_ratio: float, max_total: float, min_ms: float
) -> tuple[list[str], list[str]]:
    """What is over its target (empty: the head is within them), and the
    report's lines."""
    base_total = sum(r["base"] for r in rows)
    head_total = sum(r["head"] for r in rows)
    total = head_total / base_total if base_total else 1.0
    timed = [r for r in rows if r["base"] * 1000 >= min_ms]
    for r in timed:
        r["ratio"] = r["head"] / r["base"]
    slow = sorted(timed, key=lambda r: -r["ratio"])
    over = [r for r in slow if r["ratio"] > max_ratio]
    changed = sum(r["base_answer"] != r["head_answer"] for r in rows)
    lines = [
        (
            f"{len(rows)} requests, {len(timed)} of at least {min_ms:g} ms on the base; "
            f"total {base_total:.2f} s on the base, {head_total:.2f} s on the head ({total:.2f}x); "
            f"{changed} answers differ"
        ),
        "",
        "| request | flags | base ms | head ms | ratio |",
        "|---|---|---:|---:|---:|",
    ]
    for r in slow[:10]:
        lines.append(
            f"| {r['id']} | {' '.join(r['flags'])} | {r['base'] * 1000:.0f} | {r['head'] * 1000:.0f} | {r['ratio']:.2f} |"
        )
    warnings = []
    if total > max_total:
        warnings.append(f"The set takes {total:.2f}x as long, over {max_total}x.")
    warnings += [
        f"{r['id']} {' '.join(r['flags'])}: {r['ratio']:.2f}x, over {max_ratio}x" for r in over
    ]
    return warnings, lines + ([""] if warnings else []) + warnings


def main() -> int:
    p = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    p.add_argument("base", help="the base checker (main's)")
    p.add_argument("head", help="the checker under test")
    p.add_argument("--requests", type=Path, default=REQUESTS)
    p.add_argument("--rounds", type=int, default=5)
    p.add_argument("--max-ratio", type=float, default=1.3)
    p.add_argument("--max-total", type=float, default=1.1)
    p.add_argument("--min-ms", type=float, default=5.0)
    a = p.parse_args()
    rows = replay(a.base, a.head, load(a.requests), a.rounds)
    warnings, lines = verdict(rows, a.max_ratio, a.max_total, a.min_ms)
    print("\n".join(lines))
    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary:
        with open(summary, "a") as f:
            f.write("### The checker's speed against main\n\n" + "\n".join(lines) + "\n")
    if os.environ.get("GITHUB_ACTIONS"):
        for msg in warnings:
            print(f"::warning title=Checker speed::{msg} (docs/build-performance.md)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
