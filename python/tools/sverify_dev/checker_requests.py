"""The requests the checker-speed guard replays (docs/build-performance.md).

Maintainer tooling (`sverify_dev`): not in the wheel.

Records every checker request a probe of the catalogue makes
(`sverify_dev.catalogue.probe_all`), times each with the given checker
(fastest of three), and keeps those that take at least `--min-ms`: the
requests where a slower checker shows. `scripts/checker_speed.py` replays them
against main's checker in CI's `checker` job. Run it again when the catalogue
or the request format changes.

    uv run python -m sverify_dev.checker_requests --checker .lake/build/bin/substrait-check
"""

from __future__ import annotations

import argparse
import gzip
import json
import os
import subprocess
import time
from pathlib import Path
from typing import Any

from sverify import _checker
from sverify_dev import catalogue as cat

ROOT = Path(__file__).resolve().parents[3]
OUT = ROOT / "tests" / "checker-speed" / "requests.jsonl.gz"


def record() -> list[dict[str, Any]]:
    """Every request of a catalogue probe, once each, with its query's id."""
    seen: set[tuple[tuple[str, ...], str]] = set()
    out: list[dict[str, Any]] = []
    current = {"id": ""}
    ask = _checker._Checker.ask

    def recording(self: Any, flags: tuple[str, ...], stdin: str) -> tuple[int, str, str]:
        if (tuple(flags), stdin) not in seen:
            seen.add((tuple(flags), stdin))
            out.append({"id": current["id"], "flags": list(flags), "stdin": stdin})
        return ask(self, flags, stdin)

    probe = cat.probe

    def probing(con: Any, q: cat.Query, schemas: dict[str, Any]) -> dict[str, Any]:
        current["id"] = q.id
        return probe(con, q, schemas)

    _checker._Checker.ask = recording  # type: ignore[method-assign]
    cat.probe = probing  # type: ignore[assignment]
    try:
        cat.probe_all(cat.load_queries(), cat.load_schemas())
    finally:
        _checker._Checker.ask = ask  # type: ignore[method-assign]
        cat.probe = probe  # type: ignore[assignment]
    return out


def fastest(checker: str, reqs: list[dict[str, Any]], rounds: int = 3) -> list[float]:
    """Each request's fastest time in seconds, through one `--serve` process."""
    p = subprocess.Popen([checker, "--serve"], stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    assert p.stdin is not None and p.stdout is not None
    times = [float("inf")] * len(reqs)
    for _ in range(rounds):
        for i, r in enumerate(reqs):
            data = r["stdin"].encode()
            t0 = time.perf_counter()
            p.stdin.write(f"{' '.join(r['flags']) or '-'} {len(data)}\n".encode() + data)
            p.stdin.flush()
            _, m, k = map(int, p.stdout.readline().split())
            p.stdout.read(m + k)
            times[i] = min(times[i], time.perf_counter() - t0)
    p.kill()
    p.wait()
    return times


def write(path: Path, reqs: list[dict[str, Any]]) -> None:
    """The requests as gzipped JSON lines, the same bytes for the same requests."""
    path.parent.mkdir(parents=True, exist_ok=True)
    data = "".join(json.dumps(r, sort_keys=True) + "\n" for r in reqs).encode()
    with (
        open(path, "wb") as raw,
        gzip.GzipFile(fileobj=raw, mode="wb", compresslevel=9, mtime=0) as f,
    ):
        f.write(data)


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument(
        "--checker", required=True, help="the substrait-check to time the requests with"
    )
    ap.add_argument("--min-ms", type=float, default=5.0)
    ap.add_argument("--out", type=Path, default=OUT)
    a = ap.parse_args(argv)
    os.environ["SVERIFY_CACHE"] = "off"
    os.environ["SVERIFY_CHECKER"] = str(Path(a.checker).resolve())
    reqs = record()
    times = fastest(a.checker, reqs)
    kept = [r for r, t in zip(reqs, times, strict=True) if t * 1000 >= a.min_ms]
    write(a.out, kept)
    print(f"{len(kept)} of {len(reqs)} requests take at least {a.min_ms:g} ms; written to {a.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
