"""A JSON-lines server on stdin and stdout, so that sverify and Ibis are
imported once per editor session.

Requests: `{"id": 1, "method": "check", "path": "...", "counterexamples": 200}`
and `{"id": 2, "method": "ping"}`. Each response is one line:
`{"id": 1, "result": {...}}` or `{"id": 1, "error": "..."}`. Whatever the
checked file prints goes to stderr, never to the protocol's stdout.
"""

from __future__ import annotations

import json
import sys
import time
import traceback


def main() -> None:
    out = sys.stdout
    sys.stdout = sys.stderr  # the checked file's prints
    t0 = time.perf_counter()
    import sverify

    from . import check

    ready = {
        "ready": True,
        "sverify": getattr(sverify, "__version__", None) or _version(),
        "import_seconds": round(time.perf_counter() - t0, 3),
    }
    out.write(json.dumps(ready) + "\n")
    out.flush()
    for line in sys.stdin:
        if not line.strip():
            continue
        req = json.loads(line)
        try:
            if req.get("method") == "check":
                result = check.check(req["path"], req.get("counterexamples"))
            elif req.get("method") == "ping":
                result = {"pong": True}
            else:
                raise ValueError(f"unknown method {req.get('method')!r}")
            resp = {"id": req.get("id"), "result": result}
        except Exception as e:  # noqa: BLE001 - the client shows it
            resp = {"id": req.get("id"), "error": f"{type(e).__name__}: {e}", "trace": traceback.format_exc()}
        out.write(json.dumps(resp, default=str) + "\n")
        out.flush()


def _version() -> str | None:
    from importlib.metadata import version

    try:
        return version("sverify")
    except Exception:  # noqa: BLE001
        return None


if __name__ == "__main__":
    main()
