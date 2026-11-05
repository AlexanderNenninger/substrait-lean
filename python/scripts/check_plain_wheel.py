"""Check an install of sverify without extras (`pip install sverify`).

The Wheels workflow runs it against the built wheel, in an environment with
nothing else: no optional package may be installed, `import sverify` must
not need one, a node over an in-memory source refreshes on DuckDB, and the
`sverify` command checks a file. An extra imported at the top of a module
fails here before it breaks a plain install.

    python scripts/check_plain_wheel.py [--import-budget SECONDS]
"""

from __future__ import annotations

import argparse
import importlib.util
import statistics
import subprocess
import sys
import tempfile
import textwrap
from pathlib import Path

#: The optional packages of the extras (and of extras to come); none may be
#: installed for this check to mean anything.
OPTIONAL = (
    "datafusion",
    "polars",
    "pyspark",
    "deltalake",
    "pyiceberg",
    "hypothesis",
    "pytest",
    "opentelemetry",
    "openlineage",
)

PIPELINE = textwrap.dedent(
    """
    import pyarrow as pa
    import sverify as sv
    from sverify.io import StaticSource

    t = StaticSource(pa.table({"a": [1, 5]}), name="t")


    @sv.transform(requires={"t": [sv.unique("a")]}, ensures=[sv.unique("a")])
    def big(t):
        return t.filter(t.a > 2)


    node = big(t)
    """
)


def import_seconds(runs: int = 5) -> float:
    """The median wall time of `import sverify` in a fresh interpreter."""
    code = "import time; t = time.perf_counter(); import sverify; print(time.perf_counter() - t)"
    times = [
        float(
            subprocess.run(
                [sys.executable, "-c", code], capture_output=True, text=True, check=True
            ).stdout
        )
        for _ in range(runs)
    ]
    return statistics.median(times)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--import-budget",
        type=float,
        default=5.0,
        help="most seconds `import sverify` may take (median of 5)",
    )
    args = parser.parse_args()

    installed = [m for m in OPTIONAL if importlib.util.find_spec(m) is not None]
    assert not installed, f"optional packages are installed: {installed}"

    import pyarrow as pa

    import sverify as sv
    from sverify.io import StaticSource

    loaded = [m for m in OPTIONAL if m in sys.modules]
    assert not loaded, f"import sverify imported {loaded}"

    # The core engine: a node over an in-memory source, refreshed from a change.
    t = StaticSource(pa.table({"a": [1, 5]}), name="t")

    @sv.transform()
    def big(t):
        return t.filter(t.a > 2)

    node = big(t)
    node.refresh()
    changes = getattr(sv.io, "Changes", None) or sv.Changes
    t.apply(changes(inserts=[(7,)]))
    node.refresh()
    rows = sorted(r["a"] for r in node.to_arrow().to_pylist())
    assert rows == [5, 7], rows

    # The command line on a file of the plain install.
    with tempfile.TemporaryDirectory() as d:
        path = Path(d) / "pipeline.py"
        path.write_text(PIPELINE)
        out = subprocess.run(
            [sys.executable, "-m", "sverify.cli", "check", str(path)],
            capture_output=True,
            text=True,
        )
        assert out.returncode == 0, (
            f"sverify check exited {out.returncode}:\n{out.stdout}{out.stderr}"
        )
        assert "proved" in out.stdout, out.stdout

    took = import_seconds()
    print(f"import sverify: {took * 1000:.0f} ms (median of 5; budget {args.import_budget:g} s)")
    assert took <= args.import_budget, f"import sverify took {took:.2f} s"
    print("plain install: ok")
    return 0


if __name__ == "__main__":
    sys.exit(main())
