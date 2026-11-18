"""Set sverify's version in every place that carries it (#1606).

    python scripts/set_version.py 0.9.0.dev0

One release is nine strings: the `version` of `python/`, `dbt/` and each
`engines/<engine>/pyproject.toml`, and the `==` pins that tie them together
(`sverify==` in `dbt/` and the engines, `sverify-<engine>[run]==` in
`python/`). The release bump and the step that reopens main (a `.dev0` of the
next minor, so a build from main is never taken for a release) both run this;
`uv.lock` and `python/README.md`'s links follow as the release skill says.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
ENGINES = ("duckdb", "polars", "spark")
#: The files, and the pins each holds besides its own `version`.
PINS = {
    "python/pyproject.toml": [rf'"sverify-{e}(\[[a-z]+\])?==' for e in ENGINES],
    "dbt/pyproject.toml": ['"sverify=='],
    **{f"engines/{e}/pyproject.toml": ['"sverify=='] for e in ENGINES},
}
_VERSION = re.compile(r"[0-9]+(\.[0-9]+)*((a|b|rc)[0-9]+)?(\.dev[0-9]+)?")


def rewrite(text: str, version: str, pins: list[str]) -> str:
    """`text` with its own version and `pins` at `version`."""
    text, n = re.subn(r'(?m)^(version = ")[^"]*(")', rf"\g<1>{version}\g<2>", text, count=1)
    if n != 1:
        raise ValueError("no version line")
    for pin in pins:
        text, n = re.subn(rf'({pin})[^"]*"', rf'\g<1>{version}"', text)
        if not n:
            raise ValueError(f"no pin {pin}")
    return text


def set_version(version: str, root: Path = ROOT) -> None:
    if not _VERSION.fullmatch(version):
        sys.exit(f"not a version: {version!r}")
    for name, pins in PINS.items():
        path = root / name
        path.write_text(rewrite(path.read_text(), version, pins))


if __name__ == "__main__":
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    set_version(sys.argv[1])
