"""Rewrite the tour notebooks to install this run's wheels, as molab installs
the published ones (#1189).

Each notebook's PEP 723 header is rewritten as `publish_notebooks.py`
rewrites it for a release (the `../python` source dropped, `sverify[...]`
pinned to the wheels' version), and points uv at the wheel folders
(`[tool.uv] find-links`), which uv prefers to PyPI for the same version. Every
sverify distribution must have a wheel there, so none comes from PyPI. The
Wheels workflow then runs each notebook in its own sandbox
(`uvx marimo export html --sandbox`), extras and engine packages included.

    python scripts/notebooks_from_wheels.py --wheels DIR [DIR ...] NOTEBOOK ...
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from publish_notebooks import _HEADER, header, rewrite  # noqa: E402

#: sverify's distributions, released at one version; each needs a wheel.
DISTRIBUTIONS = ("sverify", "sverify_duckdb", "sverify_polars", "sverify_spark", "sverify_dbt")
_WHEEL = re.compile(r"^(sverify(?:_[a-z]+)?)-([^-]+)-")


def wheels(dirs: list[Path]) -> dict[str, str]:
    """Each sverify distribution's version among the wheels in `dirs`."""
    found: dict[str, str] = {}
    for d in dirs:
        for w in d.glob("*.whl"):
            if m := _WHEEL.match(w.name):
                found[m[1]] = m[2]
    return found


def with_wheels(text: str, version: str, dirs: list[Path]) -> str:
    """`text` as published for `version`, resolving from `dirs` first."""
    text = rewrite(text, version)
    m = _HEADER.search(text)
    assert m is not None
    links = ", ".join(f'"{d.resolve().as_posix()}"' for d in dirs)
    body = m.group(1) + f"#\n# [tool.uv]\n# find-links = [{links}]\n"
    text = text[: m.start(1)] + body + text[m.end(1) :]
    assert header(text)["tool"]["uv"]["find-links"], text
    return text


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--wheels", nargs="+", type=Path, required=True)
    parser.add_argument("notebooks", nargs="+", type=Path)
    args = parser.parse_args(argv)
    found = wheels(args.wheels)
    missing = [d for d in DISTRIBUTIONS if d not in found]
    assert not missing, f"no wheel for {missing} in {args.wheels}"
    versions = set(found.values())
    assert len(versions) == 1, f"the wheels are at several versions: {found}"
    (version,) = versions
    for nb in args.notebooks:
        nb.write_text(with_wheels(nb.read_text(), version, args.wheels))
        print(f"{nb}: sverify {version} from {', '.join(map(str, args.wheels))}")


if __name__ == "__main__":
    main()
