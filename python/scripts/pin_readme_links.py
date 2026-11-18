"""Point `python/README.md`'s links at a release's tag, for the PyPI page.

PyPI shows the README as it was built. Its links to the repository's docs say
`blob/main/` or `tree/main/`, and main moves on, so a user of an older release
follows them into docs for behaviour they don't have. The release's version
bump pins them to the tag; the merge back into main unpins them:

    python scripts/pin_readme_links.py 0.9.0            # blob/main -> blob/v0.9.0
    python scripts/pin_readme_links.py 0.9.0 --unpin    # blob/v0.9.0 -> blob/main

Only links into this repository change. The molab links read the `published`
branch, which `publish_notebooks.py` keeps at the release.
"""

from __future__ import annotations

import argparse
from pathlib import Path

REPO = "https://github.com/AlexanderNenninger/substrait-lean"
README = Path(__file__).resolve().parents[1] / "README.md"
KINDS = ("blob", "tree")


def pin(text: str, version: str, *, unpin: bool = False) -> str:
    """`text` with the repository's `blob/main` and `tree/main` links on the
    tag `v<version>`, or back on main when `unpin`."""
    old, new = ("v" + version, "main") if unpin else ("main", "v" + version)
    for kind in KINDS:
        text = text.replace(f"{REPO}/{kind}/{old}/", f"{REPO}/{kind}/{new}/")
    return text


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("version", help="the release's version, without the v")
    ap.add_argument("--unpin", action="store_true", help="point the links back at main")
    ap.add_argument("--readme", type=Path, default=README)
    args = ap.parse_args()
    args.readme.write_text(pin(args.readme.read_text(), args.version, unpin=args.unpin))


if __name__ == "__main__":
    main()
