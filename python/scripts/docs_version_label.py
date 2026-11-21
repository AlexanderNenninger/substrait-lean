"""Set the version badge of the built docs site (`great-docs/_site`).

Great Docs reads the badge's text from the installed package's metadata, which
says `nightly` when the build has no release to name. The site deployed from a
`v*` tag shows that release, `v0.9.0`; any other build, from main, says it is
the development version and which one:

    python scripts/docs_version_label.py             # a build from main
    GITHUB_REF_TYPE=tag python scripts/docs_version_label.py   # a tag's build

The version is `version` in `pyproject.toml`; a tag's publish job checks that
it equals the tag.
"""

from __future__ import annotations

import html
import os
import re
import sys
import tomllib
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
#: The badge beside the site's name, and the tooltip of its logo: Great Docs
#: writes the version into either, with the date of the release on PyPI.
BADGE = re.compile(r'<span class="version-badge"[^>]*>[^<]*</span>')
TOOLTIP = re.compile(r'data-tippy-content="<code>[^<]*</code><br>[^"]*"')


def version(pyproject: Path = HERE / "pyproject.toml") -> str:
    return tomllib.loads(pyproject.read_text(encoding="utf-8"))["project"]["version"]


def label(ver: str, *, release: bool) -> tuple[str, str]:
    """The badge's text and title for `ver`, as a release or as the development version."""
    if release:
        return f"v{ver}", f"Release {ver}"
    return (
        f"{ver} (development)",
        "Development version, built from main. The latest release is on PyPI.",
    )


def badge(ver: str, *, release: bool) -> str:
    """The badge's HTML for `ver`."""
    text, title = label(ver, release=release)
    return f'<span class="version-badge" title="{html.escape(title)}">{html.escape(text)}</span>'


def relabel(site: Path, ver: str, *, release: bool) -> int:
    """Rewrite the badge of every page under `site`; the number of pages changed."""
    new = badge(ver, release=release)
    text_of, title_of = label(ver, release=release)
    tip = f'data-tippy-content="<code>{html.escape(text_of)}</code><br>{html.escape(title_of)}"'
    changed = 0
    for page in site.rglob("*.html"):
        text = page.read_text()
        out = TOOLTIP.sub(lambda _: tip, BADGE.sub(lambda _: new, text))
        if out != text:
            page.write_text(out)
            changed += 1
    return changed


def main() -> None:
    site = Path(sys.argv[1]) if len(sys.argv) > 1 else HERE / "great-docs" / "_site"
    release = os.environ.get("GITHUB_REF_TYPE") == "tag"
    n = relabel(site, version(), release=release)
    if n == 0:
        print(f"::warning::no version badge or tooltip found under {site}")
        return
    print(f"version badge set on {n} pages ({'release' if release else 'development'})")


if __name__ == "__main__":
    main()
