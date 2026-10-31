"""Rewrite the tour notebooks for a release, for the `published` branch.

In the repository each notebook's PEP 723 header installs `sverify` from the
checkout (`[tool.uv.sources] sverify = { path = "../python", editable = true }`).
molab reads notebooks straight from GitHub, so the copies on `published`
install the release from PyPI instead:

* the `[tool.uv.sources]` entry for `sverify` is dropped (the table too, if
  nothing else is left in it);
* `"sverify[extras]"` becomes `"sverify[extras]==<version>"`, keeping the extras;
* Markdown links that leave `notebooks/` (`../catalogue/INDEX.md`) point at
  the release tag on GitHub, since `published` holds only the notebooks.

    python scripts/publish_notebooks.py 0.2.0 ../notebooks /tmp/out

writes the branch's content to `/tmp/out`: the rewritten notebooks in
`notebooks/`, and a README.
"""

from __future__ import annotations

import argparse
import re
import sys
import tomllib
from pathlib import Path

REPO = "https://github.com/AlexanderNenninger/substrait-lean"

README = """\
# Published notebooks

This branch holds the tour notebooks of `sverify` {version}, as released on
PyPI, so that the molab links in the README open notebooks that match the
release. Each notebook installs `sverify=={version}` from PyPI instead of the
repository checkout.

It is written by the `publish-notebooks` job of `.github/workflows/wheels.yml`,
one commit per release; don't edit it by hand. The sources are in
[`notebooks/` at v{version}]({repo}/tree/v{version}/notebooks).
"""

_HEADER = re.compile(r"^# /// script\n(.*?)^# ///$", re.S | re.M)
_SVERIFY = re.compile(r'^(#\s+)"sverify(\[[^\]]*\])?"(,?)$', re.M)
_UP_LINK = re.compile(r"\]\(\.\./([^)\s]+)\)")


def header(text: str) -> dict:
    """The PEP 723 metadata of a notebook."""
    m = _HEADER.search(text)
    if m is None:
        raise ValueError("no `# /// script` header")
    return tomllib.loads("\n".join(line[2:] for line in m.group(1).splitlines()))


def rewrite(text: str, version: str) -> str:
    """A notebook as published for `version`."""
    m = _HEADER.search(text)
    if m is None:
        raise ValueError("no `# /// script` header")
    lines = m.group(1).splitlines(keepends=True)
    out: list[str] = []
    i = 0
    while i < len(lines):
        if lines[i].strip() == "# [tool.uv.sources]":
            entries = []
            j = i + 1
            while j < len(lines) and lines[j].strip() not in ("#", "") and "[" not in lines[j][:3]:
                entries.append(lines[j])
                j += 1
            kept = [e for e in entries if not e[1:].strip().startswith("sverify")]
            if kept:
                out += [lines[i], *kept]
            elif out and out[-1].strip() == "#":
                out.pop()  # the blank comment line before the table
            i = j
            continue
        out.append(lines[i])
        i += 1
    body, n = _SVERIFY.subn(rf'\1"sverify\2=={version}"\3', "".join(out))
    if n != 1:
        raise ValueError(f"expected one sverify dependency, found {n}")
    text = text[: m.start(1)] + body + text[m.end(1) :]
    return _UP_LINK.sub(rf"]({REPO}/blob/v{version}/\1)", text)


def publish(version: str, src: Path, out: Path) -> list[Path]:
    """Write the rewritten notebooks of `src` to `out/notebooks`, and the
    README to `out`."""
    (out / "notebooks").mkdir(parents=True, exist_ok=True)
    written = []
    for nb in sorted(src.glob("*.py")):
        text = nb.read_text()
        if not _HEADER.search(text):
            continue
        target = out / "notebooks" / nb.name
        target.write_text(rewrite(text, version))
        meta = header(target.read_text())
        assert "sverify" not in meta.get("tool", {}).get("uv", {}).get("sources", {}), nb
        written.append(target)
    (out / "README.md").write_text(README.format(version=version, repo=REPO))
    return written


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("version", help="the released version, e.g. 0.2.0")
    parser.add_argument("src", type=Path, help="the repository's notebooks/")
    parser.add_argument("out", type=Path, help="the branch's content, written here")
    args = parser.parse_args(argv)
    if not re.fullmatch(r"\d+(\.\d+)*([ab]|rc)?\d*", args.version):
        sys.exit(f"not a version: {args.version!r}")
    for path in publish(args.version, args.src, args.out):
        print(path)


if __name__ == "__main__":
    main()
