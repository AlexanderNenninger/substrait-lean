"""The docs name what exists (#1448): every relative link of `docs/*.md` resolves, and no page,
skill or README names the old place of the engine facts."""

import re
from pathlib import Path

import pytest

from _repo import ROOT, needs_repo

pytestmark = needs_repo

DOCS = sorted((ROOT / "docs").glob("*.md"))

_LINK = re.compile(r"\]\((?!https?:|mailto:|#)([^)#\s]+)(#[^)\s]*)?\)")
_FENCE = re.compile(r"^```.*?^```", re.DOTALL | re.MULTILINE)


def _links(page: Path) -> list[tuple[str, str]]:
    text = _FENCE.sub("", page.read_text(encoding="utf-8"))
    return [(m.group(1), m.group(2) or "") for m in _LINK.finditer(text)]


def _slug(heading: str) -> str:
    """GitHub's anchor of a heading: lower case, punctuation dropped, spaces to hyphens."""
    text = re.sub(r"`", "", heading.strip().lower())
    return re.sub(r"\s", "-", re.sub(r"[^\w\s-]", "", text))


def _anchors(page: Path) -> set[str]:
    text = _FENCE.sub("", page.read_text(encoding="utf-8"))
    headings = {_slug(m.group(1)) for m in re.finditer(r"^#{1,6}\s+(.*)$", text, re.MULTILINE)}
    return headings | set(re.findall(r'<a id="([^"]+)">', text))


@pytest.mark.parametrize("page", DOCS, ids=lambda p: p.name)
def test_every_relative_link_of_a_page_resolves(page: Path):
    broken = [target for target, _ in _links(page) if not (page.parent / target).resolve().exists()]
    assert not broken, f"{page.name}: {broken}"


@pytest.mark.parametrize("page", DOCS, ids=lambda p: p.name)
def test_every_anchor_into_another_page_of_the_docs_exists(page: Path):
    broken = []
    for target, anchor in _links(page):
        dest = (page.parent / target).resolve()
        if (
            anchor
            and dest.suffix == ".md"
            and dest.parent == page.parent
            and anchor[1:] not in _anchors(dest)
        ):
            broken.append(f"{target}{anchor}")
    assert not broken, f"{page.name}: {broken}"


#: Where the facts were before #1189: `engines/<engine>/facts/` holds them now.
_OLD_FACTS = re.compile(r"characterization/(<engine>|\*/facts)")


def test_no_page_names_the_old_place_of_the_engine_facts():
    files = [
        *DOCS,
        *(ROOT / ".claude" / "skills").rglob("*.md"),
        *(ROOT / ".claude" / "skills").rglob("*.py"),
        ROOT / "README.md",
        ROOT / "CLAUDE.md",
        ROOT / "python" / "great-docs.yml",
    ]
    named = [
        f"{f.relative_to(ROOT)}:{n}"
        for f in files
        for n, line in enumerate(f.read_text().splitlines(), 1)
        if _OLD_FACTS.search(line)
    ]
    assert not named, named


#: Pages that keep Lean names: the reference pages (#1448) and the records for contributors
#: (`docs/README.md`). `nested-values.md` describes the model's Lean constructors; whether it is a
#: reference page is the maintainer's call.
_KEEP_LEAN_NAMES = {
    "trusted-base", "reference-semantics", "engine-profiles", "float-bounds", "optimizations",
    "proved-theorems", "nested-values", "core-semantics", "decisions", "ledger", "proofs",
    "realizability", "coverage-targets", "layers", "teaching", "build-performance",
    "how-this-is-built",
}  # fmt: skip
_LEAN_NAME = re.compile(r"\b(Rel|Profile|Engine|Expr)\.(?!lean)[A-Za-z]|_sound\b")


@pytest.mark.parametrize(
    "page", [p for p in DOCS if p.stem not in _KEEP_LEAN_NAMES], ids=lambda p: p.name
)
def test_a_user_page_names_no_lean_theorem(page: Path):
    """The checker's own output, quoted as it prints (`proved by Rel.polars_sound`), is not a name
    the page introduces."""
    named = [
        f"{n}: {line.strip()[:70]}"
        for n, line in enumerate(page.read_text(encoding="utf-8").splitlines(), 1)
        if _LEAN_NAME.search(line) and "proved by" not in line
    ]
    assert not named, f"{page.name}: {named}"
