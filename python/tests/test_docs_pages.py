"""The docs site's generated pages (`scripts/docs_pages.py`, run by `poe docs`):
every ledger entry has its anchor, and every link between entries resolves."""

import importlib.util
import json
import re
import sys
from pathlib import Path

import pytest


def _facts():
    """`sverify_dev.facts`, which needs jsonschema: the repository's tests
    import it where they use it (the wheel's tests skip those)."""
    from sverify_dev import facts

    return facts


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "python" / "scripts" / "docs_pages.py"

#: The Wheels workflow runs these tests against the installed wheel, with only
#: `python/tests` copied out: there the ledgers and the script are not here.
pytestmark = pytest.mark.skipif(not SCRIPT.is_file(), reason="the repository is not here")


@pytest.fixture(scope="module")
def pages(tmp_path_factory):
    spec = importlib.util.spec_from_file_location("docs_pages", SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules["docs_pages"] = module
    spec.loader.exec_module(module)
    out = tmp_path_factory.mktemp("site")
    module.write(out)
    return {p.relative_to(out).as_posix(): p.read_text() for p in out.rglob("*.*")}


def _ids(pattern: str) -> set[str]:
    return {json.loads(p.read_text())["id"] for p in ROOT.glob(pattern)}


def _page(name: str) -> str:
    """A section page's name on the site: Great Docs drops the number."""
    return re.sub(r"^\d+-", "", name)


def test_every_entry_has_an_anchor(pages):
    text = "\n".join(pages.values())
    anchors = set(re.findall(r"\{#([A-Za-z0-9_.-]+)\}", text))
    assert _ids("upstream/bugs/*.json") <= anchors
    assert {f["id"] for f in _facts().load().values()} <= anchors


def test_links_between_pages_resolve(pages):
    names = {_page(Path(k).name): v for k, v in pages.items() if k.startswith("ledgers/")}
    for name, text in names.items():
        for page, anchor in re.findall(r"\]\(([a-z-]+\.md)#([A-Za-z0-9_.-]+)\)", text):
            assert page in names, (name, page)
            assert f"{{#{anchor}}}" in names[page], (name, page, anchor)


def test_links_between_sections_resolve(pages):
    """A link from one page to another the site has names a page that is there:
    `name.md` in its own section, `../section/name.md` in another."""
    have = {f"{Path(k).parent}/{_page(Path(k).name)}" for k in pages}
    for key, text in pages.items():
        section = str(Path(key).parent)
        for target in re.findall(r"\]\((\.\./[a-z-]+/[a-z-]+\.md|[a-z-]+\.md)(?:#[^)]*)?\)", text):
            page = target[3:] if target.startswith("../") else f"{section}/{target}"
            assert page in have, (key, target)


def test_no_relative_links_to_the_repository(pages):
    """Links to other files of the repository point at GitHub: the site has
    only these pages."""
    for name, text in pages.items():
        for target in re.findall(r"\]\(([^)\s]+)\)", text):
            if re.match(r"^[a-z]+:|^#|^<", target):
                continue
            assert re.match(r"^(\.\./[a-z-]+/)?[a-z-]+\.md(#|$)", target), (name, target)


def test_the_docs_pages_are_on_the_site(pages):
    """Each page of `DOC_SECTIONS` is rendered with GitHub's anchors, so the
    links of `docs/` (`core-semantics.md#d13-choosing-the-route`) land."""
    module = sys.modules["docs_pages"]
    for section, entries in module.DOC_SECTIONS.items():
        for n, (path, title, _) in enumerate(entries, start=1):
            page = pages[f"{section}/{n:02d}-{Path(path).stem}.md"]
            assert page.startswith(f'---\ntitle: "{title}"'), path
            assert "from: markdown+gfm_auto_identifiers" in page, path


def test_the_map_lists_every_page_once():
    """`docs/README.md` maps every page of `docs/` and every notebook to its
    kind, once (#751)."""
    text = (ROOT / "docs" / "README.md").read_text()
    targets = re.findall(r"\]\(([^)#\s]+)", text)
    pages = sorted(ROOT.glob("docs/*.md")) + sorted(ROOT.glob("notebooks/0*.py"))
    for page in pages:
        if page.name == "README.md":
            continue
        rel = page.relative_to(ROOT / "docs") if page.parent.name == "docs" else None
        link = rel.as_posix() if rel else f"../{page.relative_to(ROOT).as_posix()}"
        rows = [
            line for line in text.splitlines() if line.startswith("| [") and f"]({link})" in line
        ]
        assert len(rows) == 1, (link, len(rows))
    for target in targets:
        if not re.match(r"^[a-z]+:", target):
            assert (ROOT / "docs" / target).resolve().exists(), target


def test_the_examples_page_is_getting_started(pages):
    page = pages["examples/examples.md"]
    assert page.startswith('---\ntitle: "Getting started"')
    assert "## 8. Substrait's own semantics" in page


def test_the_index_has_one_short_row_per_entry(pages):
    """The index's table is HTML with a plain one-line summary per entry, so
    no entry's Markdown (an unbalanced backtick, a `|`) can break it."""
    index = pages["ledgers/index.qmd"]
    rows = re.findall(r"^<tr><td><a href=\"[^\"]+#([^\"]+)\">", index, re.M)
    ids = _ids("upstream/bugs/*.json") | {f["id"] for f in _facts().load().values()}
    assert sorted(rows) == sorted(ids)
    for cell in re.findall(r"<td>([^<]*)</td>", index):
        assert len(cell) <= 200, cell
        assert "`" not in cell, cell


def test_pipe_tables_are_well_formed(pages):
    """Every row of a Markdown table has its header's columns and balanced
    code spans."""
    for name, text in pages.items():
        width = None
        for line in text.splitlines():
            if not line.startswith("|"):
                width = None
                continue
            cells = re.split(r"(?<!\\)\|", line.strip())[1:-1]
            width = width or len(cells)
            assert len(cells) == width, (name, line[:120])
            assert all(c.count("`") % 2 == 0 for c in cells), (name, line[:120])
