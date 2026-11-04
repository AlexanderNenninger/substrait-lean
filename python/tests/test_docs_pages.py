"""The docs site's generated pages (`scripts/docs_pages.py`, run by `poe docs`):
every ledger entry has its anchor, and every link between entries resolves."""

import importlib.util
import json
import re
import sys
from pathlib import Path

import pytest

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
    assert _ids("characterization/*/facts/*.json") <= anchors


def test_links_between_pages_resolve(pages):
    names = {_page(Path(k).name): v for k, v in pages.items() if k.startswith("ledgers/")}
    for name, text in names.items():
        for page, anchor in re.findall(r"\]\(([a-z-]+\.md)#([A-Za-z0-9_.-]+)\)", text):
            assert page in names, (name, page)
            assert f"{{#{anchor}}}" in names[page], (name, page, anchor)


def test_no_relative_links_to_the_repository(pages):
    """Links to other files of the repository point at GitHub: the site has
    only these pages."""
    for name, text in pages.items():
        for target in re.findall(r"\]\(([^)\s]+)\)", text):
            if re.match(r"^[a-z]+:|^#|^<", target):
                continue
            assert re.match(r"^[a-z-]+\.md(#|$)", target), (name, target)


def test_the_examples_page_is_docs_examples(pages):
    page = pages["examples/examples.md"]
    assert page.startswith('---\ntitle: "Examples"')
    assert "## 8. Substrait's own semantics" in page
