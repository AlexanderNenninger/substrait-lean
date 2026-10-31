"""The notebooks as `scripts/publish_notebooks.py` writes them for the
`published` branch: they install the release from PyPI, not the checkout."""

import importlib.util
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "python" / "scripts" / "publish_notebooks.py"
NOTEBOOKS = ROOT / "notebooks"

#: The Wheels workflow runs these tests against the installed wheel, with only
#: `python/tests` copied out: there the notebooks and the script are not here.
pytestmark = pytest.mark.skipif(
    not (SCRIPT.is_file() and NOTEBOOKS.is_dir()), reason="the repository is not here"
)


@pytest.fixture(scope="module")
def script():
    spec = importlib.util.spec_from_file_location("publish_notebooks", SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules["publish_notebooks"] = module
    spec.loader.exec_module(module)
    return module


def test_every_notebook_installs_the_release(script, tmp_path):
    written = script.publish("0.2.0", NOTEBOOKS, tmp_path)
    assert len(written) == len(list(NOTEBOOKS.glob("[0-9]*.py")))
    for nb in written:
        meta = script.header(nb.read_text())
        assert "uv" not in meta.get("tool", {}), nb.name
        [dep] = [d for d in meta["dependencies"] if d.startswith("sverify")]
        assert dep.endswith("==0.2.0"), (nb.name, dep)
        assert "](../" not in nb.read_text(), nb.name
    assert (tmp_path / "README.md").read_text().startswith("# Published notebooks")


def test_extras_are_kept_and_only_the_header_changes(script):
    nb = """# /// script
# requires-python = ">=3.12"
# dependencies = [
#     "marimo",
#     "sverify[datafusion,polars]",
# ]
#
# [tool.uv.sources]
# sverify = { path = "../python", editable = true }
# ///

"sverify"  # not the header
mo.md("[catalogue](../catalogue/INDEX.md), [chapter 5](05_keys.py)")
"""
    assert (
        script.rewrite(nb, "0.2.0")
        == f"""# /// script
# requires-python = ">=3.12"
# dependencies = [
#     "marimo",
#     "sverify[datafusion,polars]==0.2.0",
# ]
# ///

"sverify"  # not the header
mo.md("[catalogue]({script.REPO}/blob/v0.2.0/catalogue/INDEX.md), [chapter 5](05_keys.py)")
"""
    )


def test_other_sources_are_kept(script):
    nb = """# /// script
# dependencies = ["sverify", "other"]
#
# [tool.uv.sources]
# sverify = { path = "../python", editable = true }
# other = { git = "https://example.com/other" }
# ///
"""
    with pytest.raises(ValueError, match="one sverify dependency"):
        script.rewrite(nb, "0.2.0")  # inline lists are not rewritten
    nb = nb.replace('["sverify", "other"]', '[\n#     "sverify",\n#     "other",\n# ]')
    meta = script.header(script.rewrite(nb, "0.2.0"))
    assert meta["dependencies"] == ["sverify==0.2.0", "other"]
    assert meta["tool"]["uv"]["sources"] == {"other": {"git": "https://example.com/other"}}
