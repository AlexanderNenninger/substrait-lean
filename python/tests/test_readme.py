"""The Python examples of the READMEs and of the docs pages run.

Each file's ```python blocks are run in order, in one namespace and in a
fresh working directory, so an example may build on the ones before it. A
block that fails, or a printed line that its `# ...` comment does not
show, fails the test; "..." in a comment elides part of the line.
A block that cannot run says why in its first line, `# skip: a reason`;
the test prints each reason (`pytest -s`). A page with a Python block
that is in neither `READMES` nor `EXEMPT` fails `test_every_page_is_listed`.
The tour's notebooks are checked by `poe notebooks`.
"""

import contextlib
import io
import re
from pathlib import Path

import pytest

from _repo import needs_repo

ROOT = Path(__file__).resolve().parents[2]
READMES = [
    ROOT / "README.md",
    ROOT / "python" / "README.md",
    ROOT / "docs" / "tasks.md",
    ROOT / "docs" / "getting-started.md",
    ROOT / "docs" / "how-it-works.md",
    ROOT / "docs" / "core-semantics.md",
    ROOT / "docs" / "float-bounds.md",
    ROOT / "docs" / "report.md",
    ROOT / "dbt" / "README.md",
    *sorted((ROOT / "docs" / "theorems").glob("*.md")),
]
# Pages whose Python blocks are not examples of the public API.
EXEMPT = {
    "CHANGELOG.md": "the release notes quote old versions of the API",
    "dbt/API-NOTES.md": "notes on the API for contributors: fragments with their own setup",
}
FENCE = r"^```python\n(# skip: ([^\n]+)\n)?(.*?)^```"


def python_blocks(text: str) -> list[str]:
    """The ```python blocks that run, in order: those with no skip reason."""
    return [body for _, reason, body in re.findall(FENCE, text, re.S | re.M) if not reason]


def skipped_blocks(text: str) -> list[str]:
    """The reasons of the ```python blocks that carry one."""
    return [reason for _, reason, _ in re.findall(FENCE, text, re.S | re.M) if reason]


def shown_output(block: str) -> list[str]:
    """The comment lines after a `print(...)`: what the README says it prints."""
    out, after_print = [], False
    for line in block.splitlines():
        if line.startswith("print(") or line.startswith("    print("):
            after_print = True
        elif after_print and line.startswith("# "):
            out.append(line[2:].split("  ←")[0].rstrip())
        elif after_print and not line.startswith("#"):
            after_print = False
    return out


def run_blocks(path: Path, text: str) -> None:
    """Run the ```python blocks of `text` in order, in one namespace, checking
    each printed line against the block's `# ...` comments."""
    namespace: dict = {"__name__": "__readme__"}
    for k, block in enumerate(python_blocks(text)):
        printed = io.StringIO()
        with contextlib.redirect_stdout(printed):
            exec(compile(block, f"{path.name} block {k + 1}", "exec"), namespace)
        lines = [line.rstrip() for line in printed.getvalue().splitlines()]
        for expected in shown_output(block):
            expected = expected.removesuffix("...").rstrip()  # "..." elides the rest
            if not expected:
                continue
            head, _, tail = expected.partition("...")  # "..." inside elides a part too
            assert any(line.startswith(head) and tail in line for line in lines), (
                f"{path.name} block {k + 1}: no printed line starts with {expected!r}; "
                f"printed:\n{printed.getvalue()}"
            )


@pytest.mark.parametrize("readme", READMES, ids=lambda p: str(p.relative_to(ROOT)))
def test_readme_examples_run(readme, tmp_path, monkeypatch):
    # The Wheels workflow runs these tests against the installed wheel, with
    # only `python/tests` copied out: there the READMEs are not here.
    if not readme.is_file():
        pytest.skip(f"{readme.relative_to(ROOT)} of the repository is not here")
    monkeypatch.chdir(tmp_path)
    run_blocks(readme, readme.read_text())
    for reason in skipped_blocks(readme.read_text()):
        print(f"{readme.relative_to(ROOT)}: block skipped: {reason}")


@needs_repo
def test_every_page_is_listed():
    """A page with a Python block is run here, or says why it is not."""
    listed = {p.relative_to(ROOT).as_posix() for p in READMES} | set(EXEMPT)
    pages = [
        *ROOT.glob("*.md"),
        *ROOT.glob("python/README.md"),
        *ROOT.glob("docs/*.md"),
        *ROOT.glob("dbt/*.md"),
        *ROOT.glob("templates/pipelines/**/*.md"),
    ]
    missing = sorted(
        rel
        for p in pages
        if (rel := p.relative_to(ROOT).as_posix()) not in listed
        and "templates/pipelines/.claude" not in rel
        and re.search(r"^```python", p.read_text(), re.M)
    )
    assert not missing, f"pages with a Python block that no test runs: {missing}"
