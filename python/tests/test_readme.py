"""The Python examples of the READMEs and of the docs pages run.

Each file's ```python blocks are run in order, in one namespace and in a
fresh working directory, so an example may build on the ones before it. A
block that fails, or a printed line that its `# ...` comment does not
show, fails the test; "..." in a comment elides part of the line.
A block that cannot run says why in its first line, `# skip: a reason`;
the test prints each reason (`pytest -s`). A page with a Python or bash block
that is in neither `READMES` nor `EXEMPT` fails `test_every_page_is_listed`.
The tour's notebooks are checked by `poe notebooks`.
"""

import contextlib
import io
import os
import re
import shlex
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
    ROOT / "docs" / "engines.md",
    ROOT / "docs" / "coverage-targets.md",
    ROOT / "docs" / "build-performance.md",
    ROOT / "templates" / "pipelines" / "README.md",
    ROOT / "templates" / "pipelines" / "docs" / "for-enterprise.md",
    *sorted((ROOT / "docs" / "theorems").glob("*.md")),
]
# Pages whose Python blocks are not examples of the public API.
EXEMPT = {
    "CLAUDE.md": "instructions for the agents that work on the repository",
    "CHANGELOG.md": "the release notes quote old versions of the API",
    "dbt/API-NOTES.md": "notes on the API for contributors: fragments with their own setup",
}


def _blocks(lang: str, text: str) -> list[tuple[str | None, str]]:
    """The fenced blocks of a language: (skip reason or None, dedented body).
    A fence may be indented, in a list item; its closing fence has the same indent."""
    out = []
    for m in re.finditer(rf"^( *)```{lang}\n(.*?)^\1```", text, re.S | re.M):
        indent, body = m.group(1), m.group(2)
        body = "".join(line.removeprefix(indent) for line in body.splitlines(keepends=True))
        reason = re.match(r"# skip: ([^\n]+)\n", body)
        out.append((reason.group(1) if reason else None, body[reason.end() :] if reason else body))
    return out


def python_blocks(text: str) -> list[str]:
    """The ```python blocks that run, in order: those with no skip reason."""
    return [body for reason, body in _blocks("python", text) if not reason]


def skipped_blocks(text: str) -> list[str]:
    """The reasons of the ```python blocks that carry one."""
    return [reason for reason, _ in _blocks("python", text) if reason]


def bash_blocks(text: str) -> list[str]:
    """The ```bash blocks that run: those with no skip reason."""
    return [body for reason, body in _blocks("bash", text) if not reason]


def skipped_bash(text: str) -> list[str]:
    return [reason for reason, _ in _blocks("bash", text) if reason]


def run_bash(path: Path, text: str) -> None:
    """Run the `sverify ...` lines of the ```bash blocks in process, in the
    working directory (`sverify.cli.main`, as templates/pipelines/scripts/lake.py
    does). Any other command needs a skip reason: the test cannot run it."""
    from sverify.cli import main

    for k, block in enumerate(bash_blocks(text)):
        for line in block.replace("\\\n", " ").splitlines():
            argv = shlex.split(line, comments=True)
            if not argv:
                continue
            assert argv[0] == "sverify", (
                f"{path.name} bash block {k + 1}: `{line}` is not a sverify command; "
                "give the block a first line `# skip: reason`"
            )
            try:
                code = main(argv[1:])
            except SystemExit as e:
                code = e.code
            assert code in (0, None), f"{path.name} bash block {k + 1}: `{line}` exited {code}"


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
        if os.sep == "\\":  # a path prints with Windows' separators; the comments write `/`
            lines = [line.replace("\\", "/") for line in lines]
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
    run_bash(readme, readme.read_text())
    for reason in skipped_blocks(readme.read_text()) + skipped_bash(readme.read_text()):
        print(f"{readme.relative_to(ROOT)}: block skipped: {reason}")


@needs_repo
def test_every_page_is_listed():
    """A page with a Python or bash block is run here, or says why it is not."""
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
        and re.search(r"^ *```(python|bash)", p.read_text(), re.M)
    )
    assert not missing, f"pages with a Python or bash block that no test runs: {missing}"


def test_bash_runner_runs_sverify_and_refuses_the_rest():
    run_bash(Path("x.md"), "```bash\nsverify explain may_be_false   # a code\n```\n")
    with pytest.raises(AssertionError, match="skip"):
        run_bash(Path("x.md"), "```bash\npip install sverify\n```\n")
    run_bash(Path("x.md"), "```bash\n# skip: installs\npip install sverify\n```\n")
