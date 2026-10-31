"""The Python examples of the READMEs run.

Each README's ```python blocks are run in order, in one namespace and in a
fresh working directory, so an example may build on the ones before it. A
block that fails, or a printed line that its `# ...` comment does not
show, fails the test; "..." in a comment elides part of the line.
The tour's notebooks are checked by `poe notebooks`.
"""

import contextlib
import io
import re
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
READMES = [ROOT / "README.md", ROOT / "python" / "README.md"]


def python_blocks(text: str) -> list[str]:
    return re.findall(r"^```python\n(.*?)^```", text, re.S | re.M)


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


@pytest.mark.parametrize("readme", READMES, ids=lambda p: str(p.relative_to(ROOT)))
def test_readme_examples_run(readme, tmp_path, monkeypatch):
    monkeypatch.chdir(tmp_path)
    namespace: dict = {"__name__": "__readme__"}
    for k, block in enumerate(python_blocks(readme.read_text())):
        printed = io.StringIO()
        with contextlib.redirect_stdout(printed):
            exec(compile(block, f"{readme.name} block {k + 1}", "exec"), namespace)
        lines = [line.rstrip() for line in printed.getvalue().splitlines()]
        for expected in shown_output(block):
            expected = expected.removesuffix("...").rstrip()  # "..." elides the rest
            if not expected:
                continue
            head, _, tail = expected.partition("...")  # "..." inside elides a part too
            assert any(line.startswith(head) and tail in line for line in lines), (
                f"{readme.name} block {k + 1}: no printed line starts with {expected!r}; "
                f"printed:\n{printed.getvalue()}"
            )
