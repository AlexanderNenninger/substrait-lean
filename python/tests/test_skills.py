"""The agent skills shipped in `sverify/skills/` run.

Every Markdown file of a skill (its `SKILL.md` and `references/`) is checked
like a README (`test_readme.py`): its ```python blocks run in order, in one
namespace and a fresh working directory, and printed lines must match their
`# ...` comments.
"""

from pathlib import Path

import pytest

import sverify
from test_readme import run_blocks

SKILLS = Path(sverify.__file__).parent / "skills"
FILES = sorted(SKILLS.glob("*/**/*.md"))


def test_skills_exist():
    names = {p.parent.name for p in SKILLS.glob("*/SKILL.md")}
    assert names == {"sverify", "sverify-pipelines", "sverify-engines"}
    for p in SKILLS.glob("*/SKILL.md"):
        head = p.read_text().split("---")[1]
        assert f"name: {p.parent.name}\n" in head and "description:" in head


@pytest.mark.parametrize("path", FILES, ids=lambda p: str(p.relative_to(SKILLS)))
def test_skill_examples_run(path, tmp_path, monkeypatch):
    text = path.read_text()
    # An unclosed fence would hide the code after it from the test.
    assert sum(line.startswith("```") for line in text.splitlines()) % 2 == 0
    monkeypatch.chdir(tmp_path)
    run_blocks(path, text)
