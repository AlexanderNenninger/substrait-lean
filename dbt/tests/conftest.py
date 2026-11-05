"""Fixtures: dbt projects compiled in process with dbt's own runner."""

from __future__ import annotations

import shutil
import textwrap
from pathlib import Path

import pytest

EXAMPLE = Path(__file__).parents[1] / "examples" / "shop"


def dbt(project: Path, *args: str) -> None:
    """Run a dbt command in `project`, whose profiles.yml is beside it."""
    runner = pytest.importorskip("dbt.cli.main").dbtRunner()
    res = runner.invoke(
        [*args, "--project-dir", str(project), "--profiles-dir", str(project), "--quiet"]
    )
    if not res.success:
        raise RuntimeError(f"dbt {' '.join(args)} failed in {project}: {res.exception}")


@pytest.fixture(scope="session")
def shop(tmp_path_factory: pytest.TempPathFactory) -> Path:
    """The sample project (examples/shop), compiled in a copy."""
    root = tmp_path_factory.mktemp("shop") / "shop"
    shutil.copytree(
        EXAMPLE,
        root,
        ignore=shutil.ignore_patterns("target", "logs", "*.duckdb", "*.wal", "selectors.yml"),
    )
    # dbt-duckdb reads a relative path from the working directory.
    profiles = root / "profiles.yml"
    profiles.write_text(
        profiles.read_text().replace("path: shop.duckdb", f"path: {root / 'shop.duckdb'}")
    )
    if not (root / "dbt_packages").is_dir():
        dbt(root, "deps")
    dbt(root, "compile")
    return root


PROFILE = """\
tiny:
  target: dev
  outputs:
    dev: {{type: duckdb, path: "{path}", threads: 1}}
"""


@pytest.fixture
def make_project(tmp_path: Path):
    """A project from `{path: text}` files, compiled; no packages."""

    def make(files: dict[str, str]) -> Path:
        root = tmp_path / "tiny"
        files = {
            "dbt_project.yml": "name: tiny\nversion: '1.0'\nconfig-version: 2\nprofile: tiny\n",
            "profiles.yml": PROFILE.format(path=root / "tiny.duckdb"),
            **files,
        }
        for path, text in files.items():
            (root / path).parent.mkdir(parents=True, exist_ok=True)
            (root / path).write_text(textwrap.dedent(text))
        dbt(root, "compile")
        return root

    return make
