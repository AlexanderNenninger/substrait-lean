"""The projects inside dbt's pytest suites (#859, `sverify_dbt.replay_suites`):
read from a small suite written here, without dbt."""

from __future__ import annotations

import sys
from collections.abc import Iterator
from pathlib import Path

import pytest
import yaml

from sverify_dbt import replay_suites

SUITE = """
import pytest

class Base:
    @pytest.fixture(scope="class")
    def models(self):
        return {"m.sql": "select 1 as id", "schema.yml": "models: []"}

    @pytest.fixture(scope="class")
    def project_config_update(self):
        return {"vars": {"x": 1}}

class TestM(Base):
    pass

class TestNeedsProject:
    @pytest.fixture(scope="class")
    def models(self, project):
        return {}

class TestOther:
    @pytest.fixture(scope="class")
    def seeds(self):
        return {"s.csv": "id\\n1"}

    @pytest.fixture(scope="class")
    def project_config_update(self):
        return "seeds: {+quote_columns: false}"
"""


@pytest.fixture
def suite(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Iterator[Path]:
    pkg = tmp_path / "mysuite"
    pkg.mkdir()
    (pkg / "__init__.py").write_text("")
    (pkg / "test_one.py").write_text(SUITE)
    monkeypatch.syspath_prepend(str(tmp_path))
    yield pkg
    for name in [n for n in sys.modules if n.split(".")[0] == "mysuite"]:
        del sys.modules[name]


def test_a_class_and_its_subclass_are_one_project(suite: Path) -> None:
    cases, _ = replay_suites.projects(suite, "mysuite")
    by_name = {c.name: c for c in cases}
    base = by_name["mysuite.test_one.Base"]
    assert base.also == ["mysuite.test_one.TestM"]
    assert base.files == {"models/m.sql": "select 1 as id", "models/schema.yml": "models: []"}
    assert base.config == {"vars": {"x": 1}}
    assert by_name["mysuite.test_one.TestOther"].config == {"seeds": {"+quote_columns": False}}


def test_a_class_that_needs_pytests_project_is_listed_not_dropped(suite: Path) -> None:
    _, unextracted = replay_suites.projects(suite, "mysuite")
    assert unextracted == {
        "mysuite.test_one.TestNeedsProject": "LookupError: models needs the pytest fixture project"
    }


def test_write_makes_a_dbt_project(suite: Path, tmp_path: Path) -> None:
    (case,) = [
        c for c in replay_suites.projects(suite, "mysuite")[0] if c.files.get("models/m.sql")
    ]
    replay_suites.write(case, tmp_path / "p")
    assert (tmp_path / "p/models/m.sql").read_text() == "select 1 as id"
    project = yaml.safe_load((tmp_path / "p/dbt_project.yml").read_text())
    assert project["profile"] == "replay" and project["vars"] == {"x": 1}
    assert "type: duckdb" in (tmp_path / "p/profiles.yml").read_text()


@pytest.mark.parametrize(
    ("files", "config", "expected"),
    [
        ({"models/m.sql": "select 1", "models/s.yml": "models: []"}, {}, False),
        (
            {"models/s.yml": "models:\n- name: m\n  columns:\n  - {name: id, tests: [unique]}"},
            {},
            True,
        ),
        ({"models/s.yml": "models:\n- name: m\n  data_tests: [x]"}, {}, True),
        ({"tests/t.sql": "select 1 where false"}, {}, True),
        ({"checks/t.sql": "select 1 where false"}, {"test-paths": ["checks"]}, True),
        ({"tests/t.sql": "select 1 where false"}, {"test-paths": ["checks"]}, False),
        ({"models/m.sql": "select 1"}, {"data_tests": {"+severity": "warn"}}, True),
    ],
)
def test_a_project_without_tests_is_not_replayed(
    files: dict[str, str], config: dict[str, object], expected: bool
) -> None:
    assert replay_suites.Case("c", files, config).has_tests is expected
