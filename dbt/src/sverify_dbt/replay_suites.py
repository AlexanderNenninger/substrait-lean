"""The projects inside dbt's own pytest suites, as dbt projects (#859).

Maintainers' tooling like `sverify_dbt.replay`, which uses it: not part of
sverify-dbt's API and not in its wheel.

dbt's test suites (`dbt-tests-adapter`, and dbt-core's `tests/functional`)
define each case as a pytest class whose fixtures `models`, `seeds`,
`snapshots`, `macros`, `tests`, `analyses` and `project_config_update` are
the files of a small dbt project. `projects(root, package)` imports the test
modules under `root`, evaluates those fixtures without running pytest and
yields one project per distinct set of files: a `Base*` class and the `Test*`
class that inherits it give the same project once.

A class whose fixtures need pytest's `project` (a running warehouse) or
fail is listed in `unextracted` with the reason, not skipped silently.
"""

from __future__ import annotations

import importlib
import inspect
import json
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

import yaml

#: The fixtures that are files, and the project directory each one fills.
DIRECTORIES = {
    "models": "models",
    "seeds": "seeds",
    "snapshots": "snapshots",
    "macros": "macros",
    "tests": "tests",
    "analyses": "analyses",
    "functions": "functions",
}
_FIXTURES = (*DIRECTORIES, "project_config_update")
#: Pytest's own fixtures the project fixtures may ask for, with a stand-in.
_STAND_INS = {"unique_schema": "replay", "test_config": {}, "dbt_profile_target": {}}


@dataclass
class Case:
    """One distinct project: where it is defined and its files."""

    name: str
    """`module.Class` of the first class that defines it."""
    files: dict[str, str]
    """Path in the project to contents."""
    config: dict[str, Any]
    """What `project_config_update` adds to `dbt_project.yml`."""
    also: list[str] = field(default_factory=list)
    """The other classes with the same project."""


def _function(value: Any) -> Any:
    """The function under a pytest fixture, across pytest's versions."""
    get = getattr(value, "_get_wrapped_function", None)
    return get() if get else getattr(value, "__wrapped__", None)


def _is_fixture(value: Any) -> bool:
    return hasattr(value, "_get_wrapped_function") or hasattr(value, "_pytestfixturefunction")


def _evaluate(cls: type, name: str) -> Any:
    """The value of the class's fixture `name`, called on a fresh instance."""
    fn = _function(inspect.getattr_static(cls, name))
    params = list(inspect.signature(fn).parameters)[1:]
    missing = [p for p in params if p not in _STAND_INS]
    if missing:
        raise LookupError(f"{name} needs the pytest fixture {', '.join(missing)}")
    return fn(cls(), **{p: _STAND_INS[p] for p in params})


def _files(fixtures: dict[str, Any]) -> dict[str, str]:
    out = {}
    for kind, directory in DIRECTORIES.items():
        value = fixtures.get(kind)
        if not isinstance(value, dict):
            continue
        for name, text in value.items():
            if isinstance(text, str):
                out[f"{directory}/{name}"] = text
    return out


def _config(value: Any) -> dict[str, Any]:
    if isinstance(value, str):
        value = yaml.safe_load(value)
    return value if isinstance(value, dict) else {}


def projects(root: Path, package: str) -> tuple[list[Case], dict[str, str]]:
    """The distinct projects of the test modules under `root` (the directory
    of the importable package `package`), and the classes it could not read."""
    cases: dict[str, Case] = {}
    unextracted: dict[str, str] = {}
    for path in sorted(root.rglob("*.py")):
        if path.name.startswith("__"):
            continue
        module = f"{package}." + ".".join(path.relative_to(root).with_suffix("").parts)
        try:
            mod = importlib.import_module(module)
        except Exception as e:  # noqa: BLE001 - a module that does not import is recorded
            unextracted[module] = f"{type(e).__name__}: {str(e).splitlines()[0][:100]}"
            continue
        for name, cls in sorted(vars(mod).items()):
            if not (inspect.isclass(cls) and cls.__module__ == module):
                continue
            ours = [f for f in _FIXTURES if _is_fixture(inspect.getattr_static(cls, f, None))]
            if not set(ours) & set(DIRECTORIES):
                continue
            label = f"{module}.{name}"
            try:
                fixtures = {f: _evaluate(cls, f) for f in ours}
            except Exception as e:  # noqa: BLE001 - a fixture that does not evaluate
                unextracted[label] = f"{type(e).__name__}: {str(e).splitlines()[0][:100]}"
                continue
            files, config = _files(fixtures), _config(fixtures.get("project_config_update"))
            key = json.dumps([sorted(files.items()), config], sort_keys=True, default=str)
            if key in cases:
                cases[key].also.append(label)
            else:
                cases[key] = Case(label, files, config)
    # A `Base*` class names the project better than the `Test*` that inherits it.
    return sorted(cases.values(), key=lambda c: c.name), unextracted


def write(case: Case, project: Path, profile: str = "replay") -> None:
    """The case as a dbt project in `project`, with a DuckDB profile."""
    project.mkdir(parents=True, exist_ok=True)
    for rel, text in case.files.items():
        target = project / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)
    base = {"name": "replay", "version": "1.0", "config-version": 2, "profile": profile}
    (project / "dbt_project.yml").write_text(yaml.safe_dump({**base, **case.config}))
    (project / "profiles.yml").write_text(
        f"{profile}:\n  target: duckdb\n  outputs:\n"
        f'    duckdb: {{type: duckdb, path: "{project / "replay.duckdb"}", threads: 2}}\n'
    )
