"""`scripts/check_packages.py`, the Wheels workflow's install checks (#1189, #183)."""

import importlib.util
import tomllib
from pathlib import Path

from _repo import needs_repo

pytestmark = needs_repo

PYTHON = Path(__file__).parent.parent


def test_every_extra_is_checked_alone_or_with_its_engine():
    """A new extra in pyproject goes into `EXTRAS` (checked alone by the
    `extras` job) unless it installs an engine (the `packages` job's
    combinations) or is `all`."""
    path = PYTHON / "scripts" / "check_packages.py"
    spec = importlib.util.spec_from_file_location("check_packages", path)
    assert spec is not None and spec.loader is not None
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    extras = tomllib.loads((PYTHON / "pyproject.toml").read_text())["project"][
        "optional-dependencies"
    ]
    engines = {e for e, reqs in extras.items() if any(r.startswith(f"sverify-{e}") for r in reqs)}
    assert set(extras) - engines - {"all"} == set(mod.EXTRAS)
