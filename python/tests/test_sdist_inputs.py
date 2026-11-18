"""Every file a Lean source reads with `include_str` is in the sdist (#1485).

The wheel is built from the sdist, which carries the Lean project under `lean/`
through `[tool.hatch.build.targets.sdist.force-include]`. A file that table
leaves out makes the wheel's `lake build` fail, on every pull request and the
nightly, though a checkout builds.
"""

import re
import subprocess
import tomllib
from pathlib import Path

from _repo import ROOT, needs_repo

pytestmark = needs_repo

INCLUDE = re.compile(r'^[^\n]*?\binclude_str\s+"([^"]+)"', re.MULTILINE)


def _force_include() -> dict[Path, Path]:
    cfg = tomllib.loads((ROOT / "python" / "pyproject.toml").read_text())
    table = cfg["tool"]["hatch"]["build"]["targets"]["sdist"]["force-include"]
    return {(ROOT / "python" / src).resolve(): Path(dst) for src, dst in table.items()}


def _lean_files() -> list[Path]:
    out = subprocess.run(
        ["git", "ls-files", "*.lean"], cwd=ROOT, capture_output=True, text=True, check=True
    ).stdout
    return [ROOT / line for line in out.splitlines()]


def _includes() -> list[tuple[Path, Path]]:
    found = []
    for lean in _lean_files():
        for line in lean.read_text().splitlines():
            if line.lstrip().startswith("--"):
                continue
            if m := INCLUDE.match(line):
                found.append((lean, (lean.parent / m.group(1)).resolve()))
    return found


def test_the_lean_sources_do_read_a_file() -> None:
    # The scan finds something, so the test below is not vacuous.
    assert _includes()


def test_every_include_str_file_is_in_the_sdist() -> None:
    table = _force_include()
    missing = []
    for lean, target in _includes():
        covered = any(target == src or src in target.parents for src in table)
        if not covered:
            missing.append(
                f"{lean.relative_to(ROOT)} reads {target.relative_to(ROOT)}, "
                "which the sdist's force-include table lacks"
            )
    assert not missing, "\n".join(missing)


def test_the_sdist_keeps_the_file_where_lean_looks_for_it() -> None:
    # In the sdist the project sits under `lean/`: a file maps to `lean/<same path>`.
    for src, dst in _force_include().items():
        assert dst == Path("lean") / src.relative_to(ROOT), f"{src} maps to {dst}"
