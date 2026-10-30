"""Build `substrait-check` with lake and ship it inside the wheel.

The wheel is tagged `py3-none-<platform>`: the Python code is pure, the binary
is not. A regular wheel gets a stripped copy in `sverify/_bin/`; an editable
install gets a symlink to `.lake/build/bin/substrait-check`, so a later
`lake build` takes effect without reinstalling.

The Lean project is the repository root, or `lean/` in an unpacked sdist.
"""

from __future__ import annotations

import platform
import shutil
import subprocess
import sys
from pathlib import Path

from hatchling.builders.hooks.plugin.interface import BuildHookInterface

BINARY = "substrait-check"


def platform_tag() -> str:
    machine = platform.machine().lower()
    if sys.platform == "darwin":
        # Lean's linker records no real minimum macOS version (`minos 99.0`),
        # so use the oldest one each architecture's toolchain supports.
        return "macosx_11_0_arm64" if machine == "arm64" else "macosx_10_15_x86_64"
    if sys.platform == "linux":
        # `auditwheel repair` turns this into a manylinux tag in CI.
        return f"linux_{machine}"
    raise RuntimeError(f"sverify wheels are not supported on {sys.platform}")


class LakeBuildHook(BuildHookInterface):
    def initialize(self, version: str, build_data: dict) -> None:
        repo = Path(self.root) / "lean"
        if not repo.is_dir():
            repo = Path(self.root).parent
        lake = shutil.which("lake") or str(Path.home() / ".elan" / "bin" / "lake")
        if not Path(lake).exists():
            raise RuntimeError("building sverify needs `lake` (install elan) on PATH")
        subprocess.run([lake, "build", BINARY], cwd=repo, check=True)

        built = repo / ".lake" / "build" / "bin" / BINARY
        if version == "editable":
            link = Path(self.root) / "src" / "sverify" / "_bin" / BINARY
            link.parent.mkdir(exist_ok=True)
            link.unlink(missing_ok=True)
            link.symlink_to(built)
        else:
            staged = Path(self.root) / "build" / BINARY
            staged.parent.mkdir(exist_ok=True)
            shutil.copy2(built, staged)
            subprocess.run(["strip", str(staged)], check=True)
            build_data["force_include"][str(staged)] = f"sverify/_bin/{BINARY}"

        build_data["pure_python"] = False
        build_data["tag"] = f"py3-none-{platform_tag()}"
