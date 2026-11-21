"""Build `substrait-check` with lake and ship it inside the wheel.

The wheel is tagged `py3-none-<platform>`: the Python code is pure, the binary
is not. A regular wheel gets a stripped copy in `sverify/_bin/`; an editable
install gets a symlink to `.lake/build/bin/substrait-check`, so a later
`lake build` takes effect without reinstalling.

The Lean project is the repository root, or `lean/` in an unpacked sdist.
A wheel's build checks every generated entry's proof (`-Kcheck_generated=true`,
`engines/Sverify/Engines/Generated.lean`), so no wheel ships an unchecked table; an
editable install builds with the checkout's current setting.

`SVERIFY_PREBUILT_CHECKER=<path>` makes an editable install link that binary
and skip lake (CI builds the checker once per run and shares it).

PyPI carries wheels for Linux (x86_64, aarch64) and macOS on Apple silicon. On
any other platform `pip install sverify` falls back to the sdist, and building
that needs elan and a full `lake build`: it stops with a message instead,
unless `SVERIFY_BUILD_FROM_SOURCE=1` asks for the build (#1485).
"""

from __future__ import annotations

import os
import platform
import shutil
import subprocess
import sys
from pathlib import Path

from hatchling.builders.hooks.plugin.interface import BuildHookInterface

# Windows runs `.exe` files only. A Windows wheel is not on PyPI yet
# (`WHEEL_PLATFORMS`): it builds with SVERIFY_BUILD_FROM_SOURCE=1 (#183).
TARGET = "substrait-check"
BINARY = TARGET + (".exe" if sys.platform == "win32" else "")

# The (sys.platform, machine) pairs that have a wheel on PyPI.
WHEEL_PLATFORMS = {("linux", "x86_64"), ("linux", "aarch64"), ("darwin", "arm64")}


def no_wheel_message(plat: str, machine: str) -> str | None:
    """Why a build on this platform is refused, or None when it has a wheel."""
    if (plat, machine.lower()) in WHEEL_PLATFORMS:
        return None
    return (
        f"sverify has no wheel for {plat} on {machine}: PyPI carries Linux (x86_64, aarch64) "
        "and macOS on Apple silicon. Use one of those (WSL2 on Windows, or a Linux container), "
        "or build from source with SVERIFY_BUILD_FROM_SOURCE=1, which needs elan "
        "(https://github.com/leanprover/elan) and a full `lake build` of the Lean project."
    )


def platform_tag() -> str:
    machine = platform.machine().lower()
    if sys.platform == "darwin":
        # Lean's linker records no real minimum macOS version (`minos 99.0`),
        # so use the oldest one each architecture's toolchain supports.
        return "macosx_11_0_arm64" if machine == "arm64" else "macosx_10_15_x86_64"
    if sys.platform == "linux":
        # `auditwheel repair` turns this into a manylinux tag in CI.
        return f"linux_{machine}"
    if sys.platform == "win32" and machine in ("amd64", "x86_64"):
        return "win_amd64"
    raise RuntimeError(f"sverify wheels are not supported on {sys.platform}")


class LakeBuildHook(BuildHookInterface):
    def initialize(self, version: str, build_data: dict) -> None:
        if (
            version != "editable"
            and not os.environ.get("SVERIFY_BUILD_FROM_SOURCE")
            and (message := no_wheel_message(sys.platform, platform.machine()))
        ):
            raise RuntimeError(message)
        build_data["pure_python"] = False
        build_data["tag"] = f"py3-none-{platform_tag()}"
        prebuilt = os.environ.get("SVERIFY_PREBUILT_CHECKER")
        if version == "editable" and prebuilt:
            self._link(Path(prebuilt).resolve())
            return
        repo = Path(self.root) / "lean"
        if not repo.is_dir():
            repo = Path(self.root).parent
        lake = shutil.which("lake") or str(Path.home() / ".elan" / "bin" / "lake")
        if not Path(lake).exists():
            raise RuntimeError("building sverify needs `lake` (install elan) on PATH")
        # `-R` applies the option even where a previous build set it otherwise.
        check = [] if version == "editable" else ["-R", "-Kcheck_generated=true"]
        subprocess.run([lake, *check, "build", TARGET], cwd=repo, check=True)

        built = repo / ".lake" / "build" / "bin" / BINARY
        if version == "editable":
            self._link(built)
        else:
            staged = Path(self.root) / "build" / BINARY
            staged.parent.mkdir(exist_ok=True)
            shutil.copy2(built, staged)
            if sys.platform != "win32":  # Windows has no `strip`
                subprocess.run(["strip", str(staged)], check=True)
            build_data["force_include"][str(staged)] = f"sverify/_bin/{BINARY}"

    def _link(self, target: Path) -> None:
        """Point the editable install's `_bin/substrait-check` at `target`."""
        if not target.is_file():
            raise RuntimeError(f"{target} is missing: build substrait-check first")
        link = Path(self.root) / "src" / "sverify" / "_bin" / BINARY
        link.parent.mkdir(exist_ok=True)
        link.unlink(missing_ok=True)
        if sys.platform == "win32":  # a symlink needs developer mode there
            shutil.copy2(target, link)
        else:
            link.symlink_to(target)
