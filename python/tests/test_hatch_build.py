"""The build hook refuses platforms without a wheel instead of building for hours (#1485)."""

import importlib.util
import sys
from pathlib import Path

import pytest

from _repo import ROOT, needs_repo

pytestmark = needs_repo


@pytest.fixture(scope="module")
def hook():
    pytest.importorskip("hatchling")
    spec = importlib.util.spec_from_file_location("hatch_build", ROOT / "python" / "hatch_build.py")
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


@pytest.mark.parametrize(
    ("plat", "machine"),
    [("linux", "x86_64"), ("linux", "aarch64"), ("darwin", "arm64")],
)
def test_the_platforms_with_a_wheel_build(hook, plat, machine):
    assert hook.no_wheel_message(plat, machine) is None


@pytest.mark.parametrize(
    ("plat", "machine"), [("win32", "AMD64"), ("darwin", "x86_64"), ("linux", "riscv64")]
)
def test_the_others_get_a_message_naming_the_way_out(hook, plat, machine):
    message = hook.no_wheel_message(plat, machine)
    assert message is not None
    assert plat in message and "SVERIFY_BUILD_FROM_SOURCE=1" in message and "elan" in message


def _initialize(hook, monkeypatch, version, plat, machine, env=None):
    monkeypatch.setattr(sys, "platform", plat)
    monkeypatch.setattr(hook.platform, "machine", lambda: machine)
    for k in ("SVERIFY_BUILD_FROM_SOURCE", "SVERIFY_PREBUILT_CHECKER", "SVERIFY_PREBUILT_CHECK"):
        monkeypatch.delenv(k, raising=False)
    if env:
        monkeypatch.setenv(*env)
    here = str(Path(__file__).parent)
    h = hook.LakeBuildHook(here, {}, None, None, here, "wheel")
    h.initialize(version, {"force_include": {}})


def test_a_wheel_build_stops_before_lake_on_windows(hook, monkeypatch):
    with pytest.raises(RuntimeError, match="no wheel for win32"):
        _initialize(hook, monkeypatch, "standard", "win32", "AMD64")


def test_the_variable_asks_for_the_build(hook, monkeypatch):
    # Past the refusal, the Windows build then fails on the tag, not the message.
    with pytest.raises(RuntimeError, match="not supported on win32"):
        _initialize(
            hook, monkeypatch, "standard", "win32", "AMD64", ("SVERIFY_BUILD_FROM_SOURCE", "1")
        )


def test_an_editable_install_is_not_refused(hook, monkeypatch):
    with pytest.raises(RuntimeError, match="not supported on win32"):
        _initialize(hook, monkeypatch, "editable", "win32", "AMD64")
