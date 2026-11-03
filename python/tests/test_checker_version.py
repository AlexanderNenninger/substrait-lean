"""The protocol check on `substrait-check` (`engine.checker_path`)."""

import re
import stat
from pathlib import Path

import pytest

from sverify import engine
from sverify.errors import CheckerVersionError


def fake_checker(tmp_path: Path, output: str) -> str:
    """A checker that prints `output` for `--version`."""
    path = tmp_path / "substrait-check"
    path.write_text(f"#!/bin/sh\nprintf '%s\\n' '{output}'\n")
    path.chmod(path.stat().st_mode | stat.S_IEXEC)
    return str(path)


def test_the_built_checker_speaks_this_protocol() -> None:
    engine.checker_path()


@pytest.mark.parametrize(
    ("output", "message"),
    [
        # A checker from before `--version` reads it as a file name.
        ("", "older than this sverify (it does not report its protocol)"),
        (f"substrait-check protocol {engine.PROTOCOL - 1}", "older than this sverify"),
        (f"substrait-check protocol {engine.PROTOCOL + 1}", "newer than this sverify"),
    ],
)
def test_another_protocol_fails_clearly(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, output: str, message: str
) -> None:
    monkeypatch.setenv("SVERIFY_CHECK", fake_checker(tmp_path, output))
    with pytest.raises(CheckerVersionError, match=re.escape(message)) as e:
        engine.checker_path()
    if "older" in message:
        assert "lake build substrait-check" in str(e.value)
