"""`substrait-check`'s own command line (#2239): `--help`, and the usage
errors for an unknown flag or a file it can't read."""

from __future__ import annotations

import subprocess
from pathlib import Path

import pytest

from sverify.engine import checker_path

# The flags `sverify` and its tools call the checker with: their names stay.
CALLED = [
    "--assumed", "--build", "--contract", "--delta", "--dependencies", "--eval-choices",
    "--functions", "--lift-table", "--lowering-table", "--options", "--outcomes",
    "--outcomes-duckdb-stopgap", "--profile-diff", "--raises", "--realizability", "--rows",
    "--serve", "--shard", "--transfer", "--version", "--write",
]  # fmt: skip


def run(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [str(checker_path()), *args], capture_output=True, text=True, timeout=60, check=False
    )


@pytest.mark.parametrize("flag", ["--help", "-h"])
def test_help_lists_every_flag_in_groups(flag: str) -> None:
    done = run(flag)
    assert done.returncode == 0 and done.stderr == ""
    page = done.stdout
    for group in ("Checking a plan:", "Diagnostics:", "Serving:", "Tables and coverage:"):
        assert group in page
    assert "Example:" in page
    flags = {line.split()[0] for line in page.splitlines() if line.startswith("  --")}
    assert set(CALLED) <= flags


def test_an_unknown_flag_is_a_usage_error() -> None:
    done = run("--nope")
    assert done.returncode == 2 and done.stdout == ""
    assert done.stderr.splitlines() == [
        "substrait-check: unknown option --nope",
        "Run substrait-check --help for the flags.",
    ]
    assert run("--nope", "plan.json").returncode == 2


@pytest.mark.parametrize("args", [(), ("--write",), ("--version", "plan.json"), ("a", "b", "c")])
def test_a_misused_flag_is_a_usage_error(args: tuple[str, ...]) -> None:
    done = run(*args)
    assert done.returncode == 2 and "uncaught exception" not in done.stderr


@pytest.mark.parametrize("args", [(), ("--write",)])
def test_a_missing_file_names_it(tmp_path: Path, args: tuple[str, ...]) -> None:
    missing = tmp_path / "missing.json"
    done = run(*args, str(missing))
    assert done.returncode == 2 and done.stdout == ""
    [line] = done.stderr.splitlines()
    assert line.startswith(f"substrait-check: cannot read {missing}: ")
