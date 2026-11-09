"""The checker-speed guard's verdict (`scripts/checker_speed.py`)."""

import gzip
import importlib.util
import json

import pytest

from _repo import ROOT, needs_repo

pytestmark = needs_repo


@pytest.fixture(scope="module")
def speed():
    spec = importlib.util.spec_from_file_location(
        "checker_speed", ROOT / "scripts" / "checker_speed.py"
    )
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _row(name, base_ms, head_ms, same=True):
    return {
        "id": name,
        "flags": ["--contract"],
        "base": base_ms / 1000,
        "head": head_ms / 1000,
        "base_answer": "0:a",
        "head_answer": "0:a" if same else "0:b",
    }


def test_noise_passes(speed):
    ok, _ = speed.verdict(
        [_row("q1", 100, 105), _row("q2", 50, 48), _row("q3", 2, 9)], 1.3, 1.1, 5.0
    )
    assert ok  # q3 is under 5 ms on the base: its ratio isn't judged


def test_a_slow_request_fails_and_is_named(speed):
    ok, lines = speed.verdict([_row("q1", 100, 101), _row("q27", 98, 552)], 1.3, 1.1, 5.0)
    assert not ok
    assert any(line.startswith("q27 --contract: 5.63x") for line in lines)


def test_a_slow_set_fails(speed):
    ok, lines = speed.verdict([_row(f"q{i}", 100, 115) for i in range(5)], 1.3, 1.1, 5.0)
    assert not ok
    assert any("over 1.1x" in line for line in lines)


def test_the_requests_file_reads(speed):
    reqs = speed.load(speed.REQUESTS)
    assert reqs and all({"id", "flags", "stdin"} <= r.keys() for r in reqs)
    with gzip.open(speed.REQUESTS, "rt") as f:
        assert json.loads(f.readline())["stdin"]
