"""The checker's answers on disk (`sverify._proof_cache`, #825) and the
long-running checker process (#182).

Each test has a cache of its own. `_new_process` drops this process's memo,
as a new `sverify check` would start without it.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import textwrap
from collections.abc import Iterator
from pathlib import Path
from typing import Any

import ibis
import pytest
from ibis import _

import sverify as sv
from sverify import _proof_cache, _stages
from sverify import engine as E
from sverify.ibis_substrait import to_substrait_json

T = ibis.table({"id": "int64", "x": "int64"}, name="t")


@pytest.fixture(autouse=True)
def cache(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Iterator[Path]:
    root = tmp_path / "cache"
    monkeypatch.setenv("SVERIFY_CACHE_DIR", str(root))
    monkeypatch.delenv("SVERIFY_CACHE", raising=False)
    _new_process()
    yield root
    _new_process()


def _new_process() -> None:
    E._run_checker.cache_clear()


def _verify(query: ibis.Table, **kw: Any) -> tuple[sv.Report, _stages.Timings]:
    with _stages.timing() as t:
        report = sv.verify(query, requires={"t": [_.x >= 0]}, ensures=[_.y >= 0], **kw)
    return report, t


def _query(k: int = 1) -> ibis.Table:
    return T.mutate(y=_.x * k)


def _entries(root: Path) -> list[Path]:
    return sorted(root.rglob("*.json"))


def test_an_unchanged_transform_is_not_proved_again(cache: Path) -> None:
    first, t1 = _verify(_query())
    assert t1.calls["checker"] >= 1 and first.proved
    assert _entries(cache)
    _new_process()
    second, t2 = _verify(_query())
    assert t2.calls["checker"] == 0
    assert t2.hits["disk"] >= 1
    assert second.proved == first.proved
    assert [c.value for c in second.ensures] == [c.value for c in first.ensures]


def test_within_a_process_the_memo_answers(cache: Path) -> None:
    _verify(_query())
    _, t = _verify(_query())
    assert t.calls["checker"] == 0 and t.hits["memo"] >= 1


def test_a_changed_plan_misses(cache: Path) -> None:
    _verify(_query(1))
    _new_process()
    report, t = _verify(_query(-1))
    assert t.calls["checker"] >= 1
    assert not report.proved


def test_a_changed_condition_misses(cache: Path) -> None:
    _verify(_query())
    _new_process()
    with _stages.timing() as t:
        report = sv.verify(_query(), requires={"t": [_.x >= 1]}, ensures=[_.y >= 1])
    assert t.calls["checker"] >= 1 and report.proved


def test_a_changed_profile_misses(cache: Path) -> None:
    _verify(_query())
    _new_process()
    report, t = _verify(_query(), semantics="polars")
    assert t.calls["checker"] >= 1
    assert report.semantics == "polars"


def test_another_version_misses(cache: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    _verify(_query())
    _new_process()
    monkeypatch.setattr(_proof_cache, "_version", lambda: "0.0.0-other")
    _, t = _verify(_query())
    assert t.calls["checker"] >= 1


def test_another_checker_build_misses(cache: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    _verify(_query())
    _new_process()
    monkeypatch.setattr(_proof_cache, "binary_hash", lambda path: "0" * 64)
    _, t = _verify(_query())
    assert t.calls["checker"] >= 1
    # Each build keeps its entries apart.
    builds = {p.name for p in (cache / "checker").iterdir()}
    assert len(builds) == 2


def test_the_binary_hash_follows_its_content(tmp_path: Path) -> None:
    f = tmp_path / "substrait-check"
    f.write_bytes(b"one build")
    a = _proof_cache.binary_hash(str(f))
    f.write_bytes(b"another build")
    os.utime(f, ns=(1, 1))
    assert _proof_cache.binary_hash(str(f)) != a


def test_one_request_never_answers_another() -> None:
    path = str(E.checker_path())
    _proof_cache.put(path, ("--contract",), '{"a": 1}', (0, "A", ""))
    assert _proof_cache.get(path, ("--contract",), '{"a": 1}') == (0, "A", "")
    assert _proof_cache.get(path, ("--contract",), '{"a": 2}') is None
    assert _proof_cache.get(path, ("--write",), '{"a": 1}') is None


def test_a_damaged_entry_is_a_miss(cache: Path) -> None:
    first, _ = _verify(_query())
    for entry in _entries(cache):
        entry.write_text('{"answer": [0, "trunc')
    _new_process()
    second, t = _verify(_query())
    assert t.calls["checker"] >= 1
    assert second.proved == first.proved


def test_evaluation_requests_are_not_kept() -> None:
    path = str(E.checker_path())
    _proof_cache.put(path, ("--eval-spec",), "{}", (0, "rows", ""))
    assert _proof_cache.get(path, ("--eval-spec",), "{}") is None


@pytest.mark.parametrize("off", ["off", "0", "false"])
def test_the_cache_can_be_turned_off(
    cache: Path, monkeypatch: pytest.MonkeyPatch, off: str
) -> None:
    monkeypatch.setenv("SVERIFY_CACHE", off)
    _verify(_query())
    assert not cache.exists()
    _new_process()
    _, t = _verify(_query())
    assert t.calls["checker"] >= 1


def test_the_default_directory(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    monkeypatch.delenv("SVERIFY_CACHE_DIR")
    monkeypatch.setenv("XDG_CACHE_HOME", str(tmp_path / "xdg"))
    assert _proof_cache.cache_dir() == tmp_path / "xdg" / "sverify"
    monkeypatch.delenv("XDG_CACHE_HOME")
    assert _proof_cache.cache_dir() == Path.home() / ".cache" / "sverify"


def test_an_unwritable_cache_is_skipped(cache: Path) -> None:
    cache.write_text("a file where the directory would be")
    report, _ = _verify(_query())
    assert report.proved


def test_processes_share_the_cache(cache: Path) -> None:
    script = textwrap.dedent(
        """
        import ibis, sverify as sv
        from ibis import _
        from sverify import _stages
        t = ibis.table({"id": "int64", "x": "int64"}, name="t")
        with _stages.timing() as s:
            r = sv.verify(t.mutate(y=_.x), requires={"t": [_.x >= 0]}, ensures=[_.y >= 0])
        print(r.proved, s.calls["checker"], s.hits["disk"])
        """
    )
    env = {**os.environ, "SVERIFY_CACHE_DIR": str(cache)}
    procs = [
        subprocess.Popen([sys.executable, "-c", script], env=env, stdout=subprocess.PIPE, text=True)
        for _ in range(4)
    ]
    outs = [p.communicate(timeout=300)[0].split() for p in procs]
    assert all(p.returncode == 0 for p in procs)
    assert all(o[0] == "True" for o in outs)
    for entry in _entries(cache):
        json.loads(entry.read_text())
    again = subprocess.run(
        [sys.executable, "-c", script], env=env, capture_output=True, text=True, check=True
    ).stdout.split()
    assert again == ["True", "0", again[2]] and int(again[2]) >= 1


class _Interrupt(BaseException):
    pass


def test_an_interrupted_request_does_not_poison_the_checker(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A request interrupted after it was sent (the CLI's alarm, Ctrl-C)
    leaves its answer in the pipe: the process is ended, so the next
    request reads its own answer."""
    monkeypatch.setenv("SVERIFY_CACHE", "off")
    a = to_substrait_json(_query(1))
    b = to_substrait_json(T.filter(_.x > 0))
    want_b = E._CHECKER.ask((), b)
    assert want_b != E._CHECKER.ask((), a)
    proc = E._CHECKER.proc
    assert proc is not None

    real = proc.stdout

    class Stdout:
        def __getattr__(self, name: str) -> object:
            return getattr(real, name)

        def readline(self) -> bytes:
            raise _Interrupt

    monkeypatch.setattr(proc, "stdout", Stdout())
    with pytest.raises(_Interrupt):
        E._CHECKER.ask((), a)
    monkeypatch.undo()
    assert E._CHECKER.proc is None
    assert proc.poll() is not None
    assert E._CHECKER.ask((), b) == want_b
    assert E._CHECKER.proc is not proc


def test_the_checker_process_is_reused() -> None:
    plan = to_substrait_json(_query())
    E._CHECKER.ask((), plan)
    proc = E._CHECKER.proc
    E._CHECKER.ask(("--write",), plan)
    assert E._CHECKER.proc is proc
