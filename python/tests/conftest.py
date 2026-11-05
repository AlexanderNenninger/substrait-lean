"""Backends and example counts.

Every test runs under one backend, which is also a marker: `poe test-polars`
(`pytest -m polars`) runs the Polars tests, and CI runs one job per backend.
A test's backend is its `engine` parameter (or `sv_engine`, from sverify's
pytest plugin), else its `backend` mark (on the test or as the module's
`pytestmark`), else `core`: Lean, the producers, and DuckDB as the oracle.
Tests comparing two engines with each other stay in `core`. DataFusion is an
optional extra of `sverify`, but the tests need it (it is in the `dev`
group); `test_without_datafusion.py` blocks it.

`tests/lift_backlog.json` lists the tests that wait on SQL the lift
(`sverify.sql_lift`) does not read yet: the backlog of M2 (#240), each with
the reason it waits (`python -m sverify_dev.bugs` checks it). A listed
test that fails because the lift refuses its SQL is an expected failure,
with the refusal as its reason (`pytest -rx`); one that fails otherwise
fails, and one that passes fails too, until its line is removed (strict). A
test that is not listed fails as usual, whatever refuses it.
`SVERIFY_LIFT_BACKLOG=<file> pytest …` writes the tests the lift refuses to
`<file>`, one node id per line, to start or prune the list.

Two profiles, chosen by `SVERIFY_PROFILE`: `dev` (the default, except in
CI) runs every Hypothesis test with a tenth of its examples (at least 3), for
a quick local loop; `ci` (the default when `CI` is set, and `poe test-all`)
keeps the full counts. `SVERIFY_EXAMPLES=0.25` sets the fraction itself.
Every `@settings` sets `max_examples` itself, so a Hypothesis profile would
not reach them; this scales the settings each test carries.

`slow` marks the tests `poe test` leaves out (`-m "not slow"`): the ones
that take seconds even in the `dev` profile (engine agreement on many
queries, long streams, replays), and every Spark test, which starts a JVM.
`poe test-all`, `poe qa` and CI run them.

`chaos` marks the crash-injection suite in `tests/chaos/` (`poe
test-chaos`). A run collects it only when its `-m` expression names
`chaos`, so `poe test`, `poe test-all` and CI leave it out.

`SVERIFY_SHARD=2/3` keeps the second of three shards of the selected tests,
split by a hash of the node id (CI splits `core` this way); the shards
together are the whole run.
"""

import hashlib
import json
import os
from pathlib import Path
from typing import Any

import pytest
from hypothesis import settings

from sverify.engines import ENGINES

#: Keep in step with the `test-*` poe tasks and the CI matrix.
BACKENDS = ("core", *ENGINES, "datafusion", "snowflake", "spark")

PROFILE = os.environ.get("SVERIFY_PROFILE") or ("ci" if os.environ.get("CI") else "dev")
if PROFILE not in ("dev", "ci"):
    raise ValueError(f"SVERIFY_PROFILE={PROFILE!r}: expected 'dev' or 'ci'")
SCALE = float(os.environ.get("SVERIFY_EXAMPLES") or ("1" if PROFILE == "ci" else "0.1"))


def pytest_configure(config: pytest.Config) -> None:
    config.addinivalue_line("markers", "backend(name): the backend a test runs under")
    config.addinivalue_line("markers", "slow: left out of `poe test`, run by CI and `poe test-all`")
    config.addinivalue_line("markers", "chaos: crash injection, only run by `-m chaos`")
    config._lift_refused = []  # type: ignore[attr-defined]
    for name in BACKENDS:
        config.addinivalue_line("markers", f"{name}: set from the test's backend")


def _lift_refusal(exc: BaseException | None) -> str | None:
    """The lift's refusal behind an exception (it, or what it was raised
    from), if that is what it is."""
    from sverify.plan_json import Unsupported

    seen: set[int] = set()
    while exc is not None and id(exc) not in seen:
        seen.add(id(exc))
        tb = exc.__traceback__
        while tb is not None:
            if (
                isinstance(exc, Unsupported)
                and os.path.join("sverify", "sql_lift", "") in tb.tb_frame.f_code.co_filename
            ):
                return str(exc).splitlines()[0]
            tb = tb.tb_next
        exc = exc.__cause__ or exc.__context__
    return None


#: The tests that wait on the lift (`tests/lift_backlog.json`), by node id.
BACKLOG = {
    entry["test"]
    for entry in json.loads((Path(__file__).parent / "lift_backlog.json").read_text())["tests"]
}


@pytest.hookimpl(hookwrapper=True)
def pytest_runtest_makereport(item: pytest.Item, call: pytest.CallInfo) -> Any:
    outcome = yield
    report = outcome.get_result()
    listed = item.nodeid in BACKLOG
    if report.failed and call.excinfo is not None:
        reason = _lift_refusal(call.excinfo.value)
        if reason is None:
            return
        if os.environ.get("SVERIFY_LIFT_BACKLOG"):
            item.config._lift_refused.append(item.nodeid)  # type: ignore[attr-defined]
        if listed:
            report.outcome = "skipped"
            report.wasxfail = f"#240, the lift refuses: {reason}"
    elif listed and call.when == "call" and report.passed:
        report.outcome = "failed"
        report.longrepr = (
            f"{item.nodeid} passes: the lift reads its SQL now, so remove it from "
            "tests/lift_backlog.json"
        )


def pytest_sessionfinish(session: pytest.Session) -> None:
    if path := os.environ.get("SVERIFY_LIFT_BACKLOG"):
        refused = getattr(session.config, "_lift_refused", [])
        with open(path, "a") as f:
            f.writelines(f"{n}\n" for n in refused)


def backend(item: pytest.Item) -> str:
    callspec = getattr(item, "callspec", None)
    for param in ("engine", "sv_engine"):  # `sv_engine`: sverify's pytest plugin
        if callspec is not None and param in callspec.params:
            return callspec.params[param]
    if mark := item.get_closest_marker("backend"):
        return mark.args[0]
    return "core"


def _shard(config: pytest.Config, items: list[pytest.Item]) -> None:
    """Keep the shard `SVERIFY_SHARD` names (`i/n`, 1-based) of `items`."""
    spec = os.environ.get("SVERIFY_SHARD")
    if not spec:
        return
    i, n = map(int, spec.split("/"))
    if not 1 <= i <= n:
        raise pytest.UsageError(f"SVERIFY_SHARD={spec}: expected i/n with 1 <= i <= n")

    def shard(item: pytest.Item) -> int:
        return int(hashlib.sha256(item.nodeid.encode()).hexdigest(), 16) % n + 1

    keep = [item for item in items if shard(item) == i]
    config.hook.pytest_deselected(items=[item for item in items if shard(item) != i])
    items[:] = keep


def _leave_out_chaos(config: pytest.Config, items: list[pytest.Item]) -> None:
    """Deselect the chaos suite unless `-m` names it."""
    if "chaos" in (config.option.markexpr or ""):
        return
    chaos = [item for item in items if item.get_closest_marker("chaos")]
    if chaos:
        config.hook.pytest_deselected(items=chaos)
        items[:] = [item for item in items if not item.get_closest_marker("chaos")]


def pytest_collection_modifyitems(config: pytest.Config, items: list[pytest.Item]) -> None:
    _leave_out_chaos(config, items)
    for item in items:
        name = backend(item)
        if name not in BACKENDS:
            raise pytest.UsageError(f"{item.nodeid}: unknown backend {name!r}")
        item.add_marker(name)
        if name == "spark":
            item.add_marker("slow")
    _shard(config, items)
    if SCALE == 1:
        return
    # Parametrized items share one test function: scale each once.
    tests: dict[int, Any] = {}
    for item in items:
        test = getattr(item, "obj", None)
        if hasattr(test, "hypothesis"):
            tests[id(test)] = test
    for test in tests.values():
        given = test._hypothesis_internal_use_settings  # noqa: SLF001
        test._hypothesis_internal_use_settings = settings(  # noqa: SLF001
            given, max_examples=max(min(given.max_examples, 3), round(given.max_examples * SCALE))
        )


@pytest.fixture(autouse=True)
def _polars_plans_stream(monkeypatch: pytest.MonkeyPatch) -> None:
    """Every plan the tests run on Polars runs on the streaming engine with no
    node on the in-memory engine but those `ALLOWED_FALLBACKS` lists, each
    an operation Polars 2.1.0 cannot stream (#444). A new fallback fails the
    test that meets it."""
    try:
        from sverify import polars_engine
    except ImportError:
        return
    collect = polars_engine.collect

    def checked(lf):
        try:
            found = polars_engine.disallowed_fallbacks(lf)
        except Exception:  # noqa: BLE001 - the plan's own error comes from `collect`
            found = []
        # A plan with an expression too long for Polars's plan formatter
        # cannot be inspected; `streaming="require"` refuses those.
        found = [n for n in found if n != polars_engine.UNINSPECTABLE]
        if found:
            raise AssertionError(
                "the streaming plan runs these nodes on the in-memory engine, which "
                "polars_engine.ALLOWED_FALLBACKS does not allow:\n" + "\n".join(found)
            )
        return collect(lf)

    monkeypatch.setattr(polars_engine, "collect", checked)
