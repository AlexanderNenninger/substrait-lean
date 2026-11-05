"""Where a check spends its time, by stage (#745, #825).

`stage("lift")` around a piece of work adds its time to that stage while
`timing()` is collecting. Stages nest: time counts for the innermost one,
so a checker call made while lifting counts as `checker`. Outside
`timing()` a stage costs one attribute read.

The stages: `lift` (an Ibis expression or SQL to a Substrait plan),
`checker` (requests `substrait-check` answers, on a cache miss),
`counterexamples` (the search for inputs that break an unproved
postcondition, with the checker's evaluations it asks for) and `plan`
(each node's route to its engine). `sverify_dev.bench` reads them.
"""

from __future__ import annotations

import functools
import time
from collections import Counter, defaultdict
from collections.abc import Callable, Iterator
from contextlib import contextmanager
from dataclasses import dataclass, field
from typing import Any, TypeVar

F = TypeVar("F", bound=Callable[..., Any])


@dataclass
class Timings:
    """Seconds and calls per stage, and the checker requests the caches
    answered (`memo`: this process's; `disk`: `sverify._proof_cache`)."""

    seconds: defaultdict[str, float] = field(default_factory=lambda: defaultdict(float))
    calls: Counter[str] = field(default_factory=Counter)
    hits: Counter[str] = field(default_factory=Counter)

    def to_json(self) -> dict:
        return {
            "seconds": {k: round(v, 4) for k, v in sorted(self.seconds.items())},
            "calls": dict(sorted(self.calls.items())),
            "hits": dict(sorted(self.hits.items())),
        }


@dataclass
class _Frame:
    name: str
    start: float
    inner: float = 0.0  # the inner stages' time


_current: Timings | None = None
_stack: list[_Frame] = []


@contextmanager
def timing() -> Iterator[Timings]:
    """Collect the stages' times within the block (not thread-safe: for one
    benchmark at a time)."""
    global _current
    outer, _current = _current, Timings()
    try:
        yield _current
    finally:
        _current = outer


@contextmanager
def stage(name: str, within: tuple[str, ...] = ()) -> Iterator[None]:
    """Count the block's time, less its inner stages', for `name`; inside
    one of the stages `within`, for that stage."""
    t = _current
    if t is None or (_stack and _stack[-1].name in within):
        yield
        return
    frame = _Frame(name, time.perf_counter())
    _stack.append(frame)
    try:
        yield
    finally:
        _stack.pop()
        took = time.perf_counter() - frame.start
        t.seconds[name] += took - frame.inner
        t.calls[name] += 1
        if _stack:
            _stack[-1].inner += took


def staged(name: str) -> Callable[[F], F]:
    """A function whose calls count for stage `name`."""

    def wrap(fn: F) -> F:
        @functools.wraps(fn)
        def inner(*args: Any, **kwargs: Any) -> Any:
            with stage(name):
                return fn(*args, **kwargs)

        return inner  # type: ignore[return-value]

    return wrap


def hit(cache: str) -> None:
    """A checker request answered by `cache`."""
    if _current is not None:
        _current.hits[cache] += 1
