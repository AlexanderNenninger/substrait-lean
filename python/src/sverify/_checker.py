"""Running `substrait-check`: where it is, the protocol it speaks, one
long-lived `--serve` process for every request, and the integer codes its
answers write doubles in.

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release.
"""

from __future__ import annotations

import atexit
import ctypes
import functools
import json
import math
import os
import subprocess
import sys
import threading
import time
import warnings
from collections.abc import Callable
from fractions import Fraction
from pathlib import Path

from sverify import _proof_cache, _stages
from sverify._meta import PROTOCOL
from sverify._unsupported import SverifyError, UnsupportedError

#: Where the constructs Lean's model does not cover yet are tracked: the exit
#: of a checker refusal that names none of its own.
COVERAGE_ISSUES = (
    "https://github.com/AlexanderNenninger/substrait-lean/issues?q=is%3Aopen+label%3Acoverage"
)


def checker_refusal(mode: str, err: str) -> UnsupportedError:
    """A plan the checker refuses (`mode`, its message `err`), with its exit
    (`sverify.engine.checker_failed` adds the stale-build check)."""
    msg = err.strip().removeprefix("error: ") or "(no message)"
    return UnsupportedError(
        f"substrait-check {mode} refuses the plan: {msg}. Lean's model does not cover it "
        f"yet: rewrite the step, or find its issue among the open coverage issues "
        f"({COVERAGE_ISSUES})"
    )


class CheckerVersionError(SverifyError, RuntimeError):
    """The `substrait-check` binary speaks another protocol than this sverify:
    a stale build of the checker, or a checker newer than the package."""

    code = "checker_version"


_REBUILD = (
    "rebuild it with `uv sync` (an editable install) or `lake build substrait-check`, "
    "or reinstall sverify"
)


@functools.cache
def _check_protocol(path: str) -> None:
    """Ask the checker at `path` for its protocol, once per process."""
    try:
        out = subprocess.run(
            [path, "--version"], capture_output=True, text=True, timeout=60
        ).stdout.split()
    except OSError as e:
        raise FileNotFoundError(f"cannot run the checker at {path}: {e}") from e
    if out[:2] != ["substrait-check", "protocol"] or len(out) != 3 or not out[2].isdigit():
        raise CheckerVersionError(
            f"the checker at {path} is older than this sverify "
            f"(it does not report its protocol); {_REBUILD}"
        )
    found = int(out[2])
    if found < PROTOCOL:
        raise CheckerVersionError(
            f"the checker at {path} is older than this sverify (protocol {found}, "
            f"sverify needs {PROTOCOL}); {_REBUILD}"
        )
    if found > PROTOCOL:
        raise CheckerVersionError(
            f"the checker at {path} is newer than this sverify (protocol {found}, "
            f"sverify speaks {PROTOCOL}); upgrade sverify, or build the checker "
            "from the same commit"
        )


def checker_env() -> str | None:
    """`$SVERIFY_CHECKER`, else the deprecated `$SVERIFY_CHECK` with a
    `DeprecationWarning`, else None."""
    if env := os.environ.get("SVERIFY_CHECKER"):
        return env
    if env := os.environ.get("SVERIFY_CHECK"):
        warnings.warn(
            "SVERIFY_CHECK is deprecated; set SVERIFY_CHECKER", DeprecationWarning, stacklevel=3
        )
        return env
    return None


def checker_path() -> Path:
    """`$SVERIFY_CHECKER` if set, else the checker an installed engine
    profile from outside names (`sverify.profiles`), else the
    `substrait-check` the wheel ships with (a symlink to the lake build in
    an editable install). The first call for a path checks that the checker
    speaks this sverify's protocol
    (`CheckerVersionError` if not). `SVERIFY_CHECK`, its name before 1.0, is
    read with a `DeprecationWarning`."""
    path = _checker_file()
    _check_protocol(str(path))
    return path


def _checker_file() -> Path:
    """`checker_path` without the protocol check: the cache's answers were
    given by a checker of this protocol (`sverify._proof_cache`), so a hit
    needs no process."""
    if env := checker_env():
        return Path(env)
    from sverify import profiles

    # A profile from outside ships a checker over the built-in profiles and its own.
    if plugged := profiles.checker():
        return plugged
    path = Path(__file__).parent / "_bin" / "substrait-check"
    if not path.exists():
        raise FileNotFoundError(f"{path} is missing; reinstall sverify or set SVERIFY_CHECKER")
    return path


class CheckerMemoryError(SverifyError, MemoryError):
    """A checker request went over the checker's memory cap
    (`SVERIFY_CHECKER_MEMORY_MB`) and the checker was stopped (#1074)."""

    code = "checker_memory"


def memory_cap_mb() -> int:
    """The checker's memory cap in MB: `$SVERIFY_CHECKER_MEMORY_MB`, else
    4096. 0 turns the cap off."""
    return int(os.environ.get("SVERIFY_CHECKER_MEMORY_MB", "4096"))


def _rss_linux(pid: int) -> int | None:
    try:
        with open(f"/proc/{pid}/statm", "rb") as f:
            return int(f.read().split()[1]) * os.sysconf("SC_PAGE_SIZE")
    except (OSError, ValueError, IndexError):
        return None


def _rss_macos() -> Callable[[int], int | None] | None:
    """The physical footprint (what jetsam counts) of a process, through
    libproc's `proc_pid_rusage` (`rusage_info_v0`)."""
    try:
        lib = ctypes.CDLL("/usr/lib/libproc.dylib")
    except OSError:
        return None
    usage = (ctypes.c_uint64 * 12)()  # 16 bytes of UUID, then 10 counters

    def rss(pid: int) -> int | None:
        if lib.proc_pid_rusage(pid, 0, ctypes.byref(usage)) != 0:
            return None
        return int(usage[2 + 7])  # ri_phys_footprint

    return rss


#: The memory a process uses, in bytes, where this platform tells (Linux,
#: macOS); None elsewhere, and the cap is off.
_RSS: Callable[[int], int | None] | None = (
    _rss_linux if sys.platform.startswith("linux")
    else _rss_macos() if sys.platform == "darwin"
    else None
)  # fmt: skip


class _Checker:
    """One `substrait-check --serve` process, started on first use and
    reused by every request of the Python process (#182).

    A request interrupted before its answer is read (the CLI's time budget
    raises `BudgetExceeded`, a notebook's interrupt raises
    `KeyboardInterrupt`) kills the process: its answer would otherwise be
    read as the next request's. The next request starts a new one.

    A watchdog thread samples the process's memory while a request runs
    longer than a tenth of a second, and kills it past `memory_cap_mb`: the
    request raises `CheckerMemoryError`, and the next one starts a new
    process (#1074). A runaway evaluation fails its one request and leaves
    the machine alone."""

    def __init__(self) -> None:
        self.lock = threading.Lock()
        self.proc: subprocess.Popen[bytes] | None = None
        self.path: str | None = None
        self.busy = threading.Event()
        self.over: int | None = None
        self.watchdog: threading.Thread | None = None

    def ask(self, flags: tuple[str, ...], stdin: str) -> tuple[int, str, str]:
        path = str(checker_path())
        flag = " ".join(flags) or "-"
        data = stdin.encode()
        with self.lock:
            if self.proc is None or self.proc.poll() is not None or self.path != path:
                self.close()
                self.proc = subprocess.Popen(
                    [path, "--serve"], stdin=subprocess.PIPE, stdout=subprocess.PIPE
                )
                self.path = path
            assert self.proc.stdin is not None and self.proc.stdout is not None
            cap = memory_cap_mb()
            if cap > 0 and _RSS is not None and self.watchdog is None:
                self.watchdog = threading.Thread(target=self._watch, daemon=True)
                self.watchdog.start()
            self.over = None
            try:
                self.busy.set()
                self.proc.stdin.write(f"{flag} {len(data)}\n".encode() + data)
                self.proc.stdin.flush()
                header = self.proc.stdout.readline()
                if not header:
                    raise RuntimeError("substrait-check --serve exited")
                code, m, k = map(int, header.split())
                out, err = self.proc.stdout.read(m), self.proc.stdout.read(k)
                if len(out) != m or len(err) != k:
                    raise RuntimeError("substrait-check --serve exited mid-answer")
            except BaseException as e:
                self.busy.clear()
                self.close()
                if self.over is not None and not isinstance(e, CheckerMemoryError):
                    raise CheckerMemoryError(
                        f"substrait-check used {self.over >> 20} MB on one request, over its "
                        f"cap of {cap} MB, and was stopped (#1074). Set SVERIFY_CHECKER_MEMORY_MB "
                        "to raise the cap (0 turns it off)"
                    ) from e
                raise
            self.busy.clear()
        return code, out.decode(), err.decode()

    def _watch(self) -> None:
        """Kill the process when a running request takes it past the cap."""
        assert _RSS is not None
        while True:
            self.busy.wait()
            time.sleep(0.1)
            proc, cap = self.proc, memory_cap_mb() << 20
            if not self.busy.is_set() or proc is None or cap <= 0:
                continue
            rss = _RSS(proc.pid)
            if rss is not None and rss > cap and self.busy.is_set():
                self.over = rss
                proc.kill()

    def close(self) -> None:
        if self.proc is not None:
            self.proc.kill()
            self.proc.wait()
            # Close the pipes too, or the interpreter warns at exit
            # (ResourceWarning: unclosed file).
            for pipe in (self.proc.stdin, self.proc.stdout):
                if pipe is not None:
                    pipe.close()
            self.proc = None


_CHECKER = _Checker()
atexit.register(_CHECKER.close)


@functools.lru_cache(maxsize=8192)
def _run_checker(path: str, flags: tuple[str, ...], stdin: str) -> tuple[int, str, str]:
    if (answer := _proof_cache.get(path, flags, stdin)) is not None:
        _stages.hit("disk")
        return answer
    with _stages.stage("checker", within=("counterexamples",)):
        answer = _CHECKER.ask(flags, stdin)
    _proof_cache.put(path, flags, stdin, answer)
    return answer


def run_checker(flags: tuple[str, ...], stdin: str) -> tuple[int, str, str]:
    """`substrait-check <flags>` on `stdin`: exit code, stdout, stderr.

    Requests go to one long-lived `substrait-check --serve` process (a process
    start costs ~20 ms, most of it Lean's module initialization; a request
    ~0.04 ms) and are memoized: the checker is a pure function of its input.
    The answers that prove or write a plan are also kept on disk
    (`sverify._proof_cache`), so the next process does not prove an
    unchanged transform again."""
    path = str(_checker_file())
    hits = _run_checker.cache_info().hits
    answer = _run_checker(path, flags, stdin)
    if _run_checker.cache_info().hits > hits:
        _stages.hit("memo")
    return answer


# Doubles, timestamps and dates are integer codes in the Lean model
# (SubstraitLean/Float.lean). A double with magnitude m = |x| * 2^1074 has
# code ±(2m + 1), and zero (-0.0 too) has code 0, which orders codes like SQL
# engines order doubles (-inf < ... < 0.0 < ... < +inf < NaN, one NaN).
# Timestamps are microseconds, dates days.
MAX_MAG = (2**53 - 1) * 2**2045
INF_MAG, NAN_MAG = MAX_MAG + 1, MAX_MAG + 2


@functools.cache
def observations() -> dict[str, list[dict]]:
    """Each engine profile's observation rows (`--options`, "observations"):
    `{"group", "option", "row": {"shim", "evidence", ...}}`. Empty when no
    checker answers, so callers fall back to the core's choice."""
    try:
        out = subprocess.run(
            [str(checker_path()), "--options"],
            capture_output=True,
            text=True,
            check=True,
            timeout=60,
        ).stdout
        found = json.loads(out).get("observations")
    except (OSError, subprocess.SubprocessError, ValueError, SverifyError):
        found = None
    return found if isinstance(found, dict) else {}


def decode_double(code: int) -> float:
    """The double of a code (`FloatCode.toFloat`): zero is `0`, NaN the one NaN."""
    if code == 0:
        return 0.0
    sign = -1.0 if code < 0 else 1.0
    mag = (abs(code) - 1) // 2
    if mag >= NAN_MAG:
        return math.nan
    if mag == INF_MAG:
        return sign * math.inf
    return sign * float(Fraction(mag, 2**1074))
