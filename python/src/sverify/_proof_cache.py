"""The checker's answers on disk, so that an unchanged transform is not
proved again by the next `verify`, `check` or `refresh` (#825).

`substrait-check` is a pure function of its request: the mode and the
JSON it reads, which holds the plans, the conditions and the profile. An
entry is keyed by a SHA-256 of that request, the checker's protocol,
sverify's version and a SHA-256 of the checker binary itself, so a change
to any of them misses. Each entry is a file, written to a temporary name
and renamed into place, so processes that share the cache read whole
entries or none; one that does not parse is a miss.

The cache lives in `SVERIFY_CACHE_DIR`, else `$XDG_CACHE_HOME/sverify`,
else `~/.cache/sverify`. `SVERIFY_CACHE=off` (or `0`, `false`, `no`)
turns it off. Each checker build gets a directory of its own; the
directories of builds unused for `KEEP_DAYS` are removed.
"""

from __future__ import annotations

import contextlib
import functools
import hashlib
import json
import os
import shutil
import tempfile
import time
from pathlib import Path

#: The checker's modes whose answers are kept: those that prove or write a
#: plan. The modes that evaluate a plan on data (`--eval-spec`,
#: `--eval-choices`, `--outcomes`) are many small requests, each asked once.
CACHED_MODES = frozenset(
    {"-", "--contract", "--delta", "--shard", "--dependencies", "--write", "--write-datafusion"}
)
#: Days a checker build's directory stays after its last write.
KEEP_DAYS = 30

_OFF = {"0", "off", "false", "no"}


def cache_dir() -> Path | None:
    """The cache's directory, or None when `SVERIFY_CACHE` turns it off."""
    if os.environ.get("SVERIFY_CACHE", "").strip().lower() in _OFF:
        return None
    if env := os.environ.get("SVERIFY_CACHE_DIR", "").strip():
        return Path(env).expanduser()
    base = os.environ.get("XDG_CACHE_HOME", "").strip()
    return (Path(base) if base else Path.home() / ".cache") / "sverify"


@functools.cache
def _binary_hash(path: str, size: int, mtime_ns: int, inode: int) -> str:
    with open(path, "rb") as f:
        return hashlib.file_digest(f, "sha256").hexdigest()


def binary_hash(path: str) -> str:
    """A SHA-256 of the checker binary at `path`, once per process and build."""
    real = os.path.realpath(path)
    st = os.stat(real)
    return _binary_hash(real, st.st_size, st.st_mtime_ns, st.st_ino)


@functools.cache
def _version() -> str:
    from sverify import __version__

    return __version__


def _build_dir(root: Path, path: str) -> Path:
    from sverify.engine import PROTOCOL

    return root / "checker" / f"{binary_hash(path)[:32]}-p{PROTOCOL}-{_version()}"


def key(path: str, flags: tuple[str, ...], stdin: str) -> str:
    """The entry's key: a SHA-256 of the request and everything its answer
    depends on."""
    from sverify.engine import PROTOCOL

    h = hashlib.sha256()
    for part in (str(PROTOCOL), _version(), binary_hash(path), " ".join(flags) or "-"):
        h.update(part.encode())
        h.update(b"\0")
    h.update(stdin.encode())
    return h.hexdigest()


def _entry(path: str, flags: tuple[str, ...], stdin: str) -> Path | None:
    if (" ".join(flags) or "-") not in CACHED_MODES:
        return None
    root = cache_dir()
    if root is None:
        return None
    k = key(path, flags, stdin)
    return _build_dir(root, path) / k[:2] / f"{k}.json"


def get(path: str, flags: tuple[str, ...], stdin: str) -> tuple[int, str, str] | None:
    """The checker's answer to the request, if the cache has it."""
    try:
        entry = _entry(path, flags, stdin)
        if entry is None:
            return None
        data = json.loads(entry.read_text())
        code, out, err = data["answer"]
        if not (isinstance(code, int) and isinstance(out, str) and isinstance(err, str)):
            return None
    except (OSError, ValueError, KeyError, TypeError):
        return None
    return code, out, err


def put(path: str, flags: tuple[str, ...], stdin: str, answer: tuple[int, str, str]) -> None:
    """Keep the checker's answer to the request. Failing to write (a
    read-only or full disk) leaves the cache as it was."""
    try:
        entry = _entry(path, flags, stdin)
        if entry is None:
            return
        entry.parent.mkdir(parents=True, exist_ok=True)
        fd, tmp = tempfile.mkstemp(dir=entry.parent, prefix=".tmp-", suffix=".json")
        try:
            with os.fdopen(fd, "w") as f:
                json.dump({"answer": list(answer)}, f)
            os.replace(tmp, entry)
        except BaseException:
            with contextlib.suppress(OSError):
                os.unlink(tmp)
            raise
        _prune_once(entry.parents[1])
    except OSError:
        return


@functools.cache
def _prune_once(build: Path) -> None:
    """Remove the directories of other checker builds unused for
    `KEEP_DAYS`, once per process; touch this build's."""
    os.utime(build)
    cutoff = time.time() - KEEP_DAYS * 86400
    for d in build.parent.iterdir():
        try:
            if d != build and d.is_dir() and d.stat().st_mtime < cutoff:
                shutil.rmtree(d, ignore_errors=True)
        except OSError:
            continue


def clear() -> None:
    """Remove every entry."""
    root = cache_dir()
    if root is not None:
        shutil.rmtree(root / "checker", ignore_errors=True)
