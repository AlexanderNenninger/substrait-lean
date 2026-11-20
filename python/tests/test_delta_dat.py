"""The Delta Acceptance Testing suite read through `DeltaSource` (#861).

`delta-incubator/dat` publishes Delta tables written by Spark's reference
implementation, with each version's expected rows (`expected/<v>/
table_content`): column mapping, deletion vectors, checkpoints, partitions
with NULLs, CDF, schema changes and more. Every case and version is read
with `DeltaSource.snapshot` and compared with the expected rows.

The release declares no license, so it is not vendored: the test downloads
it at its pinned hash into `~/.cache/sverify/dat` and skips offline. A case
sverify does not read goes into `KNOWN` with the reason; none does at
v0.0.3."""

from __future__ import annotations

import hashlib
import json
import os
import shutil
import tarfile
import urllib.request
from pathlib import Path

import pyarrow.parquet as pq
import pytest

from sverify.io import DeltaSource

pytestmark = pytest.mark.filterwarnings("ignore::UserWarning")

RELEASE = "v0.0.3"
URL = f"https://github.com/delta-incubator/dat/releases/download/{RELEASE}/deltalake-dat-{RELEASE}.tar.gz"
SHA256 = "19c045bc6f4e8531d1985d0f7bb156d788e65078b435d613c8e4a9c753b4a982"
CACHE = Path(os.environ.get("SVERIFY_DAT", Path.home() / ".cache" / "sverify" / "dat"))
#: Cases (and versions) sverify does not read as DAT expects, with why.
KNOWN: dict[str, str] = {}


def _cases() -> Path:
    """The release's cases, downloaded and unpacked once; each step lands
    with a rename, so xdist's workers can race."""
    generated = CACHE / RELEASE / "out" / "reader_tests" / "generated"
    if generated.is_dir():
        return generated
    CACHE.mkdir(parents=True, exist_ok=True)
    archive = CACHE / f"deltalake-dat-{RELEASE}.tar.gz"
    if not archive.exists():
        part = archive.with_suffix(f".{os.getpid()}.part")
        try:
            urllib.request.urlretrieve(URL, part)  # noqa: S310 - a pinned https URL
        except OSError as e:
            pytest.skip(f"cannot download DAT {RELEASE}: {e}")
        os.replace(part, archive)
    if hashlib.sha256(archive.read_bytes()).hexdigest() != SHA256:
        archive.unlink(missing_ok=True)
        pytest.fail(f"DAT {RELEASE} does not have its pinned hash")
    unpacked = CACHE / f"{RELEASE}.{os.getpid()}.part"
    with tarfile.open(archive) as tar:
        tar.extractall(unpacked, filter="data")
    try:
        unpacked.rename(CACHE / RELEASE)
    except OSError:  # another worker was first
        shutil.rmtree(unpacked, ignore_errors=True)
    return generated


def _versions() -> list[tuple[str, str]]:
    """(case, expected version) pairs, as `pytest` ids; read after download."""
    try:
        cases = _cases()
    except pytest.skip.Exception:
        return []
    return [
        (case.name, exp.name)
        for case in sorted(cases.iterdir())
        for exp in sorted((case / "expected").iterdir())
    ]


def _rows(table) -> list[tuple]:
    return sorted((tuple(sorted(r.items())) for r in table.to_pylist()), key=repr)


@pytest.mark.parametrize(("case", "expected"), _versions(), ids="/".join)
def test_deltasource_reads_what_dat_expects(case: str, expected: str) -> None:
    if (why := KNOWN.get(f"{case}/{expected}") or KNOWN.get(case)) is not None:
        pytest.xfail(why)
    root = _cases() / case
    meta = json.loads((root / "expected" / expected / "table_version_metadata.json").read_text())
    want = pq.read_table(root / "expected" / expected / "table_content")
    version = None if expected == "latest" else int(expected.removeprefix("v"))
    snap = DeltaSource(str(root / "delta")).snapshot(version)
    assert snap.version == meta["version"]
    assert sorted(snap.table.column_names) == sorted(want.column_names)
    assert _rows(snap.table) == _rows(want)
