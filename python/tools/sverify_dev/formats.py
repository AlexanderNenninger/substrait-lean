"""Fixtures of the formats a running pipeline reads (#734, #735, #736,
`docs/stability.md`): the sink's contract record, the Substrait export and
its contract, and the report as JSON, written by one version of sverify,
for the tests that read them with every later one (`tests/test_formats.py`).

Maintainer tooling (`sverify_dev`): not in the wheel, and not part of
sverify's API.

The script uses the public API only, so that it runs on a release installed
from PyPI as well as on this checkout:

    uv run python -m sverify_dev.formats tests/formats/<version>
    <venv with sverify==X>/bin/python tools/sverify_dev/formats.py tests/formats/X

It writes, under the directory it is given:

- `sink/delta/doubled/`: a Delta table a `DeltaSink` created and then merged a
  change into, with the contract in each commit;
- `sink/iceberg/doubled.metadata.json`: the table metadata of an `IcebergSink`'s
  table after the same two writes (the contract in the table properties,
  the plan, epoch and writer in each snapshot's summary);
- `sink/contract.json`: the last contract, as `Contract.to_json` wrote it;
- `substrait/<case>.json` (and `.bin` for one case): `Report.to_substrait`'s
  exports, where the version has it;
- `report/<case>.json`: `Report.to_json`'s documents, where the version has
  it: proved, not proved with a counterexample, with needs and assumptions,
  and after a run on DuckDB;
- `quarantine/doubled_quarantine/`: the quarantine table (#184) of a node
  over a source with rows that break its preconditions, and
  `quarantine/refresh.json`, that refresh's `Refresh.to_json`, where the
  version has `on_violation`;
- `VERSION`: the version that wrote them.

The release skill (`.claude/skills/release-sverify/SKILL.md`) runs it for
each release.
"""

from __future__ import annotations

import importlib.metadata
import json
import shutil
import sys
import tempfile
from pathlib import Path

import ibis
import pyarrow as pa
from ibis import _

import sverify as sv
from sverify.io import StaticSource

ORDERS = pa.table(
    {
        "id": pa.array([1, 2, 3], pa.int64()),
        "amount": pa.array([5, 7, 0], pa.int64()),
        "region": pa.array(["eu", "us", "eu"], pa.string()),
    }
)


@sv.transform(
    requires={"orders": [_.id.notnull(), _.amount >= 0, _.amount < 1000, sv.unique("id")]},
    ensures=[_.id.notnull(), _.doubled >= 0, sv.unique("id")],
)
def doubled(orders):
    return orders.filter(orders.amount > 0).select("id", "region", doubled=_.amount * 2)


def _pretty(text: str) -> str:
    return json.dumps(json.loads(text), indent=2, sort_keys=True) + "\n"


def _write_sink(out: Path) -> None:
    """A Delta and an Iceberg sink, each created and then given a change."""
    from deltalake import DeltaTable

    from sverify.io import DeltaSink, IcebergSink

    sink = out / "sink"
    sink.mkdir(parents=True)
    with tempfile.TemporaryDirectory() as tmp:
        from pyiceberg.catalog.sql import SqlCatalog

        cat = SqlCatalog("fixtures", uri=f"sqlite:///{tmp}/catalog.db", warehouse=f"file://{tmp}")
        cat.create_namespace("db")
        for make in (
            lambda: DeltaSink(str(sink / "delta" / "doubled")),
            lambda: IcebergSink(cat, "db.doubled"),
        ):
            src = StaticSource(ORDERS, version=1, name="orders")
            node = doubled(src).write(make())
            node.refresh()
            more = pa.table({"id": [4], "amount": [11], "region": ["us"]}).cast(ORDERS.schema)
            src.replace(pa.concat_tables([ORDERS, more]), version=2)
            node.refresh()
        table = cat.load_table("db.doubled")
        meta = Path(table.metadata_location.removeprefix("file://"))
        (sink / "iceberg").mkdir()
        shutil.copy(meta, sink / "iceberg" / "doubled.metadata.json")
        text = table.properties["sverify.contract"]
    (sink / "contract.json").write_text(_pretty(text))
    # The Delta log's commits must hold the record: under `sverify.contract`
    # from 1.0 on, under `sverify` before.
    history = DeltaTable(str(sink / "delta" / "doubled")).history()
    assert any("sverify.contract" in c or "sverify" in c for c in history), history


def _write_substrait(out: Path) -> None:
    """Exports of a few verified plans, where the version has `to_substrait`."""
    if not hasattr(sv.Report, "to_substrait"):
        return
    orders = ibis.table(
        {"id": "int64", "amount": "int64", "x": "float64", "region": "string"}, name="orders"
    )
    bounded = {"orders": [_.amount >= 0, _.amount < 1000, sv.unique("id")]}
    cases = {
        "row_and_table": sv.verify(
            orders.select("id", total=_.amount * 2),
            requires=bounded,
            ensures=[_.total >= 0, sv.unique("id")],
        ),
        "aggregate": sv.verify(
            orders.group_by("region").aggregate(n=_.count(), total=_.amount.sum()),
            requires={"orders": [_.amount >= 0, _.amount < 1000, sv.max_rows(1000)]},
            ensures=[_.n >= 1, _.total >= 0, sv.unique("region")],
        ),
        "double_shims": sv.verify(
            orders.filter(_.x == 1.5).select("id", "x"),
            requires={"orders": [_.id.notnull()]},
            ensures=[_.id.notnull()],
        ),
        "substrait_profile": sv.verify(
            # A comparison in the plan meets Substrait's NaN options, so
            # this plan has none (`tests/test_substrait_profile.py`).
            orders.select("id", n=_.region.length()),
            requires={"orders": [_.region.notnull()]},
            ensures=[_.n >= 0],
            semantics="substrait",
        ),
    }
    folder = out / "substrait"
    folder.mkdir(parents=True)
    for name, report in cases.items():
        assert report.proved, f"{name}: {report}"
        text = report.to_substrait()
        (folder / f"{name}.json").write_text(_pretty(text))
    (folder / "row_and_table.bin").write_bytes(cases["row_and_table"].to_substrait(format="binary"))


def _write_report(out: Path) -> None:
    """Reports as JSON, where the version has `Report.to_json`."""
    if not hasattr(sv.Report, "to_json"):
        return
    orders = ibis.table({"id": "int64", "qty": "int64", "total": "int64"}, name="orders")
    bounded = {"orders": [_.total >= 0, _.total < 1000, sv.unique("id")]}
    ran = sv.verify(orders.select("id", d=_.total * 2), requires=bounded)
    con = sv.connect()
    con.put("orders", pa.table({"id": [1, 2], "qty": [1, 1], "total": [3, 4]}))
    ran.run(con)
    cases = {
        "proved": sv.verify(
            orders.select("id", d=_.total * 2),
            requires=bounded,
            ensures=[_.d >= 0, sv.unique("id")],
        ),
        "not_proved": sv.verify(
            orders.select("id", d=_.total - 5),
            requires={"orders": [_.total >= 0, _.total < 1000]},
            ensures=[_.d >= 0, sv.unique("id")],
        ),
        "needs": sv.verify(orders.select(r=_.total // _.qty), on_inferred="error"),
        "assumed": sv.verify(orders.aggregate(s=orders.total.sum())),
        "ran": ran,
    }
    folder = out / "report"
    folder.mkdir(parents=True)
    for name, report in cases.items():
        (folder / f"{name}.json").write_text(_pretty(report.to_json()))


def _write_quarantine(out: Path) -> None:
    """A node that sets rows aside, its quarantine table and its refresh
    report, where the version has `on_violation`."""
    from sverify.io import DeltaSink

    try:
        policy = sv.transform(on_violation="quarantine")  # type: ignore[call-arg]
    except TypeError:
        return
    del policy
    folder = out / "quarantine"
    folder.mkdir(parents=True)
    dirty = pa.table({"id": [4, 4, 5], "amount": [1, 2, -3], "region": ["us", "eu", "eu"]})
    rows = pa.concat_tables([ORDERS, dirty.cast(ORDERS.schema)])
    src = StaticSource(rows, version=1, name="orders", on_violation="quarantine")  # type: ignore[call-arg]
    node = doubled(src).write(DeltaSink(str(folder / "doubled")))
    report = node.refresh()
    (folder / "refresh.json").write_text(_pretty(report.to_json()))
    shutil.rmtree(folder / "doubled")


def write(out: Path) -> None:
    """Write every fixture this version has under `out`, which must not exist."""
    if out.exists():
        raise SystemExit(f"{out} exists: fixtures of a version are written once")
    out.mkdir(parents=True)
    (out / "VERSION").write_text(importlib.metadata.version("sverify") + "\n")
    _write_sink(out)
    _write_substrait(out)
    _write_report(out)
    _write_quarantine(out)


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("usage: python -m sverify_dev.formats <directory>")
    write(Path(sys.argv[1]))
