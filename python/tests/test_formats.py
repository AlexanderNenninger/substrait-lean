"""The formats a running pipeline reads stay readable across releases
(`docs/stability.md`, #734, #735, #736).

`tests/formats/<version>/` holds what each version wrote
(`python -m sverify_dev.formats`): a Delta table and an Iceberg table's
metadata with the sink's contract record, exports of `to_substrait` and
reports as JSON.
Each test reads every version's fixtures with this version, as a job would,
and checks what it read against the schemas in `sverify/schemas/`, which
describe the current format; a fixture of an earlier format reads as it. The tests that
write the formats afresh check that this version only adds keys."""

from __future__ import annotations

import json
import re
import shutil
from pathlib import Path

import pyarrow as pa
import pytest

import sverify as sv
from sverify.io import Contract
from sverify.io._common import CONTRACT_FORMAT
from sverify.substrait_export import TYPE_URL, read

jsonschema = pytest.importorskip("jsonschema")

HERE = Path(__file__).resolve().parent
FORMATS = HERE / "formats"
SCHEMAS = Path(sv.__file__).resolve().parent / "schemas"
PROTO = Path(sv.__file__).resolve().parent / "substrait_contract.proto"

VERSIONS = sorted(p.name for p in FORMATS.iterdir() if (p / "VERSION").exists())
EXPORTS = sorted((v, p.stem) for v in VERSIONS for p in (FORMATS / v / "substrait").glob("*.json"))
REPORTS = sorted((v, p.stem) for v in VERSIONS for p in (FORMATS / v / "report").glob("*.json"))


def _schema(name: str) -> dict:
    return json.loads((SCHEMAS / name).read_text())


def _valid(doc: object, schema: str) -> None:
    jsonschema.validate(doc, _schema(schema))


def test_fixtures_exist() -> None:
    """The baseline: a release from PyPI and this branch's own fixtures."""
    assert "0.4.0" in VERSIONS
    assert EXPORTS, "no Substrait exports among the fixtures"
    assert REPORTS, "no reports among the fixtures"


# -- the sink's contract record (#734) -------------------------------------------


@pytest.mark.parametrize("version", VERSIONS)
def test_sink_record_reads(version: str) -> None:
    """Each version's record reads as the current format, which follows the
    schema; a record of format 1 names the node `view`."""
    text = (FORMATS / version / "sink" / "contract.json").read_text()
    c = Contract.from_json(text)
    _valid(json.loads(c.to_json()), "sink-contract.schema.json")
    assert c.format == CONTRACT_FORMAT == 2
    assert c.node == "doubled" and c.sources == {"orders": 2} and c.epoch == 2
    assert "id" in c.not_null and c.unique == [["id"]]


@pytest.mark.parametrize("version", VERSIONS)
def test_delta_sink_record(version: str, tmp_path: Path) -> None:
    """A `DeltaSource` reads the contract each version's `DeltaSink` committed,
    under the key `sverify.contract` or, before 1.0, `sverify`, and every
    commit's record reads as one that follows the schema."""
    from deltalake import DeltaTable

    from sverify.io import DeltaSource
    from sverify.io.delta import LEGACY_METADATA_KEY, METADATA_KEY

    table = tmp_path / "doubled"
    shutil.copytree(FORMATS / version / "sink" / "delta" / "doubled", table)
    records = [
        c.get(METADATA_KEY, c.get(LEGACY_METADATA_KEY))
        for c in DeltaTable(str(table)).history()
        if METADATA_KEY in c or LEGACY_METADATA_KEY in c
    ]
    assert len(records) == 2
    for r in records:
        _valid(json.loads(Contract.from_json(r).to_json()), "sink-contract.schema.json")
    expected = Contract.from_json((FORMATS / version / "sink" / "contract.json").read_text())
    assert DeltaSource(str(table)).contract() == expected


@pytest.mark.parametrize("version", VERSIONS)
def test_delta_sink_resumes(version: str, tmp_path: Path) -> None:
    """A pipeline on this version refreshes into a Delta table an earlier
    version's sink wrote, and records its contract in the current format."""
    formats = pytest.importorskip("sverify_dev.formats")
    from deltalake import DeltaTable

    from sverify.io import DeltaSink, DeltaSource, StaticSource

    table = tmp_path / "doubled"
    shutil.copytree(FORMATS / version / "sink" / "delta" / "doubled", table)
    more = pa.table({"id": [4, 5], "amount": [11, 3], "region": ["us", "eu"]})
    rows = pa.concat_tables([formats.ORDERS, more.cast(formats.ORDERS.schema)])
    src = StaticSource(rows, version=3, name="orders")
    node = formats.doubled(src).write(DeltaSink(str(table)))
    node.refresh()
    rows = DeltaTable(str(table)).to_pyarrow_table().sort_by("id")
    assert rows.column("id").to_pylist() == [1, 2, 4, 5]
    assert rows.column("doubled").to_pylist() == [10, 14, 22, 6]
    c = DeltaSource(str(table)).contract()
    assert c is not None and c.format == CONTRACT_FORMAT and c.sources == {"orders": 3}


@pytest.mark.parametrize("version", VERSIONS)
def test_iceberg_sink_record(version: str) -> None:
    """An Iceberg table's property `sverify.contract` holds each version's
    record, and the current snapshot's summary names its plan and epoch, as
    `IcebergSource.stored` and `IcebergSink.committed` read them."""
    from pyiceberg.table import StaticTable

    from sverify.io import iceberg

    meta = FORMATS / version / "sink" / "iceberg" / "doubled.metadata.json"
    t = StaticTable.from_metadata(str(meta))
    text = t.properties[iceberg.KEY]
    c = Contract.from_json(text)
    _valid(json.loads(c.to_json()), "sink-contract.schema.json")
    assert c == Contract.from_json((FORMATS / version / "sink" / "contract.json").read_text())
    snapshot = t.current_snapshot()
    assert snapshot is not None and snapshot.summary is not None
    summary = snapshot.summary
    assert summary.get(iceberg.PLAN) == c.plan
    assert summary.get(iceberg.EPOCH) == str(c.epoch)
    assert summary.get(iceberg.APP) == "sverify:doubled"


def test_sink_record_only_gains_keys(tmp_path: Path) -> None:
    """The record this version writes follows the schema and has every key
    an earlier version's record has, read as the current format."""
    from sverify.io import DeltaSink, DeltaSource, StaticSource

    formats = pytest.importorskip("sverify_dev.formats")
    node = formats.doubled(StaticSource(formats.ORDERS, version=1, name="orders"))
    node.write(DeltaSink(str(tmp_path / "t"))).refresh()
    c = DeltaSource(str(tmp_path / "t")).contract()
    assert c is not None
    now = json.loads(c.to_json())
    _valid(now, "sink-contract.schema.json")
    assert now["format"] == CONTRACT_FORMAT
    for version in VERSIONS:
        text = (FORMATS / version / "sink" / "contract.json").read_text()
        old = {k for k in json.loads(text) if k in Contract.__dataclass_fields__ or k == "view"}
        old = {"node" if k == "view" else k for k in old} | {"format"}
        assert old <= set(now), f"keys of {version}'s record dropped: {set(old) - set(now)}"


def test_newer_record_refused() -> None:
    """A record of a format this version does not know is refused, and the
    error says to upgrade; unknown keys are left out."""
    text = (FORMATS / VERSIONS[-1] / "sink" / "contract.json").read_text()
    data = json.loads(text)
    with pytest.raises(ValueError, match="upgrade sverify"):
        Contract.from_json(json.dumps({**data, "format": CONTRACT_FORMAT + 1}))
    assert Contract.from_json(json.dumps({**data, "added_in_1_9": [1]})) == Contract.from_json(text)


# -- the Substrait contract metadata (#735) --------------------------------------


@pytest.mark.parametrize(("version", "case"), EXPORTS)
def test_substrait_export_reads_and_proves(version: str, case: str) -> None:
    """`from_substrait` reads each version's export and proves its contract
    again: the same postconditions, each with the status the export
    records."""
    text = (FORMATS / version / "substrait" / f"{case}.json").read_text()
    imp = read(text)
    _valid(imp.manifest, "substrait-manifest.schema.json")
    report = sv.from_substrait(text)
    assert report.proved, str(report)
    assert [(c.label, c.proved) for c in report.ensures] == [
        (e["text"], e.get("proved", False)) for e in imp.ensures
    ]


@pytest.mark.parametrize("version", sorted({v for v, _ in EXPORTS}))
def test_substrait_binary_export(version: str) -> None:
    """The binary form of an export reads as its JSON form does."""
    folder = FORMATS / version / "substrait"
    binary = (folder / "row_and_table.bin").read_bytes()
    assert read(binary) == read((folder / "row_and_table.json").read_text())
    assert sv.from_substrait(binary).proved


def test_substrait_manifest_only_gains_keys() -> None:
    """The manifest this version writes follows the schema and has every key
    an earlier version's manifest has."""
    import ibis
    from ibis import _

    orders = ibis.table({"id": "int64", "amount": "int64"}, name="orders")
    report = sv.verify(
        orders.select("id", total=_.amount * 2),
        requires={"orders": [_.amount >= 0, _.amount < 1000, sv.unique("id")]},
        ensures=[_.total >= 0, sv.unique("id")],
    )
    now = read(report.to_substrait()).manifest
    _valid(now, "substrait-manifest.schema.json")
    for version, case in EXPORTS:
        old = read((FORMATS / version / "substrait" / f"{case}.json").read_text()).manifest
        assert set(old) <= set(now), f"keys of {version}/{case} dropped: {set(old) - set(now)}"


def test_substrait_manifest_of_format_1() -> None:
    """A manifest of format 1, written before 1.0, reads with the names of
    format 2 (`semantics`, `equivalence`); a newer format is refused."""
    from sverify.substrait_export import FORMAT, _manifest

    def text(v: str, c: str) -> str:
        return (FORMATS / v / "substrait" / f"{c}.json").read_text()

    olds = [(v, c) for v, c in EXPORTS if '"profile"' in text(v, c)]
    assert olds, "no export of format 1 among the fixtures"
    for v, c in olds:
        m = read(text(v, c)).manifest
        assert m["format"] == FORMAT == 2
        assert "profile" not in m and "observation" not in m
        assert m["semantics"] in ("reference", "substrait") and isinstance(m["equivalence"], str)
    with pytest.raises(ValueError, match="upgrade sverify"):
        _manifest({"format": FORMAT + 1})


#: The fields of the contract messages as 1.0 fixes them: a field keeps its
#: number and type, and new fields take new numbers (`docs/stability.md`).
PROTO_FIELDS = {
    "Contract": {
        "manifest": (1, "google.protobuf.Struct"),
        "requires": (2, "repeated Condition"),
        "ensures": (3, "repeated Condition"),
    },
    "Condition": {
        "text": (1, "string"),
        "table": (2, "string"),
        "kind": (3, "string"),
        "inferred": (4, "bool"),
        "plan": (5, "substrait.Plan"),
        "entry": (6, "google.protobuf.Value"),
        "proved": (7, "bool"),
    },
}


def _proto_fields() -> tuple[str, dict[str, dict[str, tuple[int, str]]]]:
    text = re.sub(r"//[^\n]*", "", PROTO.read_text())
    package = re.search(r"package\s+([\w.]+);", text)
    assert package is not None
    fields: dict[str, dict[str, tuple[int, str]]] = {}
    for name, body in re.findall(r"message\s+(\w+)\s*\{([^}]*)\}", text):
        fields[name] = {
            f: (int(n), " ".join(ty.split()))
            for ty, f, n in re.findall(r"((?:repeated\s+)?[\w.]+)\s+(\w+)\s*=\s*(\d+);", body)
        }
    return package[1], fields


def test_proto_keeps_its_fields() -> None:
    """`substrait_contract.proto` keeps its package and every field's number
    and type; a field it adds takes a number no field had."""
    package, fields = _proto_fields()
    assert package == "io.sverify.substrait.v1"
    assert f"type.googleapis.com/{package}.Contract" == TYPE_URL
    for message, frozen in PROTO_FIELDS.items():
        now = fields[message]
        for name, spec in frozen.items():
            assert now.get(name) == spec, f"{message}.{name} changed: {now.get(name)} != {spec}"
        numbers = [n for n, _ in now.values()]
        assert len(numbers) == len(set(numbers)), f"{message} reuses a field number"


# -- the report as JSON (#736) ---------------------------------------------------


@pytest.mark.parametrize(("version", "case"), REPORTS)
def test_report_reads(version: str, case: str) -> None:
    """`Report.from_json` reads each version's report: it follows the schema,
    keeps its verdict, and writes every key it read back."""
    doc = json.loads((FORMATS / version / "report" / f"{case}.json").read_text())
    _valid(doc, "report.schema.json")
    report = sv.Report.from_json(doc)
    assert report.proved == doc["proved"] and report.verdict == doc["verdict"]
    assert [c.label for c in report.ensures] == [c["properties"]["label"] for c in doc["ensures"]]
    assert [n.code for n in report.needs] == [n["code"] for n in doc["needs"]]
    assert set(report.routes) == set(doc["routes"])
    now = json.loads(report.to_json())
    _valid(now, "report.schema.json")
    assert set(doc) <= set(now), f"keys of {version}/{case} dropped: {set(doc) - set(now)}"
    assert {k: v for k, v in now.items() if k in doc and k != "sverify"} == {
        k: v for k, v in doc.items() if k != "sverify"
    }


def test_report_only_gains_keys() -> None:
    """The report this version writes has every key an earlier version's
    report of the same case has."""
    import ibis
    from ibis import _

    orders = ibis.table({"id": "int64", "qty": "int64", "total": "int64"}, name="orders")
    report = sv.verify(
        orders.select("id", d=_.total * 2),
        requires={"orders": [_.total >= 0, _.total < 1000, sv.unique("id")]},
        ensures=[_.d >= 0, sv.unique("id")],
    )
    now = json.loads(report.to_json())
    _valid(now, "report.schema.json")
    for version, case in REPORTS:
        if case == "proved":
            old = json.loads((FORMATS / version / "report" / f"{case}.json").read_text())
            assert set(old) <= set(now), f"keys of {version}/{case} dropped: {set(old) - set(now)}"
            for c_old, c_now in zip(old["ensures"], now["ensures"], strict=True):
                assert set(c_old) <= set(c_now)


def test_report_of_format_1_refused() -> None:
    """Format 1 of the report was on main before 1.0, in no release: a
    reader says to write it again."""
    with pytest.raises(ValueError, match="no release wrote"):
        sv.Report.from_json({"format": 1})
