"""Contract drift (#769, ruling 189): a stored node's contract against the
one its sink last committed. A committed promise is weakened when the node
no longer proves it; a reworded CHECK the node still proves is kept."""

from __future__ import annotations

import json
from pathlib import Path

import pyarrow as pa
import pytest
from ibis import _

import sverify as sv
from sverify.cli import main
from sverify.io import DeltaSink, StaticSource
from sverify.io._common import drift

pytest.importorskip("deltalake")

ROWS = pa.table({"id": [1, 2, 3], "customer": [1, 1, 2], "amount": [5, 7, 9]})


def _transform(requires, ensures):
    @sv.transform(requires={"orders": requires}, ensures=ensures)
    def paid(orders):
        return orders.select("id", "customer", "amount")

    return paid


def _stored(path: Path, transform):
    return StaticSource(ROWS, name="orders").pipe(transform).write(DeltaSink(str(path)))


def _drift(tmp_path: Path, before, after):
    sink = tmp_path / "paid"
    _stored(sink, before).refresh()
    committed = DeltaSink(str(sink)).contract()
    assert committed is not None
    return drift(committed, _stored(sink, after))


BOUND = [_.amount > 1, _.amount < 100, _.id.notnull(), sv.unique("id")]


def test_unchanged(tmp_path):
    t = _transform(BOUND, [_.amount > 1, _.id.notnull(), sv.unique("id")])
    got = _drift(tmp_path, t, t)
    assert not any(got.weakened.values()) and not any(got.added.values())
    assert not got.plan_changed


def test_a_loosened_bound_is_weakened(tmp_path):
    before = _transform(BOUND, [_.amount > 1])
    after = _transform([_.amount > 0, _.amount < 100, sv.unique("id")], [_.amount > 0])
    got = _drift(tmp_path, before, after)
    assert got.weakened["checks"] == ["amount > 1"]
    assert got.why["amount > 1"].startswith("not proved:")


def test_a_tightened_bound_is_kept(tmp_path):
    """The text changed, and the committed one proves from the new contract."""
    before = _transform([_.amount > 0, _.amount < 100], [_.amount > 0])
    after = _transform([_.amount > 1, _.amount < 100], [_.amount > 1])
    got = _drift(tmp_path, before, after)
    assert got.weakened["checks"] == []
    assert got.added["checks"] == ["amount > 1"]


def test_a_condition_inserted_before_the_others_is_no_drift(tmp_path):
    """The record's CHECK names are positional; the texts decide."""
    before = _transform(BOUND, [_.amount < 100])
    after = _transform(BOUND, [_.amount > 1, _.amount < 100])
    got = _drift(tmp_path, before, after)
    assert not any(got.weakened.values())


def test_a_shrunk_key_is_kept_and_a_widened_one_weakened(tmp_path):
    keyed = [_.amount > 1, _.amount < 100, sv.unique("id")]
    by_both = _transform(keyed, [sv.unique("id", "customer")])
    by_id = _transform(keyed, [sv.unique("id")])
    assert not any(_drift(tmp_path / "a", by_both, by_id).weakened.values())
    widened = _drift(tmp_path / "b", by_id, by_both)
    assert widened.weakened["unique"] == [["id"]]


def test_a_lost_not_null_is_weakened(tmp_path):
    before = _transform(BOUND, [_.id.notnull()])
    after = _transform([_.amount > 1, _.amount < 100], [_.amount > 1])
    got = _drift(tmp_path, before, after)
    assert "id" in got.weakened["not_null"]


def test_check_against_sink_gates_on_a_weakened_contract(tmp_path, capsys):
    sink = tmp_path / "paid"
    req = [_.amount > 1, _.amount < 100, sv.unique("id")]
    _stored(sink, _transform(req, [_.amount > 1])).refresh()
    path = tmp_path / "p.py"
    head = (
        "import pyarrow as pa\nimport sverify as sv\nfrom ibis import _\n"
        "from sverify.io import DeltaSink, StaticSource\n"
        "ROWS = pa.table({'id': [1, 2, 3], 'customer': [1, 1, 2], 'amount': [5, 7, 9]})\n"
        "@sv.transform(requires={'orders': [_.amount > REQ, _.amount < 100, sv.unique('id')]},"
        " ensures=[_.amount > REQ])\n"
        "def paid(orders):\n    return orders.select('id', 'customer', 'amount')\n"
        f"stored = StaticSource(ROWS, name='orders').pipe(paid).write(DeltaSink({str(sink)!r}))\n"
    )
    path.write_text(head.replace("REQ", "1"))
    assert main(["check", f"{path}:stored", "--against-sink", "--json"]) == 0
    doc = json.loads(capsys.readouterr().out)
    assert doc["drift"]["stored"]["weakened"]["checks"] == []
    path.write_text(head.replace("REQ", "0"))
    assert main(["check", f"{path}:stored", "--against-sink", "--json"]) == 1
    doc = json.loads(capsys.readouterr().out)
    assert [f["code"] for f in doc["findings"]] == ["contract_weakened"]
    assert doc["findings"][0]["condition"] == "amount > 1"
    # Without the flag, check opens no sink.
    assert main(["check", f"{path}:stored", "--json"]) == 0
    assert "drift" not in json.loads(capsys.readouterr().out)
