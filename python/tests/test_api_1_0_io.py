"""The API review's sweep before 1.0 (`api-review/PROPOSAL.md`, items 11
and 12): `contract()` on every source and sink, `maintain`'s names, required
`name=`, snake_case values, and the top level (`Changes`, `from_substrait`,
`rows_per`, `arrives_within`, `approx`, `sql(name=)`, `ContractedTransform.report`).
Each renamed released name warns for one release."""

import warnings
from datetime import timedelta

import ibis
import pyarrow as pa
import pytest
from ibis import _

import sverify as sv
from sverify._duration import duration
from sverify.contracts import label
from sverify.io import Changes, Contract, DeltaSink, Sink, StaticSource
from sverify.testing import source


def _quiet(fn, *args, **kwargs):
    with warnings.catch_warnings():
        warnings.simplefilter("error", DeprecationWarning)
        return fn(*args, **kwargs)


# -- A1: Changes and from_substrait ---------------------------------------------


def test_changes_lives_in_io() -> None:
    assert "Changes" not in sv.__all__ and "from_substrait" not in sv.__all__
    with pytest.warns(DeprecationWarning, match="import it from sverify.io"):
        assert sv.Changes is Changes


def test_from_substrait_is_a_classmethod_of_report() -> None:
    t = ibis.table({"k": "int64"}, name="t")
    exported = _quiet(sv.verify, t.select("k")).to_substrait()
    assert _quiet(sv.Report.from_substrait, exported).proved
    with pytest.warns(DeprecationWarning, match="sverify.Report.from_substrait"):
        assert sv.from_substrait(exported).proved  # type: ignore[operator]


# -- A2: condition arguments --------------------------------------------------------


def test_rows_per_takes_its_columns_as_unique_does() -> None:
    assert label(sv.rows_per("a", "b", at_most=3)) == "rows_per(a, b, at_most=3)"
    with pytest.warns(DeprecationWarning, match=r"rows_per\(\*cols, at_most=\.\.\.\)"):
        assert sv.rows_per(["a", "b"], at_most=3) == sv.rows_per("a", "b", at_most=3)  # type: ignore[arg-type]
    with pytest.raises(ValueError, match="needs at_most="):
        sv.rows_per("a")


def test_arrives_within_takes_a_duration() -> None:
    iso = _quiet(sv.arrives_within, "ts", "PT15M")
    assert iso == sv.arrives_within("ts", timedelta(minutes=15))
    with pytest.warns(DeprecationWarning, match="ISO 8601"):
        assert sv.arrives_within("ts", minutes=15) == iso
    with pytest.raises(TypeError, match="needs the lateness"):
        sv.arrives_within("ts")


def test_durations_read_iso_8601() -> None:
    assert duration("P1DT12H") == timedelta(days=1, hours=12)
    assert duration("P2W") == timedelta(weeks=2)
    assert duration("PT0.5S") == timedelta(seconds=0.5)
    for bad in ("P1M", "P1Y", "PT", "15 minutes"):
        with pytest.raises(ValueError, match="ISO 8601"):
            duration(bad)


# -- A3: approx's tolerances --------------------------------------------------------


def test_approx_takes_the_tolerances_of_within() -> None:
    assert sv.approx(_.x <= 100).rel == 1e-6
    a = sv.approx(_.x <= 100, abs=0.5)
    assert a.rel is None and a.slack(100.0) == 0.5
    assert sv.approx(_.x <= 1.0, ulps=4).slack(1.0) == 4 * 2**-52
    both = sv.approx(_.x <= 1e9, rel=1e-6, abs=0.5)
    assert both.slack(1e9) == 1000.0
    assert label(a) == "approx((_.x <= 100), abs=0.5)"
    with pytest.raises(ValueError, match="0 or more"):
        sv.approx(_.x <= 1, abs=-1)


# -- A4: sql(name=) -------------------------------------------------------------------


def test_sql_names_the_chained_table_with_name() -> None:
    step = _quiet(sv.sql, "SELECT id FROM orders", name="orders")
    assert step.as_ == "orders"
    with pytest.warns(DeprecationWarning, match=r"sql\(as_=\.\.\.\) is deprecated"):
        sv.sql("SELECT id FROM orders", as_="orders")  # type: ignore[call-overload]


# -- A6: ContractedTransform.report -------------------------------------------------


def test_a_transform_has_a_report() -> None:
    @sv.transform(ensures=[_.k >= 0], requires=[_.k >= 0])
    def keep(t):
        return t

    t = ibis.table({"k": "int64"}, name="t")
    _quiet(keep, t)
    assert keep.report is not None and keep.report.proved
    with pytest.warns(DeprecationWarning, match=r"read \.report"):
        assert keep.last_report is keep.report
    assert keep.report.preconditions == []


# -- E2: contract() on every source and sink --------------------------------------


@sv.transform(requires={"orders": [_.amount >= 0, _.amount < 1000]})
def doubled(orders):
    return orders.select("id", d=orders.amount * 2)


def test_a_sink_and_its_source_read_the_contract(tmp_path) -> None:
    orders = StaticSource(pa.table({"id": [1], "amount": [3]}), name="orders")
    sink = DeltaSink(str(tmp_path / "doubled"))
    node = _quiet(doubled, orders).write(sink)
    _quiet(node.refresh)
    first, at = _quiet(sink.contract), sink.source().latest()
    assert first is not None and first == _quiet(sink.source().contract)
    orders.apply(Changes(inserts=[(2, 4)]))
    _quiet(node.refresh)
    assert _quiet(sink.contract).epoch == first.epoch + 1
    assert _quiet(sink.contract, at) == first
    with pytest.warns(DeprecationWarning, match=r"call sink\.contract\(\)"):
        assert sink.committed() == sink.contract()


def test_a_custom_sink_overriding_committed_still_works() -> None:
    with pytest.warns(DeprecationWarning, match="override contract"):

        class Old(Sink):
            def committed(self):
                return None

            def write(self, change):
                return None

    assert Old("t").contract() is None
    with pytest.raises(ValueError, match="keeps no history"):
        Sink("t").contract(3)


def test_a_custom_sink_overrides_contract() -> None:
    class New(Sink):
        record: Contract | None = None

        def contract(self, version=None):
            return self.record

        def write(self, change):
            self.record = change.contract

    orders = StaticSource(pa.table({"id": [1], "amount": [3]}), name="orders")
    sink = New("doubled")
    _quiet(_quiet(doubled, orders).write(sink).refresh)
    c = sink.contract()
    assert c is not None and c.node == "doubled"


# -- E3: maintain's names ------------------------------------------------------------


def test_maintain_takes_the_constructors_names(tmp_path) -> None:
    orders = StaticSource(pa.table({"id": [1], "amount": [3]}), name="orders")
    sink = DeltaSink(str(tmp_path / "doubled"), vacuum_retention="P7D")
    assert sink.vacuum_retention == timedelta(days=7)
    _quiet(_quiet(doubled, orders).write(sink).refresh)
    assert "vacuumed" in _quiet(sink.maintain, vacuum_retention="PT0S")
    with pytest.warns(DeprecationWarning, match="write vacuum_retention="):
        sink.maintain(vacuum=timedelta(0))


# -- E4: names are required ------------------------------------------------------------


def test_a_static_source_needs_a_name() -> None:
    t = pa.table({"k": [1]})
    assert _quiet(StaticSource, t, name="k", version=2).version == 2
    with pytest.warns(DeprecationWarning, match="without name="):
        assert StaticSource(t).name == "table"
    with pytest.warns(DeprecationWarning, match=r"StaticSource\(table, version\)"):
        assert StaticSource(t, 3, name="k").version == 3  # type: ignore[misc]
    with pytest.warns(DeprecationWarning, match="without name="):
        source(t)


# -- E5: snake_case values ----------------------------------------------------------------


def test_batch_modes_are_snake_case() -> None:
    orders = StaticSource(pa.table({"id": [1], "amount": [3]}), name="orders")
    node = _quiet(doubled, orders)
    _quiet(node.refresh)
    orders.apply(Changes(inserts=[(2, 4)]))
    out = _quiet(node.refresh)
    assert out["doubled"].report is not None
    assert out["doubled"].report.sources[0].mode == "change_feed"
    assert "(change feed)" in out["doubled"].summary()
