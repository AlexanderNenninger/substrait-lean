"""The 1.0 API review's items on `Report` and `sverify.io` (#795):
internal fields behind an underscore with deprecated aliases (B4, E1), and
`FlightLog` in `sverify.testing` (E1)."""

import dataclasses

import ibis
import pyarrow as pa
import pytest

import sverify as sv
from sverify.contracts import _REPORT_INTERNAL, Report
from sverify.io import DeltaSink, DeltaSource, SinkChange, StaticSource
from sverify.report import _REPORT_PRIVATE

#: What `Report` keeps public (B4), besides its methods.
PUBLIC = {
    "requires",
    "ensures",
    "facts",
    "deterministic",
    "issues",
    "assumed",
    "rows",
    "semantics",
    "lenses",
    "engine_version",
    "routes",
    "output",
    "ties",
    "dialect_differences",
    "inputs",
    "preconditions",
    "internal_plan",
    "black_boxes",
}


def test_report_fields_are_public_or_internal():
    names = {f.name for f in dataclasses.fields(Report)}
    assert {n for n in names if not n.startswith("_")} == PUBLIC
    assert {n.removeprefix("_") for n in names if n.startswith("_")} == {
        *_REPORT_INTERNAL,
        *_REPORT_PRIVATE,
    }


def _report() -> Report:
    t = ibis.table({"x": "int64"}, name="t")
    return sv.verify(t.select(y=t.x * 2), on_inferred="ignore")


@pytest.mark.parametrize("name", _REPORT_INTERNAL)
def test_internal_fields_keep_a_deprecated_alias(name):
    report = _report()
    with pytest.warns(DeprecationWarning, match=f"Report.{name} is internal"):
        got = getattr(report, name)
    assert got is getattr(report, "_" + name)


def test_plan_is_internal_plan():
    report = _report()
    assert report.internal_plan is not None
    with pytest.warns(DeprecationWarning, match="read Report.internal_plan"):
        assert report.plan == report.internal_plan  # type: ignore[attr-defined]


def test_the_public_attributes_do_not_warn(recwarn):
    report = _report()
    for name in PUBLIC:
        getattr(report, name)
    for name in ("verdict", "unproved", "needs", "errors", "notes"):
        getattr(report, name)
    assert not [w for w in recwarn if issubclass(w.category, DeprecationWarning)]


def test_sink_and_source_internals(tmp_path):
    sink = DeltaSink(str(tmp_path / "out"))
    assert sink.keeps_retired is True
    assert not hasattr(sink, "view")
    node = StaticSource(pa.table({"id": [1]}), name="t").pipe(lambda t: t)
    node.write(sink).refresh()
    source = DeltaSource(str(tmp_path / "out"))
    with pytest.warns(DeprecationWarning, match="hi_slack is internal"):
        assert source.hi_slack == source._hi_slack  # type: ignore[attr-defined]
    assert not hasattr(SinkChange, "native") and hasattr(SinkChange, "_native")


def test_a_custom_sink_still_says_it_keeps_retired_rows():
    from sverify.io import Sink

    class Keeps(Sink):
        keeps_retired = True

        def write(self, change):
            pass

    class Plain(Sink):
        def write(self, change):
            pass

    assert Keeps("k").keeps_retired and not Plain("p").keeps_retired
    assert DeltaSink("unused").keeps_retired


def test_flight_log_moved_to_testing():
    pytest.importorskip("pyarrow.flight")
    import sverify.io
    import sverify.testing
    from sverify.io.flight import FlightLog

    assert sverify.testing.FlightLog is FlightLog
    assert "FlightLog" in sverify.testing.__all__ and "FlightLog" not in sverify.io.__all__
    assert not hasattr(sverify.io, "FlightLog")
