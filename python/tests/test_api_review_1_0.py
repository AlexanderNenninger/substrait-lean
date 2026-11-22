"""The 1.0 API review's items on `Report` and `sverify.io` (#795):
internal fields behind an underscore, with no alias (B4, E1; #2081), and
`FlightLog` in `sverify.testing` (E1)."""

import dataclasses

import ibis
import pyarrow as pa
import pytest

import sverify as sv
from sverify.io import DeltaSink, DeltaSource, SinkChange, StaticSource
from sverify.report import Report

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


@pytest.fixture(scope="module")
def report() -> Report:
    """One verified report, read by the tests below."""
    t = ibis.table({"x": "int64"}, name="t")
    return sv.verify(t.select(y=t.x * 2), on_inferred="ignore")


def test_internal_fields_and_old_names_have_no_alias(report):
    """1.0 keeps no alias (#2081): an internal field's old name, `plan`
    (`internal_plan`) and `needed`, `needed_text`, `needed_conditions`
    (`needs`) are gone."""
    old = [f.name.removeprefix("_") for f in dataclasses.fields(Report) if f.name.startswith("_")]
    for name in [*old, "plan", "needed", "needed_text", "needed_conditions"]:
        assert not hasattr(report, name), name


def test_the_public_attributes_do_not_warn(report, recwarn):
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
    assert not hasattr(source, "hi_slack")
    assert not hasattr(SinkChange, "native") and hasattr(SinkChange, "_native")
    with pytest.raises(TypeError):  # keyword-only, like the other result types (#2343)
        SinkChange(None, None, None, None)  # type: ignore[misc]


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
