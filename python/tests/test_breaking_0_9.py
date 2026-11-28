"""0.9.0's breaking changes, each through its 0.8.0 spelling (#2577).

`docs/stability.md` asks that a break be loud and caught by a unit test of
the old form. Each test here uses the old form and checks that it raises;
where the error can name the replacement, it does. `docs/upgrading-0.9.md`
has each migration note with an example.

Tested elsewhere: the exception names and the checker's environment
variables (`test_api_1_0.py`), `Report`'s internal fields and `needed`
(`test_api_review_1_0.py`), `SVERIFY_PREBUILT_CHECK` (`test_hatch_build.py`).
"""

import dataclasses

import pytest

import sverify as sv
import sverify.errors
import sverify.io
import sverify.odcs
import sverify.openlineage
import sverify.types
from sverify.incremental import SourceBatch, Stored
from sverify.io import Contract
from sverify.io._common import SinkWrite


def _fields(cls: type) -> set[str]:
    return {f.name for f in dataclasses.fields(cls)}


# -- module-level names: the error names the replacement ----------------------


@pytest.mark.parametrize(
    ("module", "old", "new"),
    [
        (sverify.types, "Observation", "sverify.types.Lenses"),
        (sverify.types, "CheckedCondition", "sverify.types.Postcondition"),
        (sverify.types, "RefreshReport", "sverify.types.BatchRefresh"),
        (sverify.errors, "SqlError", "sverify.errors.SQLError"),
        (sverify.odcs, "OdcsContract", "sverify.odcs.ODCSContract"),
        (sv, "Changes", "sverify.io.Changes"),
        (sv, "from_substrait", "sverify.Report.from_substrait"),
    ],
)
def test_a_renamed_module_name_raises_naming_the_new_one(module, old, new):
    with pytest.raises(AttributeError, match=f"renamed it {new}$"):
        getattr(module, old)


def test_an_unknown_name_says_no_more_than_python_does():
    with pytest.raises(AttributeError, match=r"^module 'sverify.types' has no attribute 'Nope'$"):
        sverify.types.Nope  # noqa: B018


# -- attributes and keywords: the old name is gone -----------------------------


def test_report_proved_is_verdict():
    """`report.proved` → `report.verdict == sv.Verdict.PROVED`."""
    assert "proved" not in _fields(sv.Report) and not hasattr(sv.Report, "proved")
    assert "verdict" in dir(sv.Report)
    with pytest.raises(TypeError):
        bool(sv.Verdict.PROVED)


@pytest.mark.parametrize(
    ("cls", "old", "new"),
    [
        (sverify.types.Route, ["kind", "reason", "facts", "proved_facts", "version"],
         ["taken", "why", "engine_facts", "theorem_facts", "probed_version"]),
        (sverify.types.Issue, ["hint_needs"], ["suggested_requires", "needs"]),
        (Contract, ["profile"], ["semantics"]),
        (Stored, ["profile", "where", "where_key"], ["semantics", "location", "location_key"]),
        (SinkWrite, ["inserted", "deleted"], ["inserts", "deletes"]),
        (SourceBatch, ["trusted", "kind"], ["assumes", "mode"]),
        (sverify.types.RetentionReport, ["view"], ["node"]),
        (sverify.odcs.Unread, ["reason"], ["why"]),
        (sverify.types.References, ["col", "other"], ["cols", "table", "others"]),
    ],
)  # fmt: skip
def test_a_renamed_attribute_is_gone(cls, old, new):
    have = _fields(cls) | set(dir(cls))
    assert not have & set(old), cls.__name__
    assert set(new) <= have, cls.__name__


def test_upstream_says_why_and_its_assertions():
    names = set(dir(sverify.openlineage.Upstream)) | _fields(sverify.openlineage.Upstream)
    assert {"why", "assertions"} <= names
    assert not names & {"why_unverified", "evidence"}


def test_source_batch_takes_assumes_and_mode():
    with pytest.raises(TypeError, match="'trusted'"):
        SourceBatch.from_changes(0, 1, trusted="t")  # type: ignore[call-arg]
    with pytest.raises(TypeError, match="'reason'"):
        SourceBatch.from_snapshot(0, 1, None, reason="r")  # type: ignore[call-arg]


def test_references_takes_cols_table_and_others():
    with pytest.raises(TypeError, match="'col'"):
        sverify.types.References(col="a", table="t", other="b")  # type: ignore[call-arg]
    r = sv.references("a", to=("t", "b"))
    assert (r.cols, r.table, r.others) == (("a",), "t", ("b",))


def test_flight_source_takes_credentials():
    pytest.importorskip("pyarrow.flight")
    from sverify.io import FlightSource

    for old in ("secret", "token"):
        with pytest.raises(TypeError, match=f"'{old}'"):
            FlightSource("grpc://localhost:1", "t", **{old: "x"})  # type: ignore[call-arg]


def test_batch_refresh_diffed_is_a_dict():
    """`RefreshReport.diffed`, a list, is `BatchRefresh.diffed`, a dict of
    view to reason: `.append` and indexing by position no longer work."""
    diffed = sverify.types.BatchRefresh(sources=[], preconditions=[], versions={}).diffed
    assert diffed == {}
    with pytest.raises(AttributeError):
        diffed.append("v")  # type: ignore[attr-defined]


# -- #2081's removals -----------------------------------------------------------


def test_sink_keeps_retired_is_the_one_spelling():
    """0.8's `_keeps_retired = True` is no longer read, so a sink that sets
    it is refused where it is defined."""
    with pytest.raises(TypeError, match="keeps_retired = True"):

        class Old(sverify.io.Sink):  # pyright: ignore[reportUnusedClass]
            _keeps_retired = True

            def write(self, change):
                pass


def test_iceberg_sink_keeps_create_options_ignored_internal():
    pytest.importorskip("pyiceberg")
    from sverify.io import IcebergSink

    assert not hasattr(IcebergSink, "create_options_ignored")


def test_maintain_takes_the_retention_keywords():
    pytest.importorskip("pyiceberg")
    from sverify.io import DeltaSink, IcebergSink

    with pytest.raises(TypeError, match="'vacuum'"):
        DeltaSink("unused").maintain(vacuum="7d")  # type: ignore[call-arg]
    with pytest.raises(TypeError, match="'expire'"):
        IcebergSink.maintain(None, expire="7d")  # type: ignore[call-arg, arg-type]


def test_sql_takes_name():
    with pytest.raises(TypeError, match=r"takes name= since 0\.9\.0"):
        sv.sql("SELECT * FROM t", as_="t")  # type: ignore[call-overload]


def test_rows_per_takes_columns_and_at_most():
    with pytest.raises(ValueError, match=r"rows_per\('a', 'b', at_most=3\)"):
        sv.rows_per(["a", "b"], 3)  # type: ignore[arg-type]


def test_arrives_within_takes_a_duration():
    with pytest.raises(TypeError, match="'days'"):
        sv.arrives_within("ts", days=1)  # type: ignore[call-arg]


# -- the command line -------------------------------------------------------------


@pytest.mark.parametrize(
    ("old", "new"), [("--output-format", "--format X"), ("--json", "--format json")]
)
def test_a_removed_flag_names_its_replacement(old, new, tmp_path, capsys):
    from sverify.cli import ExitCode, main

    path = tmp_path / "p.py"
    path.write_text("")
    argv = ["check", str(path), old, *(["json"] if old == "--output-format" else [])]
    assert main(argv) == ExitCode.USAGE
    assert f"sverify 0.9.0 removed {old}: write {new}" in capsys.readouterr().err
