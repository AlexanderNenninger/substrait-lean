"""The API review's sweep before 1.0 (#795, items 7, 8,
9 and 14): the 0.6 aliases removed (`test_api_06.py`), the engine lists of
1.x, the exception names, `SverifyWarning`, `SverifyError.code`, and the
environment variables. Each renamed released name warns for one release."""

import importlib
import re

import pytest
from ibis import _

import sverify as sv
import sverify.engines
import sverify.errors
from _pipelines import make_orders
from sverify.contracts import ContractedTransform
from sverify.engines import ENGINES
from sverify.errors import (
    SverifyError,
    SverifyWarning,
    UnprovedWarning,
    UnsupportedError,
)

# -- H1: names that end in Error ----------------------------------------------


def test_the_old_exception_names_are_gone() -> None:
    for old in ("Unsupported", "NotIncremental"):
        assert not hasattr(sverify.errors, old)
    assert not hasattr(sverify.contracts, "InferredPreconditionWarning")
    assert "NotIncrementalError" in sverify.errors.__all__


# -- H2 and H4: SverifyWarning and .code --------------------------------------


def _public(base: type) -> list[type]:
    return [
        c
        for n in sverify.errors.__all__
        if isinstance(c := getattr(sverify.errors, n), type) and issubclass(c, base)
    ]


def test_every_error_has_its_own_snake_case_code() -> None:
    errors = _public(SverifyError)
    assert len(errors) == 20
    codes = {c.code for c in errors if c is not SverifyError}
    assert len(codes) == len(errors) - 1
    assert all(re.fullmatch(r"[a-z]+(_[a-z]+)*", c) for c in codes), codes
    assert UnsupportedError.code == "unsupported"
    assert sverify.errors.UnverifiedRunError.code == "unverified_run"


def test_every_warning_is_a_sverify_warning() -> None:
    names = [n for n in sverify.errors.__all__ if n.endswith("Warning")]
    assert sorted(c.__name__ for c in _public(SverifyWarning)) == sorted(names)
    assert issubclass(SverifyWarning, UserWarning)
    # The warnings of modules outside `sverify.errors` too (#881 1.8).
    importlib.import_module("sverify.odcs")
    importlib.import_module("sverify.openlineage")

    def subclasses(c: type) -> list[type]:
        return [s for d in c.__subclasses__() for s in (d, *subclasses(d))]

    ours = {c for c in subclasses(Warning) if c.__module__.startswith("sverify.")}
    assert ours and all(issubclass(c, SverifyWarning) for c in ours), ours


@sv.transform(ensures=[_.big > 100], on_unproved="warn")
def clipped(orders):
    return orders.select("id", big=orders.amount.clip(0, 10))


def test_on_unproved_warn_warns_with_the_report(tmp_path) -> None:
    orders = make_orders(tmp_path / "orders", [(1, "ada", 5)])
    with pytest.warns(UnprovedWarning, match=r"\(\.report has the details\)") as w:
        node = clipped(orders)
    warning = next(x.message for x in w if isinstance(x.message, UnprovedWarning))
    assert warning.report is node.report and warning.report.verdict == sv.Verdict.UNPROVED


# -- A5: the engines of 1.x -----------------------------------------------------


def test_the_engines_are_duckdb_polars_and_spark() -> None:
    from sverify import profiles

    runs = {e for e, p in profiles.plugins().items() if p.runner}
    assert runs == {"duckdb", "polars", "spark"}
    assert ENGINES == ("duckdb", "polars")
    with pytest.raises(ValueError, match=r"expected one of \('duckdb', 'polars'\)"):
        sv.connect("sqlite")  # type: ignore[arg-type]


# -- A6: ContractedTransform's constructor ---------------------------------------


def test_contracted_transform_takes_keywords() -> None:
    def f(t):
        return t

    with pytest.raises(TypeError):
        ContractedTransform(f, None, [], "error", True, None)  # type: ignore[misc]
    t = ContractedTransform(f, check_engine="polars", on_inferred="off")
    assert t.check_engine == "polars" and t.on_inferred == "off"
    assert not hasattr(t, "infer")


# -- J1: SVERIFY_CHECKER ----------------------------------------------------------


def test_the_old_environment_names_are_not_read(monkeypatch, tmp_path) -> None:
    from sverify import _checker, _duckdb

    monkeypatch.delenv("SVERIFY_CHECKER", raising=False)
    monkeypatch.setenv("SVERIFY_CHECK", str(tmp_path / "old"))
    monkeypatch.setattr(_checker, "__file__", str(tmp_path / "sverify" / "_checker.py"))
    with pytest.raises(
        FileNotFoundError
    ):  # the wheel's checker is not there, and `old` is not read
        _checker._checker_file()
    monkeypatch.setenv("SVERIFY_MEMORY_LIMIT", "1GB")
    monkeypatch.delenv("SVERIFY_TEMP_DIRECTORY", raising=False)
    monkeypatch.setenv("SVERIFY_SPILL_DIRECTORY", str(tmp_path))
    assert _duckdb.limits()["temp_directory"] != str(tmp_path)


def test_sverify_temp_directory_sets_duckdbs_temp_directory(monkeypatch, tmp_path) -> None:
    from sverify import _duckdb

    monkeypatch.setenv("SVERIFY_MEMORY_LIMIT", "1GB")
    monkeypatch.setenv("SVERIFY_TEMP_DIRECTORY", str(tmp_path))
    assert _duckdb.limits() == {"memory_limit": "1GB", "temp_directory": str(tmp_path)}


def test_result_dataclasses_are_keyword_only() -> None:
    """#881 1.5: a result or IO dataclass is built by keyword, so a field
    added in 1.x breaks no caller. `Report` and `Contract` are built by
    sverify alone; `Batch`, `Snapshot`, `SourceBatch` and `SinkWrite` by
    custom IO too."""
    import dataclasses

    from sverify.incremental import Snapshot, SourceBatch
    from sverify.io import Batch, Contract
    from sverify.io._common import SinkWrite

    for cls in (sv.Report, Contract, Batch, Snapshot, SourceBatch, SinkWrite):
        assert all(f.kw_only for f in dataclasses.fields(cls) if f.init), cls.__name__
