"""The API review's sweep before 1.0 (#795, items 7, 8,
9 and 14): the 0.6 aliases removed (`test_api_06.py`), the engine lists of
1.x, the exception names, `SverifyWarning`, `SverifyError.code`, and the
environment variables. Each renamed released name warns for one release."""

import re
import warnings

import ibis
import pytest
from ibis import _

import sverify as sv
import sverify.engines
import sverify.errors
from _pipelines import make_orders
from sverify import engine as engine_module
from sverify.contracts import ContractedTransform
from sverify.engines import ENGINES
from sverify.errors import (
    InferredWarning,
    NotIncrementalError,
    SverifyError,
    SverifyWarning,
    UnprovedWarning,
    UnsupportedError,
)

# -- H1: names that end in Error ----------------------------------------------


@pytest.mark.parametrize(
    ("module", "old", "new"),
    [
        (sverify.errors, "Unsupported", UnsupportedError),
        (sverify.errors, "NotIncremental", NotIncrementalError),
        (sverify.engines, "Unsupported", UnsupportedError),
    ],
)
def test_the_old_exception_names_warn(module, old, new) -> None:
    with pytest.warns(DeprecationWarning, match=rf"{module.__name__}\.{old} is deprecated"):
        assert getattr(module, old) is new
    assert old not in module.__all__ and new.__name__ in module.__all__


def test_the_old_names_still_catch() -> None:
    with pytest.warns(DeprecationWarning):
        from sverify.errors import Unsupported
    with pytest.raises(Unsupported):
        sv.verify(
            "with recursive c as (select 1 as x) select * from c",
            tables={"t": ibis.schema({"x": "int64"})},
        )


def test_inferred_precondition_warning_is_inferred_warning() -> None:
    import sverify.contracts as contracts

    with pytest.warns(DeprecationWarning, match="InferredWarning"):
        assert contracts.InferredPreconditionWarning is InferredWarning


# -- H2 and H4: SverifyWarning and .code --------------------------------------


def _public(base: type) -> list[type]:
    return [
        c
        for n in sverify.errors.__all__
        if isinstance(c := getattr(sverify.errors, n), type) and issubclass(c, base)
    ]


def test_every_error_has_its_own_snake_case_code() -> None:
    errors = _public(SverifyError)
    assert len(errors) == 18
    codes = {c.code for c in errors if c is not SverifyError}
    assert len(codes) == len(errors) - 1
    assert all(re.fullmatch(r"[a-z]+(_[a-z]+)*", c) for c in codes), codes
    assert UnsupportedError.code == "unsupported"
    assert sverify.errors.UnverifiedRunError.code == "unverified_run"


def test_every_warning_is_a_sverify_warning() -> None:
    names = [n for n in sverify.errors.__all__ if n.endswith("Warning")]
    assert sorted(c.__name__ for c in _public(SverifyWarning)) == sorted(names)
    assert issubclass(SverifyWarning, UserWarning)


@sv.transform(ensures=[_.big > 100], on_unproved="warn")
def clipped(orders):
    return orders.select("id", big=orders.amount.clip(0, 10))


def test_on_unproved_warn_warns_with_the_report(tmp_path) -> None:
    orders = make_orders(tmp_path / "orders", [(1, "ada", 5)])
    with pytest.warns(UnprovedWarning, match=r"\(\.report has the details\)") as w:
        node = clipped(orders)
    warning = next(x.message for x in w if isinstance(x.message, UnprovedWarning))
    assert warning.report is node.report and not warning.report.proved


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


def test_sverify_check_is_sverify_checker(monkeypatch, tmp_path) -> None:
    monkeypatch.delenv("SVERIFY_CHECKER", raising=False)
    monkeypatch.setenv("SVERIFY_CHECK", str(tmp_path / "old"))
    with pytest.warns(DeprecationWarning, match="SVERIFY_CHECK is deprecated; set SVERIFY_CHECKER"):
        assert engine_module.checker_env() == str(tmp_path / "old")
    monkeypatch.setenv("SVERIFY_CHECKER", str(tmp_path / "new"))
    with warnings.catch_warnings():
        warnings.simplefilter("error", DeprecationWarning)
        assert engine_module.checker_env() == str(tmp_path / "new")


def test_sverify_temp_directory_sets_duckdbs_temp_directory(monkeypatch, tmp_path) -> None:
    from sverify import _duckdb

    monkeypatch.setenv("SVERIFY_MEMORY_LIMIT", "1GB")
    monkeypatch.setenv("SVERIFY_TEMP_DIRECTORY", str(tmp_path))
    assert _duckdb.limits() == {"memory_limit": "1GB", "temp_directory": str(tmp_path)}


def test_sverify_spill_directory_is_sverify_temp_directory(monkeypatch, tmp_path) -> None:
    from sverify import _duckdb

    monkeypatch.setenv("SVERIFY_MEMORY_LIMIT", "1GB")
    monkeypatch.delenv("SVERIFY_TEMP_DIRECTORY", raising=False)
    monkeypatch.setenv("SVERIFY_SPILL_DIRECTORY", str(tmp_path))
    with pytest.warns(DeprecationWarning, match="set SVERIFY_TEMP_DIRECTORY"):
        assert _duckdb.limits()["temp_directory"] == str(tmp_path)
