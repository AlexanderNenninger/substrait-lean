"""The shared decoder of Lean's written plans (`sverify._plan_read`)."""

import math

import pytest

from sverify import _plan_read as pr
from sverify.sql import Unsupported

#: Patterns where counting parentheses is easy to get wrong.
TRICKY = [
    ("abc", 1),
    ("(a)(b)", 2),
    (r"\(a\)", 1),
    (r"\\(a)", 1),
    (r"(\()", 1),
    ("(?:a)(b)", 1),
    ("(?:(a)|(b))+", 2),
    ("[(]a", 1),
    ("[^(](a)", 1),
    ("[]()](x)", 1),
    ("[^]()](x)", 1),
    (r"[\]()](x)", 1),
    ("((a)(b(c)))", 4),
    (r"(a\))", 1),
]


@pytest.mark.parametrize(("pattern", "groups"), TRICKY)
def test_regex_groups(pattern: str, groups: int) -> None:
    assert pr.regex_groups(pattern) == groups


@pytest.mark.parametrize(("pattern", "groups"), TRICKY)
def test_regex_groups_agree_with_polars(pattern: str, groups: int) -> None:
    """The SQL writer and Polars count with one definition, and it agrees
    with the `regex` crate's own count."""
    pl = pytest.importorskip("polars")
    from sverify.sql.core import regex_groups as sql_groups
    from sverify_polars.engine import regex_groups as polars_groups

    rust = pl.Series([""], dtype=pl.String).str.extract_groups(pattern).dtype
    assert isinstance(rust, pl.Struct)
    assert sql_groups(pattern) == polars_groups(pattern) == max(len(rust.fields), 1) == groups


@pytest.mark.parametrize("pattern", ["(?i)a", "(?P<x>a)", "(?=a)"])
def test_regex_groups_refuses_other_groups(pattern: str) -> None:
    """`Text.simpleRegex` accepts `(?:` and no other `(?`."""
    from sverify.sql.core import regex_groups

    with pytest.raises(Unsupported, match=r"\(\?"):
        regex_groups(pattern)


def test_invalid_pattern_on_polars() -> None:
    pytest.importorskip("polars")
    from sverify_polars.engine import regex_groups

    assert regex_groups("(a") is None


def test_function_names() -> None:
    plan = {
        "extensions": [
            {"extensionUriAnchor": {}},
            {"extensionFunction": {"functionAnchor": 1, "name": "add:i64_i64"}},
            {"extensionFunction": {"name": "equal:any_any"}},
            {"extensionFunction": {"functionAnchor": "1", "name": "later"}},
        ]
    }
    assert pr.function_names(plan) == {1: "add:i64_i64", 0: "equal:any_any"}
    assert pr.function_names({}) == {}
    with pytest.raises(Unsupported, match="missing field 'name'"):
        pr.function_names({"extensions": [{"extensionFunction": {}}]}, Unsupported)


def test_type_kind() -> None:
    assert pr.type_kind({"i32": {}}) == ("int", "i32")
    assert pr.type_kind({"precisionTimestamp": {"precision": 6}}) == ("time", 6)
    assert pr.type_kind({"precisionTime": {}}) == ("tod", 0)
    assert pr.type_kind({"decimal": {"precision": 10}}) == ("decimal", (10, 0))
    assert pr.type_kind({"list": {"type": {"string": {}}}}) == ("list", {"string": {}})
    assert pr.type_kind({"map": {}}) is None
    assert pr.type_kind(None) is None


def test_literal() -> None:
    assert pr.literal({"i8": 3}) == ("int", ("i8", 3))
    assert pr.literal({"i64": "-12"}) == ("int", ("i64", -12))
    assert pr.literal({"fp64": "-Infinity"}) == ("float", -math.inf)
    assert math.isnan(pr.literal({"fp64": "NaN"})[1])
    assert pr.literal({"precisionTime": {"precision": 9, "value": 5_000}}) == ("tod", 5)
    assert pr.literal({"precisionTimestamp": {"precision": 6, "value": "7"}}) == ("time", 7)
    compound = {"intervalYearToMonth": {"years": 1}, "intervalDayToSecond": {"days": 1}}
    assert pr.literal({"intervalCompound": compound}) == ("interval", (12, 86_400_000_000))
    # 1.5 as DECIMAL(2, 1): 15, little-endian two's complement.
    assert pr.literal(
        {"decimal": {"value": "DwAAAAAAAAAAAAAAAAAAAA==", "precision": 2, "scale": 1}}
    ) == (
        "decimal",
        (15, 2, 1),
    )
    with pytest.raises(Unsupported, match="unsupported literal"):
        pr.literal({"map": {}}, Unsupported)
    with pytest.raises(Unsupported, match="only microsecond"):
        pr.literal({"precisionTimestamp": {"precision": 3, "value": 1}}, Unsupported)


def test_interval_micros() -> None:
    assert pr.interval_micros({"days": 1, "seconds": 2, "subseconds": 3, "precision": 3}) == (
        86_402_003_000
    )
    assert pr.interval_micros({"subseconds": -1, "precision": 9}) == -1
