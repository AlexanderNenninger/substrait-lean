"""Tests and constraints as conditions, and the compiled SQL's rewrite."""

from __future__ import annotations

import pytest
import sverify as sv

from sverify_dbt import mapping
from sverify_dbt.check import _rewrite, _Unreadable
from sverify_dbt.manifest import Test


def t(kind: str, column: str | None = "c", **kwargs) -> Test:
    return Test("test.p.x", "x", kind, kwargs, "model.p.m", column, ["model.p.m"])


def conds(test: Test, side: str = "ensures", **kw) -> list:
    return mapping.test_conditions(test, side=side, table_of=lambda _: None, **kw).conditions


@pytest.mark.parametrize(
    ("test", "expected"),
    [
        (t("not_null"), "c IS NOT NULL"),
        (t("accepted_values", values=["a", "it's"]), "c IS NULL OR (c IN ('a', 'it''s'))"),
        (t("accepted_values", values=[1, 2], quote=False), "c IS NULL OR (c IN (1, 2))"),
        (t("dbt_utils.accepted_range", min_value=0), "c IS NULL OR (c >= 0)"),
        (
            t("dbt_utils.accepted_range", min_value=0, max_value=9, inclusive=False),
            "c IS NULL OR (c > 0 AND c < 9)",
        ),
        (
            t("dbt_expectations.expect_column_values_to_be_between", max_value=5, strictly=True),
            "c IS NULL OR (c < 5)",
        ),
        (
            t("dbt_expectations.expect_column_values_to_be_in_set", value_set=["x"]),
            "c IS NULL OR (c IN ('x'))",
        ),
        (
            t("dbt_expectations.expect_column_values_to_not_be_in_set", value_set=["x"]),
            "c IS NULL OR (c NOT IN ('x'))",
        ),
        (t("dbt_utils.expression_is_true", None, expression="a > b"), "coalesce((a > b), TRUE)"),
        (t("dbt_utils.expression_is_true", expression="> 0"), "coalesce((c > 0), TRUE)"),
        (
            t(
                "dbt_expectations.expect_column_values_to_be_between",
                min_value=1,
                row_condition="kind = 'a'",
            ),
            "NOT coalesce((kind = 'a'), FALSE) OR (c IS NULL OR (c >= 1))",
        ),
    ],
)
def test_row_conditions(test: Test, expected: str) -> None:
    assert conds(test) == [expected]


def test_where_config_filters_the_rows() -> None:
    test = t("not_null")
    test.where = "status = 'live'"
    assert conds(test) == ["NOT coalesce((status = 'live'), FALSE) OR (c IS NOT NULL)"]


def test_quoted_columns() -> None:
    assert conds(t("not_null", "Order Id")) == ['"Order Id" IS NOT NULL']


def test_unique_needs_not_null_to_be_assumed() -> None:
    """dbt's unique lets NULLs repeat; sv.unique counts them as one key."""
    test = t("unique")
    assert conds(test) == [sv.unique("c")]
    got = mapping.test_conditions(test, side="requires", table_of=lambda _: None)
    assert got.conditions == [] and "not_null" in (got.reason or "")
    assert conds(test, "requires", not_null={"c"}) == [sv.unique("c")]
    combo = t("dbt_utils.unique_combination_of_columns", None, combination_of_columns=["a", "b"])
    assert conds(combo, "requires") == [sv.unique("a", "b")]


def test_relationships() -> None:
    test = Test(
        "test.p.r",
        "r",
        "relationships",
        {"to": "ref('o')", "field": "id"},
        "model.p.i",
        "oid",
        ["model.p.o", "model.p.i"],
    )
    names = {"model.p.o": "o"}
    got = mapping.test_conditions(test, side="requires", table_of=names.get)
    assert got.conditions == [sv.references("oid", to=("o", "id"))]
    assert not mapping.test_conditions(test, side="requires", table_of=lambda _: None).conditions
    assert "foreign keys" in (
        mapping.test_conditions(test, side="ensures", table_of=names.get).reason or ""
    )


def test_unmapped() -> None:
    assert "no mapping" in (
        mapping.test_conditions(
            t("dbt_utils.at_least_one"), side="ensures", table_of=lambda _: None
        ).reason
        or ""
    )
    assert "singular" in (
        mapping.test_conditions(
            Test("test.p.s", "s", None, {}, None, None, []), side="ensures", table_of=lambda _: None
        ).reason
        or ""
    )


def test_constraints() -> None:
    pk = mapping.constraint_conditions({"type": "primary_key"}, "id")
    assert pk.conditions == ["id IS NOT NULL", sv.unique("id")]
    check = mapping.constraint_conditions({"type": "check", "expression": "x > 0"}, None)
    assert check.conditions == ["coalesce((x > 0), TRUE)"]
    model_pk = mapping.constraint_conditions({"type": "primary_key", "columns": ["a", "b"]}, None)
    assert model_pk.conditions == ["a IS NOT NULL", "b IS NOT NULL", sv.unique("a", "b")]
    assert not mapping.constraint_conditions({"type": "foreign_key"}, "id").conditions


@pytest.mark.parametrize(
    ("sql", "expected"),
    [
        (
            '"qty" IS NULL OR "qty" < 9000000000000000000',
            (
                "qty",
                "dbt_utils.accepted_range: {arguments: {max_value: 9000000000000000000, "
                "inclusive: false}}",
            ),
        ),
        (
            '"x" IS NULL OR "x" >= -5',
            ("x", "dbt_utils.accepted_range: {arguments: {min_value: -5}}"),
        ),
        (
            "a + b < 3",
            (None, 'dbt_utils.expression_is_true: {arguments: {expression: "a + b < 3"}}'),
        ),
    ],
)
def test_needed_as_dbt_tests(sql: str, expected: tuple) -> None:
    assert mapping.as_dbt_test(sql) == expected


def test_rewrite_reads_inputs_by_name() -> None:
    sql = (
        'with x as (select * from "db"."main"."orders" where a > 0) '
        'select o.a, orders.b from x join "db"."main"."orders" as o on true '
        'join "db"."main"."orders" on true'
    )
    out = _rewrite(sql, {'"db"."main"."orders"': "raw_orders"})
    assert '"db"' not in out
    assert 'FROM "raw_orders" AS orders WHERE' in out
    assert 'JOIN "raw_orders" AS o' in out
    assert "FROM x" in out


def test_rewrite_refuses_unknown_tables() -> None:
    with pytest.raises(_Unreadable, match="no ref or source"):
        _rewrite('select * from "db"."main"."other"', {'"db"."main"."orders"': "orders"})


def test_needs_as_dbt_tests() -> None:
    """`Report.needs` gives the column, comparison and bound directly."""
    assert mapping.dbt_test("q", "IS NOT NULL", None, '"q" IS NOT NULL') == "not_null"
    assert mapping.dbt_test("q", ">=", "0", "") == (
        "dbt_utils.accepted_range: {arguments: {min_value: 0}}"
    )
    assert mapping.dbt_test("q", "<>", "0", '"q" IS NULL OR "q" <> 0') == (
        'dbt_utils.expression_is_true: {arguments: {expression: "\\"q\\" IS NULL OR \\"q\\" <> 0"}}'
    )
