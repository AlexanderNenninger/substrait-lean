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


def test_row_counts_are_caps() -> None:
    be = "dbt_expectations.expect_table_row_count_to_be_between"
    assert conds(t(be, None, max_value=5)) == [sv.max_rows(5)]
    assert conds(t(be, None, min_value=0, max_value=5)) == [sv.max_rows(5)]
    low = mapping.test_conditions(
        t(be, None, min_value=1, max_value=5), side="ensures", table_of=lambda _: None
    )
    assert low.conditions == [] and "lower bound" in (low.reason or "")
    # an input's test: the cap holds whatever the lower bound is.
    assert conds(t(be, None, min_value=1, max_value=5), "requires") == [sv.max_rows(5)]
    # `strictly` makes the bounds exclusive: the cap is one lower, and a lower bound
    # of 0 is `count > 0`.
    assert conds(t(be, None, max_value=5, strictly=True)) == [sv.max_rows(4)]
    assert conds(t(be, None, max_value=5, strictly=True), "requires") == [sv.max_rows(4)]
    assert not conds(t(be, None, min_value=0, max_value=5, strictly=True))
    never = mapping.test_conditions(
        t(be, None, max_value=0, strictly=True), side="ensures", table_of=lambda _: None
    )
    assert never.conditions == [] and "always fails" in (never.reason or "")
    eq = "dbt_expectations.expect_table_row_count_to_equal"
    assert conds(t(eq, None, value=0)) == [sv.max_rows(0)]
    grouped = mapping.test_conditions(
        t(eq, None, value=1, group_by=["a"]), side="ensures", table_of=lambda _: None
    )
    assert "per group" in (grouped.reason or "")
    filtered = t(eq, None, value=1, row_condition="a > 0")
    assert not conds(filtered)


@pytest.mark.parametrize(
    ("kind", "kwargs", "cols", "holds"),
    [
        ("expect_table_columns_to_match_set", {"column_list": ["B", "a"]}, ["a", "b"], True),
        ("expect_table_columns_to_match_set", {"column_list": ["a"]}, ["a", "b"], False),
        (
            "expect_table_columns_to_match_ordered_list",
            {"column_list": ["a", "b"]},
            ["b", "a"],
            False,
        ),
        (
            "expect_table_columns_to_match_ordered_list",
            {"column_list": ["a", "b"]},
            ["A", "B"],
            True,
        ),
        ("expect_table_columns_to_contain_set", {"column_list": ["a"]}, ["a", "b"], True),
        ("expect_table_columns_to_not_contain_set", {"column_list": ["a"]}, ["a", "b"], False),
        ("expect_table_column_count_to_equal", {"value": 2}, ["a", "b"], True),
        ("expect_table_column_count_to_be_between", {"min_value": 3}, ["a", "b"], False),
        ("expect_column_to_exist", {"column_index": 2}, ["x", "c"], True),
        ("expect_column_to_exist", {"column_index": 1}, ["x", "c"], False),
        ("expect_column_to_exist", {"column_index": 0}, ["x", "c"], True),
        ("expect_column_to_exist", {"column_index": -3}, ["c", "x"], True),
        ("expect_table_column_count_to_be_between", {"max_value": 0}, ["a"], True),
    ],
)
def test_column_set_tests(kind: str, kwargs: dict, cols: list[str], holds: bool) -> None:
    got = mapping.test_conditions(
        t(f"dbt_expectations.{kind}", "c", **kwargs), side="ensures", table_of=lambda _: None
    )
    assert got.conditions == [] and got.schema is not None
    assert (got.schema(cols) is None) == holds


@pytest.mark.parametrize(
    "kind",
    [
        "dbt_utils.at_least_one",
        "dbt_utils.not_constant",
        "dbt_utils.equal_rowcount",
        "dbt_utils.equality",
    ],
)
def test_table_tests_without_a_condition_name_the_test(kind: str) -> None:
    got = mapping.test_conditions(t(kind, None), side="ensures", table_of=lambda _: None)
    assert got.conditions == [] and kind in (got.reason or "")


@pytest.mark.parametrize(
    ("test", "expected"),
    [
        (
            t("dbt_expectations.expect_column_values_to_match_regex", regex="^a.*"),
            "c IS NULL OR (regexp_matches(c, '^a.*'))",
        ),
        (
            t(
                "dbt_expectations.expect_column_values_to_not_match_regex_list",
                regex_list=["a", "b"],
            ),
            "c IS NULL OR (NOT (regexp_matches(c, 'a') AND regexp_matches(c, 'b')))",
        ),
        (
            t(
                "dbt_expectations.expect_column_values_to_not_match_like_pattern_list",
                like_pattern_list=["a%", "b%"],
                match_on="all",
            ),
            "c IS NULL OR (NOT (c LIKE 'a%' OR c LIKE 'b%'))",
        ),
        (
            t(
                "dbt_expectations.expect_column_value_lengths_to_be_between",
                min_value=2,
                max_value=4,
                strictly=True,
            ),
            "c IS NULL OR (length(c) > 2 AND length(c) < 4)",
        ),
        (
            t(
                "dbt_expectations.expect_column_values_to_match_like_pattern_list",
                like_pattern_list=["a%", "%z"],
                match_on="all",
            ),
            "c IS NULL OR (c LIKE 'a%' AND c LIKE '%z')",
        ),
        (
            t("dbt_expectations.expect_column_values_to_not_match_like_pattern", like_pattern="x_"),
            "c IS NULL OR (NOT (c LIKE 'x_'))",
        ),
        (
            t(
                "dbt_expectations.expect_column_value_lengths_to_be_between",
                min_value=2,
                max_value=4,
            ),
            "c IS NULL OR (length(c) >= 2 AND length(c) <= 4)",
        ),
        (
            t("dbt_expectations.expect_column_value_lengths_to_equal", value=3),
            "c IS NULL OR (length(c) = 3)",
        ),
        (t("dbt_utils.not_accepted_values", values=["a"]), "c IS NULL OR (c NOT IN ('a'))"),
        (t("dbt_utils.not_empty_string"), "c IS NULL OR (trim(c) <> '')"),
        (
            t(
                "dbt_expectations.expect_column_pair_values_A_to_be_greater_than_B",
                None,
                column_A="a",
                column_B="b",
                or_equal=True,
            ),
            "coalesce((a >= b), TRUE)",
        ),
        (
            t(
                "dbt_expectations.expect_column_pair_values_to_be_equal",
                None,
                column_A="a",
                column_B="b",
            ),
            "coalesce((a = b), TRUE)",
        ),
    ],
)
def test_string_and_pair_conditions(test: Test, expected: str) -> None:
    assert conds(test) == [expected]


@pytest.mark.parametrize(
    "test",
    [
        t("dbt_expectations.expect_column_values_to_match_regex", regex="a", flags="i"),
        t(
            "dbt_expectations.expect_column_values_to_match_regex_list",
            regex_list=["a"],
            match_on="x",
        ),
        t("dbt_expectations.expect_column_values_to_match_regex_list", regex_list=[]),
    ],
)
def test_string_refusals(test: Test) -> None:
    got = mapping.test_conditions(test, side="ensures", table_of=lambda _: None)
    assert got.conditions == [] and got.reason


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
            t("dbt_utils.unknown_test"), side="ensures", table_of=lambda _: None
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


@pytest.mark.parametrize(
    "source",
    ["read_csv('/no/such/file.csv')", "read_parquet('s3://bucket/x.parquet') p", "glob('*')"],
)
def test_rewrite_refuses_a_table_function_before_duckdb_binds_it(source: str) -> None:
    """A table function opens a file or URL when DuckDB plans it (#891 2.3):
    the refusal names it, and no DuckDB call has happened by then."""
    with pytest.raises(_Unreadable, match="a table function"):
        _rewrite(f"select * from {source}", {'"db"."main"."orders"': "orders"})


def test_rewrite_reads_a_series_function() -> None:
    assert "range" in _rewrite("select i from range(3) t(i)", {}).lower()


def test_needs_as_dbt_tests() -> None:
    """`Report.needs` gives the column, comparison and bound directly."""
    assert mapping.dbt_test("q", "IS NOT NULL", None, '"q" IS NOT NULL') == "not_null"
    assert mapping.dbt_test("q", ">=", "0", "") == (
        "dbt_utils.accepted_range: {arguments: {min_value: 0}}"
    )
    assert mapping.dbt_test("q", "<>", "0", '"q" IS NULL OR "q" <> 0') == (
        'dbt_utils.expression_is_true: {arguments: {expression: "\\"q\\" IS NULL OR \\"q\\" <> 0"}}'
    )


@pytest.mark.parametrize(
    "cond",
    [
        "c IS NULL OR (regexp_matches(c, '^a'))",
        "c IS NULL OR (c LIKE 'a%' OR c LIKE 'b%')",
        "c IS NULL OR (length(c) >= 2 AND length(c) <= 4)",
        "c IS NULL OR (trim(c) <> '')",
        "c IS NULL OR (NOT (c LIKE 'x'))",
    ],
)
def test_sverify_proves_a_test_it_is_given(cond: str) -> None:
    """The conditions are in the lift's subset: the same test upstream proves them."""
    report = sv.verify(
        "select c from t",
        tables={"t": {"c": "VARCHAR"}},
        semantics="duckdb",
        requires={"t": [cond]},
        ensures=[cond],
        on_inferred="error",
    )
    assert report.ensures[0].proved


def ranges(**kw) -> Test:
    return t("dbt_utils.mutually_exclusive_ranges", None, **kw)


def test_mutually_exclusive_ranges_on_plain_columns() -> None:
    """dbt-utils 1.4.1's macro fails a NULL bound and any row whose upper bound
    passes the next lower bound, so every variant implies sv.non_overlapping."""
    want = sv.non_overlapping("lo", "hi", by=("k",))
    for gaps in ("allowed", "not_allowed", "required"):
        test = ranges(lower_bound_column="lo", upper_bound_column="hi", partition_by="k", gaps=gaps)
        assert conds(test, "requires") == [want]
    both = ranges(lower_bound_column="lo", upper_bound_column="hi", partition_by="a, b")
    assert conds(both, "requires") == [sv.non_overlapping("lo", "hi", by=("a", "b"))]
    alone = ranges(lower_bound_column="lo", upper_bound_column="hi")
    assert conds(alone, "requires") == [sv.non_overlapping("lo", "hi")]


def test_mutually_exclusive_ranges_in_ensures_adds_the_rows_conditions() -> None:
    test = ranges(lower_bound_column="lo", upper_bound_column="hi", partition_by="k")
    assert conds(test) == [sv.non_overlapping("lo", "hi", by=("k",)), "hi IS NOT NULL", "lo < hi"]
    zero = ranges(lower_bound_column="lo", upper_bound_column="hi", zero_length_range_allowed=True)
    assert conds(zero)[2] == "lo <= hi"
    gapless = ranges(lower_bound_column="lo", upper_bound_column="hi", gaps="not_allowed")
    assert conds(gapless) == []


def test_an_open_end_needs_every_start_before_it() -> None:
    """`coalesce(hi, L)` reads a NULL end as L. A row starting at L or later
    could follow the open row, so the test implies the condition only with a
    test that `lo < L`."""
    end = "timestamp '9999-12-31'"
    test = ranges(
        lower_bound_column="lo", upper_bound_column=f"coalesce(hi, {end})", partition_by="k"
    )
    got = mapping.test_conditions(test, side="requires", table_of=lambda _: None)
    assert got.conditions == [] and "lo < CAST('9999-12-31' AS TIMESTAMP)" in (got.reason or "")
    want = [sv.non_overlapping("lo", "hi", by=("k",))]
    for sibling in [
        t("dbt_utils.expression_is_true", None, expression=f"lo < {end}"),
        t("dbt_utils.expression_is_true", "lo", expression=f"< {end}"),
        t("dbt_utils.accepted_range", "lo", max_value=end, inclusive=False),
    ]:
        assert conds(test, "requires", siblings=[sibling]) == want, sibling
    for other in [
        t("dbt_utils.accepted_range", "lo", max_value=end),  # lo <= L
        t("dbt_utils.expression_is_true", None, expression=f"hi < {end}"),
        t("dbt_utils.expression_is_true", None, expression="lo < timestamp '9999-12-30'"),
    ]:
        assert conds(test, "requires", siblings=[other]) == [], other
    assert conds(test) == []  # ensures: no column states the open end


@pytest.mark.parametrize(
    "kw",
    [
        {"lower_bound_column": "lo + 1", "upper_bound_column": "hi"},
        {"lower_bound_column": "lo", "upper_bound_column": "greatest(hi, lo)"},
        {"lower_bound_column": "lo", "upper_bound_column": "hi", "partition_by": "k || 'x'"},
    ],
)
def test_mutually_exclusive_ranges_on_expressions_are_not_mapped(kw: dict) -> None:
    got = mapping.test_conditions(ranges(**kw), side="requires", table_of=lambda _: None)
    assert got.conditions == [] and "dbt still runs it" in (got.reason or "")


def test_mutually_exclusive_ranges_with_where_is_not_mapped() -> None:
    test = ranges(lower_bound_column="lo", upper_bound_column="hi")
    test.where = "k > 0"
    assert conds(test, "requires") == []
