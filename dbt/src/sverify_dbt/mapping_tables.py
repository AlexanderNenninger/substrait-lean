"""dbt's table-level tests: a cap on the rows, the model's column names, and
the tests sverify has no condition for, each with its reason."""

from __future__ import annotations

from typing import TYPE_CHECKING, Any

import sverify as sv

from sverify_dbt.manifest import Test

if TYPE_CHECKING:
    from sverify_dbt.mapping import Mapped


def _mapped(*args: Any, **kwargs: Any) -> Mapped:
    from sverify_dbt.mapping import Mapped  # mapping imports this module

    return Mapped(*args, **kwargs)


_TWO = "it compares the row counts of two relations"
_TYPES = "it reads the table's types, which sverify-dbt checks as a contract"
_AGG = "it is an aggregate over the rows, and sverify proves no ratio of rows"
TABLE_LEVEL = {
    # test: why sverify has no condition for it
    "at_least_one": "it needs a lower bound on the rows, and sverify proves caps only",
    "not_constant": "it needs two distinct values, and sverify proves no lower bound",
    "not_null_proportion": _AGG,
    "recency": "it reads the clock and the newest row",
    "equal_rowcount": _TWO,
    "fewer_rows_than": _TWO,
    "equality": "it compares the rows of two relations",
    "cardinality_equality": "it compares the values of a column in two relations",
    "mutually_exclusive_ranges": "it compares the ranges of different rows",
    "sequential_values": "it compares each row with its neighbour",
    "expect_table_row_count_to_equal_other_table": _TWO,
    "expect_table_row_count_to_equal_other_table_times_factor": _TWO,
    "expect_table_aggregation_to_equal_other_table": "it compares aggregates of two relations",
    "expect_column_values_to_be_increasing": "it compares each row with its neighbour",
    "expect_column_values_to_be_decreasing": "it compares each row with its neighbour",
    "expect_column_distinct_count_to_equal": _AGG,
    "expect_column_distinct_count_to_be_greater_than": "it needs a lower bound on distinct values",
    "expect_column_distinct_count_to_be_less_than": "sverify proves no bound on a distinct count",
    "expect_column_values_to_be_of_type": _TYPES,
    "expect_column_values_to_be_in_type_list": _TYPES,
    "expect_table_row_count_to_equal": "",
    "expect_table_row_count_to_be_between": "",
    "expect_table_columns_to_match_ordered_list": "",
    "expect_table_columns_to_match_set": "",
    "expect_table_columns_to_contain_set": "",
    "expect_table_columns_to_not_contain_set": "",
    "expect_table_column_count_to_equal": "",
    "expect_table_column_count_to_be_between": "",
    "expect_column_to_exist": "",
}


def table_level(test: Test, base: str, side: str, row_filter: str | None) -> Mapped:
    """A test on the table: a cap on its rows, a test of its column names, or
    why sverify has no condition for it."""
    why = TABLE_LEVEL[base]
    if why:
        return _mapped([], f"{test.kind}: {why}; dbt still runs it")
    kw = test.kwargs
    if base.startswith("expect_table_row_count"):
        return _row_count(test, base, side, row_filter)
    if side == "requires":
        return _mapped([])  # an input's column names are no precondition
    transform = str(kw.get("transform", "upper"))
    fold = {"upper": str.upper, "lower": str.lower, "": str}.get(transform)
    if fold is None:
        return _mapped([], f"the transform {transform!r} is not upper or lower")
    want = [fold(c) for c in _as_list(kw.get("column_list"))]
    n_min, n_max = kw.get("min_value"), kw.get("max_value")

    def check(cols: list[str]) -> str | None:
        have = [fold(c) for c in cols]
        if base == "expect_table_columns_to_match_ordered_list":
            ok = have == want
        elif base == "expect_table_columns_to_match_set":
            ok = set(have) == set(want)
        elif base == "expect_table_columns_to_contain_set":
            ok = set(want) <= set(have)
        elif base == "expect_table_columns_to_not_contain_set":
            ok = not set(want) & set(have)
        elif base == "expect_table_column_count_to_equal":
            ok = len(cols) == kw.get("value")
        elif base == "expect_table_column_count_to_be_between":
            ok = (n_min is None or len(cols) >= n_min) and (n_max is None or len(cols) <= n_max)
        else:  # expect_column_to_exist
            name = fold(str(test.column or kw.get("column_name") or ""))
            idx = kw.get("column_index")
            ok = name in have and (idx is None or have.index(name) == int(idx) - 1)
        return None if ok else f"the model's columns are {', '.join(cols)}"

    return _mapped([], schema=check)


def _as_list(v: Any) -> list[Any]:
    return list(v) if isinstance(v, list | tuple) else ([] if v is None else [v])


def _row_count(test: Test, base: str, side: str, row_filter: str | None) -> Mapped:
    """`expect_table_row_count_to_equal` and `…_to_be_between` as a cap
    (`sv.max_rows`): the upper bound is what sverify proves, and what a test
    on an input lets it assume. A lower bound above 0 has no proof."""
    kw = test.kwargs
    if kw.get("group_by"):
        return _mapped([], "a row count per group has no sverify condition; dbt still runs it")
    if row_filter:
        return _mapped([], "the count of a filtered set of rows is no cap on the table")
    if base.endswith("equal"):
        lo = hi = kw.get("value")
    else:
        lo, hi = kw.get("min_value"), kw.get("max_value")
    if side == "requires":
        return _mapped([sv.max_rows(int(hi))] if hi is not None else [])
    if lo is not None and lo > 0:
        return _mapped(
            [], f"a lower bound of {lo} rows: sverify proves caps on rows only; dbt still runs it"
        )
    if hi is None:
        return _mapped([], "the test has no upper bound on the rows")
    return _mapped([sv.max_rows(int(hi))])
