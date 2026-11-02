"""Weighted tables (`sverify._weighted`): rows are equal as the model compares
them (`row_key`), whatever their Arrow types, and values come back unchanged."""

import math
from datetime import timedelta
from decimal import Decimal

import pyarrow as pa
import pytest

from sverify._weighted import (
    WEIGHT,
    consolidated,
    duplicate_keys,
    expanded,
    negated,
    weighted,
)
from sverify.incremental import _apply_change, arrow_rows, row_key, snapshot_diff


def z(rows: list[tuple], weights: list[int], schema: pa.Schema) -> pa.Table:
    t = pa.Table.from_pylist([dict(zip(schema.names, r, strict=True)) for r in rows], schema=schema)
    return t.append_column(WEIGHT, pa.array(weights, pa.int64()))


def pairs(t: pa.Table) -> list[tuple]:
    return [(r[:-1], r[-1]) for r in arrow_rows(t)]


DOUBLE = pa.schema([("x", pa.float64())])


def test_one_nan_and_one_zero():
    nan = float("nan")
    out = pairs(consolidated(z([(nan,), (nan,), (-0.0,), (0.0,), (1.0,)], [1, 1, 1, 1, 1], DOUBLE)))
    assert [(row_key(r), w) for r, w in out] == [(("NaN",), 2), ((0.0,), 2), ((1.0,), 1)]
    # The first row's value is kept: -0.0, not 0.0.
    assert math.copysign(1, out[1][0][0]) == -1


def test_weights_cancel_and_order_is_first_occurrence():
    s = pa.schema([("a", pa.int64()), ("b", pa.string())])
    t = z([(2, "b"), (1, None), (2, "b"), (1, None), (3, "c")], [1, 1, 1, -1, -2], s)
    assert pairs(consolidated(t)) == [((2, "b"), 2), ((3, "c"), -2)]


def test_lists_structs_and_types_round_trip():
    s = pa.schema(
        [
            ("l", pa.list_(pa.int64())),
            ("s", pa.struct([("k", pa.string())])),
            ("d", pa.decimal128(10, 2)),
            ("dur", pa.duration("us")),
            ("ts", pa.timestamp("us", tz="Europe/Berlin")),
        ]
    )
    row = ([1, None], {"k": "x"}, Decimal("1.25"), timedelta(seconds=3), None)
    out = consolidated(z([row, row], [1, 2], s))
    assert out.schema == pa.schema([*s, pa.field(WEIGHT, pa.int64())])
    assert pairs(out) == [(row, 3)]


def test_no_columns():
    t = pa.table({WEIGHT: pa.array([1, 2], pa.int64())})
    assert consolidated(t).column(WEIGHT).to_pylist() == [3]
    assert consolidated(weighted(pa.table({}), 1)).num_rows == 0


def test_expanded():
    s = pa.schema([("a", pa.int64())])
    assert arrow_rows(expanded(z([(1,), (2,), (3,)], [2, 0, 1], s))) == [(1,), (1,), (3,)]
    with pytest.raises(ValueError):
        expanded(z([(1,)], [-1], s))


def test_snapshot_diff_is_the_bag_difference():
    old = pa.table({"a": [1, 1, 2]})
    new = pa.table({"a": [1, 3, 3]})
    assert pairs(snapshot_diff(old, new)) == [((1,), -1), ((3,), 2), ((2,), -1)]


def test_apply_change_checks_deletes_first():
    s = pa.schema([("a", pa.int64())])
    current = pa.table({"a": [1, 1, 2]}, schema=s)
    change = z([(3,), (1,)], [1, -1], s)
    assert sorted(arrow_rows(_apply_change(current, change, "t"))) == [(1,), (2,), (3,)]
    # Inserting and deleting a row that is not there is still an error.
    with pytest.raises(ValueError, match=r"cannot delete \(4,\) from t"):
        _apply_change(current, z([(4,), (4,)], [1, -1], s), "t")


def test_negated():
    s = pa.schema([("a", pa.int64())])
    assert pairs(negated(z([(1,)], [2], s))) == [((1,), -2)]


def test_duplicate_keys_count_nulls_as_equal():
    t = pa.table({"k": [1, 1, 1, None, None, 2], "v": [0, 1, 2, 3, 4, 5]})
    assert duplicate_keys(t, ["k"]) == 3
    assert duplicate_keys(t, ["k"], pa.table({"k": [None, 2]})) == 1
    assert duplicate_keys(t, ["k", "v"]) == 0
