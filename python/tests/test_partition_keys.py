"""`check_keys` and `check_unique` (`sverify.partition`) group in Arrow. They
report what the loops they replaced did: the same verdict, and the same row
named in the message (#1447)."""

import math
import struct
from collections.abc import Mapping, Sequence

import pyarrow as pa
import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

from sverify.partition import check_keys, check_unique


def _key_value(v):
    """A key as Lean's `keyOf` has it: a double canonical (`canonV`), then by its bits."""
    if isinstance(v, float):
        return ("f", struct.pack("<d", math.nan if v != v else v + 0.0))
    return v


def old_check_keys(shards, keys):
    owner: dict[tuple, int] = {}
    for i, shard in enumerate(shards):
        for t, names in keys.items():
            columns = [shard[t].column(n).to_pylist() for n in names]
            for key in zip(*columns, strict=True):
                k = tuple(map(_key_value, key))
                j = owner.setdefault(k, i)
                if j != i:
                    raise ValueError(
                        f"split key {key} (columns {list(names)} of {t}) is on shards {j} and {i}"
                    )


def old_check_unique(tables, unique):
    for t, sets in unique.items():
        for names in sets:
            seen: set[tuple] = set()
            for piece in tables[t]:
                columns = [piece.column(n).to_pylist() for n in names]
                for key in zip(*columns, strict=True):
                    k = tuple(map(_key_value, key))
                    if k in seen:
                        raise ValueError(f"{t} has two rows with {list(names)} = {key}")
                    seen.add(k)


def _outcome(f, *args) -> str | None:
    try:
        f(*args)
    except ValueError as e:
        return str(e)
    return None


_INTS = st.one_of(st.none(), st.integers(0, 3))
_FLOATS = st.one_of(st.none(), st.sampled_from([0.0, -0.0, 1.5, math.nan, math.inf]))
_STRS = st.one_of(st.none(), st.sampled_from(["a", "b", ""]))
_ROW = st.tuples(_INTS, _FLOATS, _STRS)


def _table(rows: Sequence[tuple]) -> pa.Table:
    a, b, c = (list(col) for col in zip(*rows, strict=True)) if rows else ([], [], [])
    return pa.table(
        {
            "a": pa.array(a, pa.int64()),
            "b": pa.array(b, pa.float64()),
            "c": pa.array(c, pa.string()),
        }
    )


_TABLE = st.lists(_ROW, max_size=6).map(_table)
_NAMES = st.sampled_from([["a"], ["b"], ["c"], ["a", "b"], ["b", "c"], ["a", "b", "c"]])


@settings(max_examples=300, deadline=None)
@given(
    shards=st.lists(st.fixed_dictionaries({"t": _TABLE, "u": _TABLE}), max_size=4),
    names=_NAMES,
    both=st.booleans(),
)
def test_check_keys_reports_what_the_loop_did(shards, names, both):
    keys: Mapping[str, Sequence[str]] = {"t": names, "u": names} if both else {"t": names}
    assert _outcome(check_keys, shards, keys) == _outcome(old_check_keys, shards, keys)


@settings(max_examples=300, deadline=None)
@given(
    pieces=st.lists(_TABLE, max_size=4),
    sets=st.lists(_NAMES, min_size=1, max_size=2),
)
def test_check_unique_reports_what_the_loop_did(pieces, sets):
    tables, unique = {"t": pieces}, {"t": sets}
    assert _outcome(check_unique, tables, unique) == _outcome(old_check_unique, tables, unique)


def test_a_key_split_over_two_shards_names_the_first_row():
    t = _table([(1, 0.0, "a"), (2, 0.0, "a")])
    u = _table([(2, 0.0, "a"), (1, -0.0, "a")])
    shards = [{"t": t}, {"t": u}]
    with pytest.raises(ValueError, match=r"split key \(2, 0.0\) .* is on shards 0 and 1"):
        check_keys(shards, {"t": ["a", "b"]})


def test_signed_zeros_and_nans_are_one_key_as_keyof_has_them():
    """Lean's `keyOf` maps a double through `canonV`: one zero and one NaN (D31, #1519)."""
    nan = float("nan")
    t = _table([(None, 0.0, "a"), (None, nan, "a")])
    u = _table([(None, -0.0, "a"), (None, nan, "a")])
    with pytest.raises(ValueError, match="is on shards 0 and 1"):
        check_keys([{"t": t}, {"t": u}], {"t": ["a", "b"]})
    for a, b in ((0.0, -0.0), (nan, -nan)):
        with pytest.raises(ValueError, match="is on shards 0 and 1"):
            shards = [{"t": _table([(None, a, "a")])}, {"t": _table([(None, b, "a")])}]
            check_keys(shards, {"t": ["b"]})


def test_a_repeated_key_across_pieces_is_named():
    pieces = [_table([(1, 0.0, "a")]), _table([(2, 0.0, "a"), (1, 0.0, "b")])]
    with pytest.raises(ValueError, match=r"t has two rows with \['a'\] = \(1,\)"):
        check_unique({"t": pieces}, {"t": [["a"]]})
