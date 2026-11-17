"""Key equality for the glue around the engines (D31, #1511, #1519).

A key is an identity boundary: Lean's `keyOf` maps each value through `canonV`,
so `-0.0` is `0.0`, every NaN is one NaN, and NULL is a key of its own. Only
flat double columns are canonicalised here; `canonV` also reaches into lists and
structs, which pyarrow cannot encode as keys at all. pyarrow
groups and encodes doubles by their bits, so every place in sverify that
matches keys through pyarrow canonicalises the key columns here first. The
stored values stay raw: only the copy a key is matched on changes.
"""

from __future__ import annotations

from collections.abc import Sequence

import pyarrow as pa
import pyarrow.compute as pc


def canonical_key(a: pa.Array | pa.ChunkedArray) -> pa.Array | pa.ChunkedArray:
    """A key column with `-0.0` as `0.0` and every NaN as one NaN (NULL stays NULL);
    any other column as it is."""
    if not pa.types.is_floating(a.type):
        return a
    one_nan = pa.scalar(float("nan"), a.type)
    plus = pc.call_function("add", [a, pa.scalar(0.0, a.type)])  # -0.0 + 0.0 is 0.0
    return pc.call_function("if_else", [pc.call_function("is_nan", [a]), one_nan, plus])


def canonical_keys(table: pa.Table, names: Sequence[str]) -> pa.Table:
    """`table` with the key columns `names` canonical, for a grouping or a join on them."""
    for n in names:
        i = table.schema.get_field_index(n)
        if pa.types.is_floating(table.schema.field(i).type):
            table = table.set_column(i, table.schema.field(i), canonical_key(table.column(i)))
    return table
