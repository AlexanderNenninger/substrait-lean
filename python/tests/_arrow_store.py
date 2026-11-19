"""A reference store for tests: state as Arrow tables in the process, merged by
`sverify._weighted.consolidated`. What the engines' stores are compared with."""

from __future__ import annotations

from typing import Any

import pyarrow as pa

from sverify._store import State, Store, arrow_of
from sverify._weighted import consolidated


class ArrowStore(Store[Any]):
    """A `Store` whose state is an Arrow table in the Python process."""

    def merge(
        self, plan: str, schema: pa.Schema, a: State, b: State, *, keep: bool
    ) -> State | pa.Table:
        return consolidated(arrow_of(a).cast(schema), arrow_of(b).cast(schema))
