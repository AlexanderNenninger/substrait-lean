"""Cast rules of the Ibis producer: `CAST` and `TRY_CAST`.

Part of the Ibis producer (`sverify.ibis_substrait`), derived from
ibis-substrait (Apache License 2.0); `__init__.py` notes the changes.
"""

from __future__ import annotations

from typing import Any

import ibis.expr.operations as ops

from sverify.ibis_substrait._base import Exprs, register, same_type
from sverify.plan_json import Json, cast_json


def _cast(x: Exprs, op: Any) -> Json:
    if same_type(op.arg.dtype, op.to):
        return x(op.arg)
    return cast_json(x(op.arg), op.to)


def _try_cast(x: Exprs, op: Any) -> Json:
    """`TRY_CAST`: NULL where the cast fails (#58)."""
    if same_type(op.arg.dtype, op.to):
        return x(op.arg)
    return cast_json(x(op.arg), op.to, or_null=True)


register(
    {
        ops.Cast: _cast,
        ops.TryCast: _try_cast,
    }
)
