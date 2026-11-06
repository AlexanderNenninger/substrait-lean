"""A source's cursor as JSON, for the contracts a sink writes and the
quarantine table (#730: below both).

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release.
"""

from __future__ import annotations

import base64
import math
from datetime import date, datetime, time
from decimal import Decimal
from typing import Any

UNRECORDED = object()
"""A cursor that is not recorded: the source's cursors do not last, or
this one has no JSON form."""

_TAG = "$cursor"


def cursor_json(value: Any) -> Any:
    """`value` as JSON, for a contract: JSON's own values as they are, and
    datetimes, dates, times, decimals, bytes and tuples (and dicts with a
    key `"$cursor"`) as `{"$cursor": <type>, "value": ...}`. `UNRECORDED`
    if some part has no JSON form (a NaN, an object)."""
    if value is None or isinstance(value, bool | int | str):
        return value
    if isinstance(value, float):
        return value if math.isfinite(value) else UNRECORDED
    tagged: tuple[str, Any] | None = None
    if isinstance(value, datetime):
        tagged = ("datetime", value.isoformat())
    elif isinstance(value, date):
        tagged = ("date", value.isoformat())
    elif isinstance(value, time):
        tagged = ("time", value.isoformat())
    elif isinstance(value, Decimal):
        tagged = ("decimal", str(value))
    elif isinstance(value, bytes):
        tagged = ("bytes", base64.b64encode(value).decode())
    if tagged is not None:
        return {_TAG: tagged[0], "value": tagged[1]}
    if isinstance(value, list | tuple):
        items = [cursor_json(v) for v in value]
        if any(v is UNRECORDED for v in items):
            return UNRECORDED
        return items if isinstance(value, list) else {_TAG: "tuple", "value": items}
    if isinstance(value, dict) and all(isinstance(k, str) for k in value):
        out = {k: cursor_json(v) for k, v in value.items()}
        if any(v is UNRECORDED for v in out.values()):
            return UNRECORDED
        return {_TAG: "dict", "value": out} if _TAG in out else out
    return UNRECORDED


def cursor_value(data: Any) -> Any:
    """The cursor `cursor_json` encoded as `data`."""
    if isinstance(data, list):
        return [cursor_value(v) for v in data]
    if not isinstance(data, dict):
        return data
    if _TAG not in data:
        return {k: cursor_value(v) for k, v in data.items()}
    kind, value = data[_TAG], data["value"]
    if kind == "dict":
        return {k: cursor_value(v) for k, v in value.items()}
    if kind == "tuple":
        return tuple(cursor_value(v) for v in value)
    decode = {
        "datetime": datetime.fromisoformat,
        "date": date.fromisoformat,
        "time": time.fromisoformat,
        "decimal": Decimal,
        "bytes": base64.b64decode,
    }
    return decode[kind](value)
