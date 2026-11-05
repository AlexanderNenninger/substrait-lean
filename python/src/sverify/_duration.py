"""Durations: a `timedelta`, or an ISO 8601 duration string (`"PT15M"`,
`"P1D"`, `"P2W"`), as every duration parameter takes them (API review L6).
Years and months have no fixed length, so they are refused."""

from __future__ import annotations

import re
from datetime import timedelta

Duration = timedelta | str
"""A `timedelta`, or an ISO 8601 duration such as `"PT15M"` or `"P1DT12H"`."""

_ISO = re.compile(
    r"P(?:(?P<weeks>\d+(?:\.\d+)?)W)?(?:(?P<days>\d+(?:\.\d+)?)D)?"
    r"(?:T(?:(?P<hours>\d+(?:\.\d+)?)H)?(?:(?P<minutes>\d+(?:\.\d+)?)M)?"
    r"(?:(?P<seconds>\d+(?:\.\d+)?)S)?)?"
)


def duration(value: Duration, what: str = "a duration") -> timedelta:
    """`value` as a `timedelta`.

    Raises:
        ValueError: A string that is not an ISO 8601 duration of weeks,
            days, hours, minutes and seconds.
        TypeError: Neither a `timedelta` nor a string.
    """
    if isinstance(value, timedelta):
        return value
    if not isinstance(value, str):
        raise TypeError(f"{what} is a timedelta or an ISO 8601 string, not {value!r}")
    m = _ISO.fullmatch(value.strip().upper())
    if m is None or value.strip().upper() in ("P", "PT") or value.strip().upper().endswith("T"):
        raise ValueError(
            f"{what} {value!r} is not an ISO 8601 duration of weeks, days, hours, minutes "
            'and seconds, such as "PT15M" or "P1DT12H" (years and months have no fixed length)'
        )
    return timedelta(**{k: float(v) for k, v in m.groupdict().items() if v is not None})
