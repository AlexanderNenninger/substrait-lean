"""A column of a precision other than microseconds is refused by the checker (#2004): the model's
timestamps count microseconds, so a plan that compares `precision_timestamp(9)` with
`precision_timestamp(6)` would compare raw counts of different units."""

import json

import ibis
import pytest

from sverify._checker import run_checker
from sverify.ibis_substrait import to_substrait_json

T = ibis.table({"a": "timestamp", "b": "timestamp"}, name="t")


def _patched(precision: int, tag: str = "precisionTimestamp") -> str:
    plan = json.loads(to_substrait_json(T.filter(T.a > T.b)))

    # The first column of the table's schema.
    schema = next(iter(_reads(plan)))["baseSchema"]["struct"]["types"]
    schema[0][tag]["precision"] = precision
    return json.dumps(plan)


def _reads(x):
    if isinstance(x, dict):
        if "namedTable" in x:
            yield x
        for v in x.values():
            yield from _reads(v)
    elif isinstance(x, list):
        for v in x:
            yield from _reads(v)


def test_microseconds_are_read():
    code, _, err = run_checker((), _patched(6))
    assert code in (0, 4), err


@pytest.mark.parametrize("precision", [0, 3, 9])
def test_a_precision_other_than_microseconds_is_refused(precision):
    code, _, err = run_checker((), _patched(precision))
    assert code != 0 and "microseconds" in err, (code, err)
