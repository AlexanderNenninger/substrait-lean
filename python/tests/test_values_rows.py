"""The rows of a `virtualTable` (`VALUES`) are checked as plans are (#1491).

The parser used to evaluate each row with the total evaluator at parse time,
so an overflow or a zero divisor in a computed row vanished from the safety
analysis, and it never compared a cell or a literal with its declared type, so
`--write` could emit a plan no consumer accepts. A hand-written plan reaches
this through `substrait-check` and `sverify.from_substrait`.
"""

import json

import pytest

from sverify._unsupported import UnsupportedError
from sverify.engine import written_plan

N = {"nullability": "NULLABILITY_NULLABLE"}


def _lit(kind: str, v: object) -> dict:
    return {"literal": {kind: v}}


def _call(fn: str, a: dict, b: dict) -> dict:
    return {
        "scalarFunction": {
            "functionReference": 1,
            "outputType": {"i64": N},
            "arguments": [{"value": a}, {"value": b}],
        }
    }


def _values(row: dict, fn: str = "add:i64_i64", ty: dict | None = None) -> str:
    """A plan reading one `VALUES` row into a single column of type `ty`."""
    ty = ty or {"i64": N}
    return json.dumps(
        {
            "extensions": [{"extensionFunction": {"functionAnchor": 1, "name": fn}}],
            "relations": [
                {
                    "root": {
                        "names": ["c0"],
                        "input": {
                            "read": {
                                "baseSchema": {"names": ["c0"], "struct": {"types": [ty]}},
                                "virtualTable": {"expressions": [{"fields": [row]}]},
                            }
                        },
                    }
                }
            ],
        }
    )


I64_MAX = 2**63 - 1

#: Plans no consumer accepts or whose rows would raise: the parser refuses each.
REFUSED = {
    "overflowing row": _values(_call("add:i64_i64", _lit("i64", str(I64_MAX)), _lit("i64", "1"))),
    "zero divisor in a row": _values(
        _call("divide:i64_i64", _lit("i64", "1"), _lit("i64", "0")), "divide:i64_i64"
    ),
    "string in an i64 column": _values(_lit("string", "abc")),
    "i64 literal past 64 bits": _values(_lit("i64", "99999999999999999999")),
    "i32 cell past 32 bits": _values(_lit("i32", 5000000000), ty={"i32": N}),
}


@pytest.mark.parametrize("case", REFUSED)
def test_a_values_row_that_raises_or_misses_its_type_is_refused(case):
    with pytest.raises(UnsupportedError):
        written_plan(REFUSED[case])


def test_a_row_that_fits_its_type_is_written_back_with_its_type():
    plan = _values(_lit("i32", 7), ty={"i32": N})
    assert json.loads(written_plan(plan))["relations"][0]["root"]["input"]["read"]["baseSchema"][
        "struct"
    ]["types"] == [{"i32": N}]
