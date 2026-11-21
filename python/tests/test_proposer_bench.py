"""The proposer benchmark's theory classifier (`sverify_dev.proposer_bench`,
#2246): which theory a proposer needs for an obligation."""

from __future__ import annotations

import pytest

from sverify_dev.proposer_bench import obligations, theory


@pytest.mark.parametrize(
    ("kind", "expr", "want"),
    [
        ("overflow", "DECIMAL_22_6((($6 * 10000) - $7))", "LIA"),
        ("overflow", "($1 * $2)", "NIA"),
        ("overflow", "(($1 + 1) * ($2 - 3))", "NIA"),
        ("division by zero", "($3 / ($1 - $2))", "NIA"),
        ("division by zero", "(DECIMAL_TO_DOUBLE_6($0) / DECIMAL_TO_DOUBLE_6($7))", "NIA"),
        ("division by zero", "(DECIMAL_TO_DOUBLE_6($0) / 2.5)", "LRA"),
        ("overflow to infinity", "($0 + $1)", "FP"),
        ("SUM overflow", "sum($4)", "LIA"),
        ("postcondition", "(_.name.upper() == 'A')", "strings"),
        ("cast out of range", "CAST(UPPER($1) AS BIGINT)", "strings"),
        ("overflow", "(my_box($1) + 1)", "UF"),
    ],
)
def test_theory(kind: str, expr: str, want: str) -> None:
    assert theory(kind, expr, frozenset({"my_box"})) == want


def test_obligations_read_a_report() -> None:
    out = {
        "ensures": [{"name": "(_.x >= 0)", "proved": True}, {"name": "(_.x < 9)", "proved": False}],
        "issues": [
            {"kind": "overflow", "expr": "($0 + 1)", "error": True, "bound": {"needs": [{}]}},
            {"kind": "overflow", "expr": "($0 * $1)", "error": True, "bound": {"why": "w"}},
            {"kind": "overflow", "expr": "($0 + 2)", "error": False},
        ],
        "epsilon": {"s": {"unbounded": True}, "t": {"unbounded": False}},
    }
    got = [(o.kind, o.theory, o.closed_by, o.why) for o in obligations("c", "p", out, frozenset())]
    assert got == [
        ("postcondition", "LIA", "", ""),
        ("overflow", "LIA", "infer", ""),
        ("overflow", "NIA", "", "w"),
        ("double bound", "FP", "", "no row bound on s"),
    ]
