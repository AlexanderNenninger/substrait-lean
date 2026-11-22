"""The proposer benchmark's theory classifier (`sverify_dev.proposer_bench`,
#2246): which theory a proposer needs for an obligation."""

from __future__ import annotations

import json
from dataclasses import asdict

import pytest

from sverify_dev import proposer_bench as pb
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


def test_pairs_lift(tmp_path):
    """A set of consecutive-line pairs over a DDL file, and one of JSON lines
    with their schema: a pair that lifts, one with a refused side, and a
    schema type with no Ibis type."""
    d = tmp_path / "sqlsolver_data"
    (d / "no_order_by").mkdir(parents=True)
    (d / "schemas").mkdir()
    (d / "schemas" / "tpcc.base.schema.sql").write_text(
        "CREATE TABLE `t` (`a` int not null, `b` varchar(10) null);"
    )
    (d / "no_order_by" / "tests_tpcc").write_text(
        "SELECT a FROM t WHERE a > 1\nSELECT a FROM t WHERE 1 < a\n"
        "SELECT a FROM t\nSELECT a, a FROM t\n"
    )
    (tmp_path / "benchmarks").mkdir()
    pair = {
        "schema": {"U": {"X": "INT", "Y": "NONE"}},
        "constraint": [{"not_null": {"value": "U__X"}}],
        "pair": ["SELECT X FROM U", "SELECT X FROM U"],
    }
    (tmp_path / "benchmarks" / "literature.jsonlines").write_text(json.dumps(pair) + "\n")
    sets = {s.name: s for s in pb.lift_pairs(tmp_path)}
    tpcc = sets["SQLSolver tpcc"]
    assert (tpcc.pairs, tpcc.both, tpcc.one, tpcc.neither) == (2, 1, 1, 0)
    assert tpcc.why == {"DUPLICATE OUTPUT COLUMN": 1}
    lit = sets["VeriEQL literature"]
    assert (lit.pairs, lit.neither) == (1, 1)
    assert lit.why == {"schema: column type NONE": 2}
    assert "| SQLSolver tpcc | 2 | 1 | 1 | 0 |" in pb.tables(
        {"pairs": [asdict(s) for s in sets.values()]}
    )
