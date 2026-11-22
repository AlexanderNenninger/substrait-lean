"""The SQL sverify writes stays within `sverify_dev.plan_size.BOUND` of the
plan it was given, for every verified coverage case and catalogue query, in
every SQL dialect (#821)."""

from _repo import needs_repo
from sverify_dev.plan_size import BOUND, over, plan_nodes, plan_windows, sizes, sql_size, sql_sorts


@needs_repo
def test_written_sql_is_bounded():
    ss = sizes()
    assert len({s.dialect for s in ss}) == 3
    bad = [f"{s.source} {s.label} ({s.dialect}): {'; '.join(w)}" for s in ss if (w := over(s))]
    assert not bad, f"over {BOUND}:\n" + "\n".join(bad)


def test_measures():
    plan = {"relations": [{"root": {"input": {"project": {
        "input": {"read": {"baseSchema": {"names": ["a", "b"]}}},
        "expressions": [{"scalarFunction": {"arguments": [
            {"value": {"selection": {}}}, {"value": {"literal": {"i64": "1"}}}]}}],
    }}}}]}  # fmt: skip
    # project, read, its two columns, the call and its two arguments
    assert plan_nodes(plan) == 7
    tokens, depth = sql_size("SELECT CASE WHEN a THEN CASE WHEN b THEN 1 END END FROM t", "duckdb")
    assert depth == 2
    assert tokens == 14


def test_sorts_and_windows():
    assert sql_sorts("SELECT ROW_NUMBER() OVER (ORDER BY a) FROM t ORDER BY b", "duckdb") == (2, 1)
    window = {"windowFunction": {"sorts": [{}]}}
    rel = {"window": {"windowFunctions": [{}, {}]}}
    assert plan_windows({"project": {"expressions": [window, window]}, "input": rel}) == 4
