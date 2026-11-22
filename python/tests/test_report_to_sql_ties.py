"""A window over ties and the SQL a report writes (#2325).

The default observation reads the rows as a multiset, so which of the tied
rows gets which number is open (`Rel.Allowed`): `to_sql` writes the window
without a row-order tiebreak for every dialect, and every engine's run is one
of the allowed results. Under `rows="sequence"` the numbering must follow the
input's order, which no dialect can promise, so `to_sql` refuses.
"""

import ibis
import pyarrow as pa
import pytest

import sverify as sv
from sverify.errors import RouteError, UnsupportedError

T = ibis.table({"k": "int64", "qty": "int64"}, name="t")
QUERY = "select k, row_number() over (partition by k order by qty) as rn from t"
DATA = pa.table({"k": [1, 1, 1, 2], "qty": [5, 5, 5, 7]})
DIALECTS = ["duckdb", "snowflake", "spark"]


@pytest.fixture(scope="module")
def report():
    r = sv.verify(QUERY, tables={"t": T})
    assert not r.deterministic  # the ties leave the numbering open
    return r


@pytest.mark.parametrize("dialect", DIALECTS)
def test_the_window_is_written_without_a_tiebreak(report, dialect):
    sql = report.to_sql(dialect)
    assert "ROW_NUMBER() OVER (PARTITION BY" in sql
    assert sql.count("ORDER BY") == 1  # the window's own key, no ordinal after it


@pytest.mark.parametrize("dialect", DIALECTS)
def test_a_sequence_of_ties_is_refused(dialect):
    sequence = sv.verify(QUERY, tables={"t": T}, ensures=[sv.equivalent(rows="sequence")])
    with pytest.raises((RouteError, UnsupportedError)):
        sequence.to_sql(dialect)


@pytest.mark.parametrize("engine", ["duckdb", "polars"])
def test_a_run_gives_one_allowed_numbering(report, engine):
    con = sv.connect()
    con.put("t", DATA)
    out = report.run(con, engine).to_pydict()
    by_key: dict[int, list[int]] = {}
    for k, rn in zip(out["k"], out["rn"], strict=True):
        by_key.setdefault(k, []).append(rn)
    assert {k: sorted(v) for k, v in by_key.items()} == {1: [1, 2, 3], 2: [1]}
