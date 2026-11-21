"""A `CASE` around a nest of double comparisons runs on Polars in memory that
follows its input (#2210).

The plan Polars collects has no common-subexpression elimination
(`sverify_polars.engine._OPTIMIZATIONS`), so every copy of an operand an
expression names is computed. The lowering wrote a nested operand six times
per double comparison, and a `CASE` listed each issue of its branches once per
read, so the NULL guard of an ordering comparison of doubles took 5.8 GB on 64
rows. Each test runs in a process of its own and reads its peak resident set."""

import subprocess
import sys

import pytest

pytestmark = pytest.mark.backend("polars")

#: The peak, in MB, of a process that has imported sverify and run the plan.
#: The plan took over 5,000 MB before the fix and about 500 MB after.
LIMIT_MB = 1200

#: The comparison `x < y` of doubles as sverify's export writes it (NaN
#: greatest, one zero), under a NULL guard.
LT = "((NOT isnan(x) AND isnan(y)) OR (NOT isnan(x) AND NOT isnan(y) AND x + 0.0 < y + 0.0))"

SCRIPT = """
import resource, sys
import ibis
import sverify as sv
from sverify.engine import connect

schema = ibis.schema({"x": "float64", "y": "float64"})
rows = [(float(i % 5) if i % 7 else None, float(i % 3) if i % 11 else None) for i in range(64)]
report = sv.verify(sys.argv[1], tables={"t": schema})
con = connect()
con.create("t", schema, rows)
out = report.run(con, engine="polars").to_pylist()
peak = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
# ru_maxrss: bytes on macOS, KB on Linux.
print(len(out), peak // 2**20 if sys.platform == "darwin" else peak // 1024)
"""


def peak_mb(sql: str) -> tuple[int, int]:
    out = subprocess.run(
        [sys.executable, "-c", SCRIPT, sql], capture_output=True, text=True, check=True, timeout=300
    ).stdout.split()
    return int(out[0]), int(out[1])


@pytest.mark.parametrize(
    "sql",
    [
        "SELECT CASE WHEN x IS NULL OR y IS NULL THEN CAST(NULL AS BOOLEAN) "
        f"ELSE NOT {LT} END AS c FROM t",
        f"SELECT CASE WHEN x IS NULL THEN CAST(NULL AS BOOLEAN) ELSE {LT} END AS c FROM t",
    ],
    ids=["not", "plain"],
)
def test_a_case_over_double_comparisons_uses_memory_of_its_input(sql: str) -> None:
    rows, mb = peak_mb(sql)
    assert rows == 64
    assert mb < LIMIT_MB, f"peak {mb} MB"
