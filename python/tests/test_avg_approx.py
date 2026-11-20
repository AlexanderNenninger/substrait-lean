"""A lifted integer mean carries D52's mark (#1608 12d-4, #1735).

Under `semantics="duckdb"`, `AVG` of integers is written as the plan states it,
and DuckDB's own `avg` of integers, which dbt and the SQL-file CLI run, returns a
double within a band of that value. The plan is proved only where every decision
that reads the mean has one outcome over the band and every output column that
reads it has a bound in `Report.epsilon`; elsewhere the report holds an error
(ruling 104). 12b-2 turns the comparisons of the mean with integers back into
proved ones."""

import pyarrow as pa
import pytest

import sverify as sv
from sverify.errors import UnverifiedRunError

T = {"t": pa.schema([("k", pa.int64()), ("x", pa.int64()), ("d", pa.float64())])}
#: `x` is in [0, 1e7], `d` in [-1e7, 1e7]: a mean is in [0, 1e7]; 1e6 rows at most.
REQUIRES = {
    "t": [
        "x IS NULL OR x BETWEEN 0 AND 10000000",
        "d IS NULL OR d BETWEEN -10000000 AND 10000000",
        sv.max_rows(1_000_000),
    ]
}
#: The issue's kind, as the checker names it (one name in Lean, JSON, Python and docs).
KIND = "source_threshold"


def verified(sql: str):
    return sv.verify(sql, tables=T, requires=REQUIRES, semantics="duckdb", on_inferred="warn")


def refused(report) -> bool:
    return report.verdict == "unproved" and any(i.kind == KIND for i in report.errors)


#: #1735: a group of 88,085 rows with sum 378693551270 has the mean
#: 0x1.0666bcc2506abp+22 in the plan, and DuckDB's grouped `avg` on x86-64 Linux gives
#: 0x1.0666bcc2506acp+22; a threshold between them keeps the group in one and not the other.
EDGE = "SELECT k FROM t GROUP BY k HAVING AVG(x) < 4299183.1897598915"


def test_the_issue_1735_threshold_is_refused():
    report = verified(EDGE)
    assert refused(report)
    with pytest.raises(UnverifiedRunError):
        report.to_sql("duckdb")


@pytest.mark.parametrize(
    "sql",
    [
        # The mean against a double column and an integer column (ruling 92's S2).
        "SELECT k FROM t WHERE d > (SELECT AVG(x) FROM t)",
        "SELECT k FROM t WHERE x > (SELECT AVG(x) FROM t)",
        # Taint (ruling 104, item 4): the mean read through other operators.
        "SELECT k FROM t GROUP BY k HAVING AVG(x) * 2 < 4299183.18",
        "SELECT k FROM (SELECT k, AVG(x) AS m FROM t GROUP BY k) WHERE m < 4299183.18",
        "SELECT a.k FROM (SELECT k, AVG(x) AS m FROM t GROUP BY k) a JOIN t ON t.d = a.m",
        "SELECT m, COUNT(*) AS n FROM (SELECT k, AVG(x) AS m FROM t GROUP BY k) GROUP BY m",
        "SELECT AVG(x) < 4299183.18 AS flag FROM t",
        "SELECT k, AVG(x) AS m FROM t GROUP BY k ORDER BY m",
        # Over-refused, soundly (ruling 108): the lifted mean's abstract range is the
        # sum's over the count's (about +-1e13), not the values' [0, 1e7], so the band
        # straddles 2e7. The `ratioSharpen` follow-up for `fdiv(itof s, itof c)` proves it.
        "SELECT k FROM t GROUP BY k HAVING AVG(x) < 20000000",
    ],
)
def test_a_decision_on_the_mean_without_one_outcome_over_the_band_is_refused(sql):
    report = verified(sql)
    assert refused(report), (report.verdict, [str(e) for e in report.errors])


@pytest.mark.parametrize(
    "sql",
    [
        # The threshold lies beyond the lifted quotient's abstract range: the sum is in
        # [0, 1e13] and the count in [1, 1e6], so the quotient is in [0, 1e13], and the
        # band does not reach 2e13: one outcome.
        "SELECT k FROM t GROUP BY k HAVING AVG(x) < 20000000000000",
        # No decision reads the mean.
        "SELECT k, SUM(x) AS s, COUNT(x) AS n FROM t GROUP BY k",
    ],
)
def test_a_decision_the_band_does_not_straddle_stays_proved(sql):
    report = verified(sql)
    assert report.verdict == "proved", [str(e) for e in report.errors]


def test_the_plain_mean_is_proved_with_its_band_in_the_report():
    report = verified("SELECT k, AVG(x) AS m FROM t GROUP BY k")
    assert report.verdict == "proved", ([str(e) for e in report.errors], report.unproved)
    band = report._epsilon["m"]["bounds"]["abs"]
    # Sound and loose: the band is over the quotient's range (+-1e13), 17 * 2^-53 of it.
    assert band["proved"] and 0 < band["value"] < 1e-1


def test_the_reference_lift_has_no_mark():
    """The reference's mean is the engines' common one (12b-1): no band, no refusal."""
    report = sv.verify(EDGE, tables=T, requires=REQUIRES, semantics="portable", on_inferred="warn")
    assert not any(i.kind == KIND for i in report.errors)


#: A key needs a column the mean does not taint (ruling 108, C-key).
GROUPED = "SELECT k, AVG(x) AS m FROM t GROUP BY k"


@pytest.mark.parametrize("cols", [["k"], ["k", "m"]])
def test_a_key_with_an_untainted_subset_stays_proved(cols):
    report = sv.verify(
        GROUPED,
        tables=T,
        requires=REQUIRES,
        ensures=[sv.unique(*cols)],
        semantics="duckdb",
        on_inferred="warn",
    )
    assert report.verdict == "proved", [str(e) for e in report.errors]


def test_a_key_on_the_mean_alone_is_refused():
    report = sv.verify(
        f"SELECT DISTINCT m FROM ({GROUPED})",
        tables=T,
        requires=REQUIRES,
        ensures=[sv.unique("m")],
        semantics="duckdb",
        on_inferred="warn",
    )
    assert refused(report)
    exprs = [i.expr for i in report.errors if i.kind == KIND]
    assert "DISTINCT" in exprs and any(e.startswith("the key") for e in exprs), exprs


def test_a_postcondition_at_the_edge_of_the_mean_is_refused():
    """DuckDB's mean may lie a band below 0 (ruling 104, C-contract). The robust
    check widens the column's abstract value by the band and reads no fact, so a
    postcondition a band's width away is refused as well: sound, and loose."""
    report = sv.verify(
        GROUPED,
        tables=T,
        requires=REQUIRES,
        ensures=["m >= 0"],
        semantics="duckdb",
        on_inferred="warn",
    )
    assert refused(report)
    assert any(i.expr.startswith("the postcondition") for i in report.errors if i.kind == KIND)


# --- Ruling 197: a SUM inside its type is exact on every engine -----------------
#
# A `SUM` whose argument's range and proved row cap keep it inside its type
# (`Measure.sumFits`: 64 bits for integers, the result's precision for decimals)
# is outside the `overflow` option's scope (D34), so its value is the reference's on
# every engine. The report's `epsilon` holds no integer or decimal column, and a
# double aggregate's flag reads only the aggregate's own input. A column that reads
# a lifted mean (D52) has its flag from the whole plan (`colEps`): a filter on the
# sum keeps the mean's band proved only where the filter's condition is proved exact
# on every engine (`keepIf`). The mean's own `SUM(x)` fits 64 bits at every cap here
# (1e11 * 1e7 = 1e18 <= 2^63 - 1).

TS = {
    "t": pa.schema(
        [("k", pa.int64()), ("x", pa.int64()), ("c", pa.decimal128(5, 2)), ("d", pa.float64())]
    )
}
RANGES = ["x IS NULL OR x BETWEEN 0 AND 10000000", "d IS NULL OR d BETWEEN -10000000 AND 10000000"]


def _abs_bound(report, col: str) -> dict:
    """The column's absolute bound in the report's `epsilon`, `{}` where it has none."""
    eps = report._epsilon or {}
    return ((eps.get(col) or {}).get("bounds") or {}).get("abs") or {}


def _sum_proved(arg: str, cap: int) -> bool:
    """Is a filter on `SUM(arg)` proved exact? Read through the lifted mean beside it."""
    report = sv.verify(
        f"SELECT m FROM (SELECT k, SUM({arg}) AS s, AVG(x) AS m FROM t GROUP BY k) WHERE s > 0",
        tables=TS,
        requires={"t": [*RANGES, sv.max_rows(cap)]},
        semantics="duckdb",
        on_inferred="warn",
    )
    return bool(_abs_bound(report, "m").get("proved"))


def test_an_integer_sum_inside_64_bits_is_proved_exact():
    # 1e11 rows of at most 1e7: 1e18 <= 2^63 - 1.
    assert _sum_proved("x", 100_000_000_000)


def test_a_decimal_sum_inside_its_type_is_proved_exact():
    # DECIMAL(5,2) sums to DECIMAL(15,2): 1e6 rows of 999.99 stay below 1e15 - 1.
    assert _sum_proved("c", 1_000_000)


def test_a_decimal_sum_that_may_leave_its_type_is_not_proved():
    # 1e11 rows of 999.99 reach 1e16 > 1e15 - 1, though the unscaled sum,
    # 99999 * 1e11, fits 64 bits. The integer SUM at the same cap is proved
    # (test_an_integer_sum_inside_64_bits_is_proved_exact): the type's bound moves the flag.
    assert not _sum_proved("c", 100_000_000_000)


@pytest.mark.parametrize(("cap", "bounded"), [(1_000_000, True), (100_000_000_000, False)])
def test_a_double_sum_over_more_than_2_32_rows_has_no_bound(cap, bounded):
    """`measureEps` bounds a double `SUM` over at most 2^32 rows (ruling 197, N3)."""
    report = sv.verify(
        "SELECT k, SUM(d) AS ds FROM t GROUP BY k",
        tables=TS,
        requires={"t": [*RANGES, sv.max_rows(cap)]},
        semantics="portable",
        on_inferred="warn",
    )
    assert ("value" in _abs_bound(report, "ds")) is bounded


@pytest.mark.parametrize(("cap", "proved"), [(1_000_000, True), (None, False)])
def test_the_band_of_a_lifted_mean_follows_its_sums_flag(cap, proved):
    requires = REQUIRES["t"][:2] + ([sv.max_rows(cap)] if cap is not None else [])
    report = sv.verify(
        GROUPED, tables=T, requires={"t": requires}, semantics="duckdb", on_inferred="warn"
    )
    assert bool(_abs_bound(report, "m").get("proved")) is proved
