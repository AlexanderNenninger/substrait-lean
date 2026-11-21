"""Spark's parser refuses a statement nested too deeply (`spark-exec-parser-depth`):
`parse_sql` turns that one error into `Unsupported`, chained, and passes every
other Spark error through. A constructed exception stands for Spark's; the real
80-level statement is the fact's probe."""

import pytest

from sverify._unsupported import Unsupported
from sverify_spark.engine import parse_sql


class _Spark:
    version = "4.3.0"

    def __init__(self, error):
        self.error = error

    def sql(self, sql):
        raise self.error


class _SparkError(Exception):
    def __init__(self, condition):
        super().__init__(condition)
        self.condition = condition

    def getCondition(self):
        return self.condition


def test_a_statement_too_complex_to_parse_is_refused_by_sverify():
    cause = _SparkError("FAILED_TO_PARSE_TOO_COMPLEX")
    with pytest.raises(Unsupported, match=r"refused the SQL sverify wrote.*\(1,234 bytes\)") as e:
        parse_sql(_Spark(cause), "x" * 1234)
    assert e.value.__cause__ is cause
    assert "spark-exec-parser-depth" in str(e.value)
    assert "nothing ran" in str(e.value)


@pytest.mark.parametrize("error", [_SparkError("PARSE_SYNTAX_ERROR"), ValueError("no condition")])
def test_any_other_spark_error_passes_through_unchanged(error):
    with pytest.raises(type(error)) as e:
        parse_sql(_Spark(error), "SELECT 1")
    assert e.value is error


def test_a_statement_that_parses_is_returned():
    class Fine:
        def sql(self, sql):
            return ("frame", sql)

    assert parse_sql(Fine(), "SELECT 1") == ("frame", "SELECT 1")
