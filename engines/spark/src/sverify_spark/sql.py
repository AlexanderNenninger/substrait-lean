"""Spark's SQL as sverify's lift reads it (#866): its `Surface` and the
profile its own semantics is, and the front end `sverify_spark.PLUGIN`
registers. The lift itself is shared (`sverify.sql_lift`), and reading needs
no JVM: this module imports no `pyspark`.

A query means what Spark 4.3 computes under every setting of the Spark
profile (`SETTINGS`), ANSI mode among them (D73). The lift reads a construct
only where a Spark fact states what Spark computes for it (`RULES`, ruling
288 H1), over integers, booleans and strings (`VALUES`); everything else is
refused, naming #866, and so is every construct DuckDB's lift reads from its
generated Lean table (H5: Spark has none yet). The hand rules are tested
Python: their outside evidence is the replay of Spark's golden files (#2615).
"""

from __future__ import annotations

from collections.abc import Mapping
from typing import Any

from ibis.backends.sql.datatypes import PySparkType

from sverify.sql_lift import Lifted, Profile, Surface, lift

#: What Spark's functions do, as the lift reads them: the values `Profile.spark`
#: states (`substrait-check --options`, `choices.spark`; tied by
#: `engines/spark/tests/test_sql_lift_spark.py`). The other fields keep the
#: reference's value and no rule that reads them is in `RULES`: Spark's choice
#: is not one value there (`domain_error`, `log_zero`, `corr_degenerate`).
SPARK = Profile(
    "spark",
    overflow="ERROR",
    on_division_by_zero="ERROR",
    min_mod_neg_one="ZERO",
    float_division_by_zero="ERROR",
)

#: The constructs the lift reads in Spark's SQL, by SQLGlot node class, each
#: with the Spark fact (`engines/spark/facts/`) that states what Spark computes.
RULES: Mapping[str, str] = {
    # Relations
    "Where": "spark-kleene",
    "Having": "spark-kleene",
    "Group": "spark-null-keys",
    "Join": "spark-null-keys",
    "Order": "spark-null-order",
    "Ordered": "spark-null-order",
    "Limit": "spark-sort-stability",
    "Distinct": "spark-set-operations",
    "Union": "spark-set-operations",
    "Intersect": "spark-set-operations",
    "Except": "spark-set-operations",
    # Values
    "Literal": "spark-literal-types",
    "Null": "spark-literal-types",
    "Boolean": "spark-literal-types",
    # Logic and comparisons
    "And": "spark-kleene",
    "Or": "spark-kleene",
    "Not": "spark-kleene",
    "In": "spark-kleene",
    "Is": "spark-is-null",
    "EQ": "spark-nan-equality",
    "NEQ": "spark-nan-equality",
    "NullSafeEQ": "spark-null-keys",
    "NullSafeNEQ": "spark-null-keys",
    "LT": "spark-nan-order",
    "LTE": "spark-nan-order",
    "GT": "spark-nan-order",
    "GTE": "spark-nan-order",
    "Case": "spark-exec-evaluation-order",
    "If": "spark-exec-evaluation-order",
    "Coalesce": "spark-implicit-casts",
    # Integers
    "Add": "spark-int-arith",
    "Sub": "spark-int-arith",
    "Mul": "spark-int-arith",
    "Neg": "spark-int-arith",
    "Mod": "spark-int-modulus",
    "Abs": "spark-int-abs",
    # Strings
    "DPipe": "spark-concat",
    "Length": "spark-string-plain",
    # Aggregates
    "Count": "spark-sum-int",
    "Min": "spark-nan-order",
    "Max": "spark-nan-order",
}

#: The node classes with no meaning of their own: names, aliases, the clauses
#: that hold the others, parentheses, `*` and CTEs (inlined).
SYNTAX = frozenset(
    {
        "Select",
        "From",
        "Table",
        "TableAlias",
        "Alias",
        "Identifier",
        "Column",
        "Star",
        "Paren",
        "With",
        "CTE",
    }
)


def values(t: Any) -> bool:
    """The types the lift reads Spark's SQL over: signed integers, booleans
    and strings (and NULL)."""
    return t.is_signed_integer() or t.is_boolean() or t.is_string() or t.is_null()


def coerces(source: Any, target: Any) -> bool:
    """The conversions Spark makes where the text says none that the lift
    reads: an integer to a wider one (spark-implicit-casts)."""
    return (
        source.is_signed_integer() and target.is_signed_integer() and source.nbytes <= target.nbytes
    )


#: Spark's SQL as the lift reads it.
SPARK_SQL = Surface(
    "spark",
    "Spark",
    SPARK,
    null_ordering="nulls_are_small",
    types=PySparkType,
    catalog="spark_catalog",
    db="default",
    rules=RULES,
    syntax=SYNTAX,
    values=values,
    coerces=coerces,
    case_sensitive=True,
)


def lift_spark(query: str, schemas: Mapping[str, Any], semantics: str = "spark") -> Lifted:
    """Spark's SQL `query` lifted to a plan over the Ibis schemas `schemas`
    (by table name), under the profile `semantics` names (`"spark"` or
    `"portable"`)."""
    return lift(query, schemas, semantics, surface=SPARK_SQL)
