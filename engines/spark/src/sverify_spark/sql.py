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

import functools
from collections.abc import Mapping
from typing import Any

from ibis.backends.sql.datatypes import PySparkType

from sverify.sql_lift import Lifted, Profile, Surface, lift

#: The `Profile` fields the lift reads from `Profile.spark`, by the (group,
#: option) of their row in `substrait-check --options`'s `choices.spark`.
PROFILE_OPTIONS: Mapping[str, tuple[str | None, str]] = {
    "overflow": (None, "overflow"),
    "on_division_by_zero": (None, "on_division_by_zero"),
    "min_mod_neg_one": (None, "min_mod_neg_one"),
    "float_division_by_zero": ("fp.div", "on_division_by_zero"),
}


@functools.cache
def spark_profile() -> Profile:
    """What Spark's functions do, as the lift reads them: `Profile.spark`'s
    one choice for each field of `PROFILE_OPTIONS`, read from the checker
    (ruling 288 H4). The other fields keep the reference's value and no rule
    that reads them is in `RULES`, since Spark's choice there is not one value
    (`domain_error`, `log_zero`, `corr_degenerate`).

    Raises:
        ValueError: The checker gives no single value for one of them.
    """
    from sverify.routes import _options_json

    rows = {(r["group"], r["option"]): r["choice"] for r in _options_json()["choices"]["spark"]}
    values = {}
    for name, (group, option) in PROFILE_OPTIONS.items():
        choice = rows.get((group, option)) or rows[(None, option)]
        found = choice.get("behaviours", [])
        if len(found) != 1:
            raise ValueError(f"Profile.spark's {option} ({group}) is not one value: {choice}")
        values[name] = found[0]
    return Profile("spark", **values)


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
    # `count(x)` skips NULLs and is 0 on no rows (spark-sum-int, second note).
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
    """The types the lift reads Spark's SQL over: `INT`, `BIGINT`, booleans
    and strings (and NULL). A narrower integer is refused: the lift types an
    integer literal beside one as DuckDB does (`TINYINT + 100` overflows at
    127), where Spark widens the literal (spark-literal-types)."""
    return t.is_int32() or t.is_int64() or t.is_boolean() or t.is_string() or t.is_null()


def coerces(source: Any, target: Any) -> bool:
    """The conversions Spark makes where the text says none that the lift
    reads: an `INT` to a `BIGINT` (spark-implicit-casts)."""
    return source.is_int32() and target.is_int64()


def orders(t: Any) -> bool:
    """The types whose order a Spark fact states, for `<`, `min`, `max` and
    sort keys: integers. Strings wait for spark-string-order (#2629), booleans
    for a fact of their own."""
    return t.is_integer()


@functools.cache
def spark_sql() -> Surface:
    """Spark's SQL as the lift reads it, with `spark_profile` as its own
    semantics."""
    return Surface(
        "spark",
        "Spark",
        spark_profile(),
        null_ordering="nulls_are_small",
        types=PySparkType,
        catalog="spark_catalog",
        db="default",
        rules=RULES,
        syntax=SYNTAX,
        values=values,
        coerces=coerces,
        orders=orders,
        case_sensitive=True,
    )


def lift_spark(query: str, schemas: Mapping[str, Any], semantics: str = "spark") -> Lifted:
    """Spark's SQL `query` lifted to a plan over the Ibis schemas `schemas`
    (by table name), under the profile `semantics` names (`"spark"` or
    `"portable"`)."""
    return lift(query, schemas, semantics, surface=spark_sql())
