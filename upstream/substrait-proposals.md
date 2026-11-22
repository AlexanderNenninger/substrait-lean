# Substrait spec-gap proposals

Four places where Substrait's specification leaves a plan's result open, each
recorded as a spec gap in [`bugs/`](bugs/) and drafted as a proposal for the
Substrait project (#1093). None is posted: the maintainer is discussing them
with the Substrait community first. Each section gives the gap, what the
engines do today, and what Sverify does about it.

The engine tables cover DuckDB, Polars and Spark, each cell linking the
engine fact behind it. Snowflake's facts are kept privately and are left out.
The drafts themselves live outside this repository, beside the other upstream
reports ([`upstream-report` skill](../.claude/skills/upstream-report/SKILL.md#spec-gap-proposals-1093)).

## ST-7: the unspecified sort direction

A sort field's direction is required, and `relations/basics.md` describes six
directions. The enum has a seventh, `SORT_DIRECTION_UNSPECIFIED`, the value a
field gets when a producer never sets one, and nothing says whether a consumer
rejects it or picks a direction and a NULL placement. It relates to
[substrait#213](https://github.com/substrait-io/substrait/issues/213), which
asks exactly this; the draft is a comment there proposing that the value is
invalid. Record: [ST-7](bugs/ST-7.json).

| Engine | NULL placement with no `NULLS FIRST` or `NULLS LAST` | Fact |
|---|---|---|
| DuckDB 2.0.0 | last, ascending and descending | [duckdb-F2](../engines/duckdb/facts/duckdb-F2.json) |
| Polars 2.1.0 | first, ascending and descending | [polars-null-order](../engines/polars/facts/polars-null-order.json) |
| Spark 4.3.0 | first ascending, last descending | [spark-null-order](../engines/spark/facts/spark-null-order.json) |

Sverify reads the direction as ascending with the NULL placement open, and its
reference puts NULLs last ([D6](../docs/decisions.md#d6-sort-keys-without-a-null-order),
[D8](../docs/decisions.md#d8-the-references-null-order)). A window's or a
measure's key must state its direction.

Status: not posted; the maintainer is discussing it with the Substrait
community first.

## ST-8: decimal rounding

`functions_arithmetic_decimal.yaml` gives each function's result type and
nothing about how digits beyond the result's scale are dropped: always for
`divide`, and for `add`, `subtract` and `multiply` once the precision passes 38.
A cast to a smaller scale leaves it open too. It relates to
[substrait#1224](https://github.com/substrait-io/substrait/issues/1224), which
asks this for the precision-38 case; the draft is a comment there proposing a
`rounding` option. Record: [ST-8](bugs/ST-8.json).

| Engine | Tie rule when digits are dropped | `CAST(1.05 AS DECIMAL(2,1))` | Fact |
|---|---|---|---|
| DuckDB 2.0.0 | half away from zero | `1.1` | [duckdb-decimal-arith](../engines/duckdb/facts/duckdb-decimal-arith.json) |
| Polars 2.1.0 | half to even | `1.0` | [polars-decimal-arith](../engines/polars/facts/polars-decimal-arith.json) |
| Spark 4.3.0 | half away from zero | `1.1` | [spark-decimal-arith](../engines/spark/facts/spark-decimal-arith.json) |

Sverify has one option for every place a decimal loses digits,
`decimal_rescale` ([core semantics](../docs/core-semantics.md)), and its
reference rounds half away from zero
([D42](../docs/decisions.md#d42-the-references-value-of-the-options-no-earlier-decision-states)).
Decimal division is refused until #27.

Status: not posted; the maintainer is discussing it with the Substrait
community first.

## ST-5: infinities with no IEEE number

`divide` says what happens at `inf / inf`: its `on_domain_error` option
decides. The floating-point `add`, `subtract` and `multiply` take only
`rounding`, and nothing says what `inf - inf`, `inf + (-inf)` or `0 * inf`
give. No Substrait issue asks it; the draft is a new issue proposing
`divide`'s `on_domain_error` for the three operations. Record:
[ST-5](bugs/ST-5.json).

| Engine | `inf - inf`, `inf + (-inf)`, `0 * inf` | Fact |
|---|---|---|
| DuckDB 2.0.0 | NaN | [duckdb-R15-double-arith](../engines/duckdb/facts/duckdb-R15-double-arith.json) |
| Polars 2.1.0 | NaN | [polars-double-arith](../engines/polars/facts/polars-double-arith.json) |
| Spark 4.3.0 | NaN, in ANSI mode and out of it | [spark-double-arith](../engines/spark/facts/spark-double-arith.json) |

Sverify's reference creates no NaN: such an operation is an issue that
`verify` rules out or checks on the data
([D37](../docs/decisions.md#d37-no-operation-creates-a-nan)).

Status: not posted; the maintainer is discussing it with the Substrait
community first.

## ST-9: floating-point overflow

Substrait's test cases expect `±inf` when finite floating-point inputs give a
result too large for the type, and no floating-point function offers an
option to raise. `sum` of `fp32` and `fp64` takes `overflow` values the
specification defines for integers only. No Substrait issue asks it; the
draft is a new issue proposing `overflow` on floating-point arithmetic, with
each value's meaning for floats. Record: [ST-9](bugs/ST-9.json).

| Engine | `1e308 * 10`, and `sum` of `1e308` and `1e308` | Fact |
|---|---|---|
| DuckDB 2.0.0 | `inf`; no double operation raises | [duckdb-double-overflow](../engines/duckdb/facts/duckdb-double-overflow.json) |
| Polars 2.1.0 | `inf` | [polars-double-arith](../engines/polars/facts/polars-double-arith.json), [polars-nonfinite-aggregates](../engines/polars/facts/polars-nonfinite-aggregates.json) |
| Spark 4.3.0 | `inf`, in ANSI mode and out of it | [spark-double-arith](../engines/spark/facts/spark-double-arith.json), [spark-sum-double](../engines/spark/facts/spark-sum-double.json) |

Sverify's reference raises when an operation on finite doubles gives `±inf`,
an inferred precondition that `verify` proves from the bounds or checks on
the data ([D38](../docs/decisions.md#d38-no-operation-on-finite-doubles-overflows-to-infinity)).

Status: not posted; the maintainer is discussing it with the Substrait
community first.
