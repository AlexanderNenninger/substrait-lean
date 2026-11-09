"""Substrait plans as SQL, with the semantics of the Lean `Rel` model.

`to_sql(plan, dialect)` reads a Substrait JSON plan the way
`SubstraitLean/Parse.lean` does, so it accepts exactly the plans the checker
accepts: the same operators, the same functions and the same constant folding,
with every other construct rejected (`Unsupported`). It then writes one SQL
query whose result is `Rel.eval` of the plan. Nothing is left to engine
defaults:

* Every subquery names its columns positionally (`c0`, `c1`, …), so field
  references are unambiguous whatever the input tables call their columns.
* Integers are `BIGINT`: operands are cast, and arithmetic must raise on
  overflow (Lean's integers are unbounded; a wrapped result would be wrong).
  Division and remainder truncate. Where DataFusion fails at run time
  (division by zero, `MIN / -1`, a bad `POWER` or `CAST(double AS BIGINT)`),
  Lean's value is NULL and `analysis/Sverify/Analysis/Safety.lean` says when that can
  happen; the SQL raises there too (`Dialect.raise_`).
* Doubles have one zero and one NaN (`core/Sverify/Core/Float.lean`): `-0.0` is
  `0.0`, NaN equals itself and is above `inf`, in comparisons, join
  conditions, groups, window partitions and sort keys. Every double read
  from a table, and every one an operation could make `-0.0`, goes through
  `Dialect.canon`, so `-0.0` never reaches a result.
* Filters keep a row only when the condition is TRUE, `AND`/`OR`/`NOT` are
  Kleene's, and every `ORDER BY` key says where NULLs go.
* Row order follows `Rel.eval`'s list order wherever it matters. Below a
  `FETCH` or a window, subqueries carry an ordinal column `o`: scan order for
  tables, row index for `VALUES`, left-major for joins, branch order for
  `UNION ALL` and sort order for windows. Window sorts break ties by it, as
  Lean's stable merge sort does, and the query's result is ordered by it when
  the plan has a `FETCH` or a window.

Engines differ in syntax and in a few semantics; those go through the hooks of
a `Dialect` (see `sverify_duckdb.dialect`).
"""

from sverify.sql.core import black_box, nested, strings, temporal
from sverify.sql.core._base import (
    BIN_KINDS,
    BIT_AGGS,
    BITWISE,
    CALLS,
    DAY_MAX,
    DAY_MIN,
    DOUBLE_FNS,
    EXACT_HOLISTIC,
    EXPRS,
    FMATH,
    I64_MAX,
    I64_MIN,
    ORD,
    OUTSIDE_DATES,
    OUTSIDE_TS,
    TS_MAX,
    TS_MIN,
    UN_KINDS,
    US_PER_DAY,
    VAR_AGGS,
    WHOLE,
    Aggregate,
    Bin,
    Const,
    Cross,
    Dec,
    DecOp,
    Dialect,
    Distinct,
    Emit,
    Expr,
    Fetch,
    Field,
    Filter,
    FixedKind,
    Frame,
    If,
    Join,
    Kind,
    LeanKind,
    Lit,
    Lst,
    Measure,
    OrderBy,
    Plan,
    Project,
    Read,
    Rel,
    Semi,
    SortKey,
    Un,
    UnionAll,
    Unnest,
    Unsupported,
    Values,
    Window,
    WinFn,
    _timestamp_text,
    arity,
    davg_kind,
    dsum_kind,
    expr_kind,
    kinds,
    lean_expr_kind,
    lean_kinds,
    like_pattern,
    numbers_copies,
    order_matters,
    parse_format,
    parse_plan,
    pow10,
    register,
    replace,
    to_sql,
)
from sverify.sql.core.strings import REPEAT_MAX, regex_groups, unicode_classes
from sverify.sql.core.temporal import DATE_PARTS, TIME_UNITS

#: The areas, which register their cases on import; no two share a function.
AREAS = (strings, temporal, nested, black_box)

__all__ = [
    "AREAS",
    "Aggregate",
    "BIN_KINDS",
    "BITWISE",
    "BIT_AGGS",
    "Bin",
    "CALLS",
    "Const",
    "Cross",
    "DATE_PARTS",
    "DAY_MAX",
    "DAY_MIN",
    "DOUBLE_FNS",
    "Dec",
    "DecOp",
    "Dialect",
    "Distinct",
    "EXPRS",
    "Emit",
    "Expr",
    "FMATH",
    "Fetch",
    "Field",
    "Filter",
    "FixedKind",
    "Frame",
    "I64_MAX",
    "I64_MIN",
    "If",
    "Join",
    "Kind",
    "LeanKind",
    "Lit",
    "Lst",
    "Measure",
    "ORD",
    "OUTSIDE_DATES",
    "OUTSIDE_TS",
    "TS_MAX",
    "TS_MIN",
    "OrderBy",
    "Plan",
    "Project",
    "REPEAT_MAX",
    "Read",
    "Rel",
    "Semi",
    "SortKey",
    "TIME_UNITS",
    "UN_KINDS",
    "US_PER_DAY",
    "Un",
    "UnionAll",
    "Unnest",
    "Unsupported",
    "VAR_AGGS",
    "EXACT_HOLISTIC",
    "Values",
    "WHOLE",
    "WinFn",
    "Window",
    "_timestamp_text",
    "arity",
    "davg_kind",
    "dsum_kind",
    "expr_kind",
    "kinds",
    "lean_expr_kind",
    "lean_kinds",
    "like_pattern",
    "numbers_copies",
    "order_matters",
    "parse_format",
    "parse_plan",
    "pow10",
    "regex_groups",
    "register",
    "replace",
    "to_sql",
    "unicode_classes",
]
