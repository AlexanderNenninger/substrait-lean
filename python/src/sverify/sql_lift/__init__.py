"""DuckDB SQL to Substrait plans, through SQLGlot (#231, M1: #239).

Internal: not part of sverify's public API (`docs/stability.md`); it may
change in any release. Users
reach it through `sv.sql(query, dialect="duckdb", semantics=...)`.

    plan = lift("SELECT region, sum(amount) AS total FROM orders GROUP BY region",
                {"orders": ibis.schema({"region": "string", "amount": "float64"})},
                semantics="duckdb")

SQLGlot parses the query (`read="duckdb"`, strict) and resolves and types its
names against the inputs' schemas (`qualify`). The lift then
writes one Substrait plan, reading each input as a named table, in which every
choice DuckDB's SQL leaves implicit is explicit: casts where DuckDB coerces,
the output type of every function, the options Substrait defines for them
(`on_division_by_zero`, …), and the direction and NULL order of every sort
key. SQLGlot is trusted for parsing and name resolution only; the types of
expressions come from the profile, not from SQLGlot's typing.

How the SQL text reads is DuckDB's in both modes (`engines/duckdb/
facts/`, F1–F3): `/` divides as doubles, `//` divides integers, NULLs sort
last, an integer literal has the narrowest type that holds it, `1.5` is a
`DECIMAL(2, 1)`. The **semantics** (`Profile`) is what the functions then do
where DuckDB and the reference (#185, #209) differ:

* `semantics="duckdb"` (`DUCKDB`): DuckDB's own. A double `/` by zero is
  `±inf` or NaN (`on_division_by_zero: IEEE`), even with
  `error_on_division_by_zero` on. The plan means what DuckDB computes, and the
  checker proves contracts of that. Where Lean's generated lift table has
  an entry (`lift_table`, #268: `+`, `-`, `*`, `/`, `%` of doubles, `log`, `sign`,
  `greatest`/`least`, casts between BIGINT and DOUBLE, `avg` of integers),
  the lift writes that entry, which Lean proves means what DuckDB computes,
  NaN and ±inf included; the other rules are written by hand, pending
  generation.
* `semantics="portable"` (`PORTABLE`): sverify's reference profile. A double `/`
  by zero raises (`ERROR`, decided on #185). A cast of a double or decimal
  to an integer is refused, with the spellings that mean the same under both
  semantics (`CAST(round(x) AS BIGINT)`): DuckDB's cast rounds and the
  reference's (R9, decided on #209) truncates, and the lift refines the
  dialect (D54). The written SQL is guarded where DuckDB differs.

The subset (#239): SELECT, WHERE, arithmetic, comparisons, AND/OR/NOT,
IS NULL, IS [NOT] DISTINCT FROM, BETWEEN, IN lists, CASE, CAST, COALESCE,
NULLIF; numbers (`power`, `abs`, `round`, `floor`, `ceil`, `sign`, `isnan`,
`greatest`, `least`, square roots, logarithms, `exp` and trigonometry); dates and timestamps
(`date_trunc`, date parts: `EXTRACT`, `date_part`, `year()`, …, a date or
timestamp plus or minus a constant interval, `DATE - DATE`, `datediff`);
strings (`length`, `substring`, `trim`, `strpos`, `contains`, `starts_with`,
LIKE and ILIKE, `||`, `concat`, `replace`, `repeat`, `left`, `upper`,
`lower`); inner, left, right, full, semi, anti and cross joins; subqueries
in FROM, uncorrelated scalar, IN and EXISTS subqueries, correlated [NOT] EXISTS
and [NOT] IN as conjuncts of WHERE (a semi or anti join, #345), and non-recursive
CTEs; GROUP BY with `count`, `sum`, `avg`, `min` and
`max`, DISTINCT and FILTER (WHERE …) in them, HAVING; window functions
(ranking, `lag`/`lead`, first/last/nth value, aggregates; ROWS and RANGE
frames); DISTINCT, ORDER BY, LIMIT and OFFSET; and the black boxes of
`sverify.black_box` (#325: `base64(encode(s))`, `entropy`), in `blackbox.py`. Anything else, unknown
functions (`Anonymous`) included, raises `Unsupported` saying what.
"""

import importlib

# Re-exported: what other modules, tests and tools import from `sverify.sql_lift`.
from sverify.sql_lift._base import (  # noqa: F401
    DIALECT,
    DUCKDB,
    PORTABLE,
    PROFILES,
    RULES,
    Lifted,
    LiftTable,
    Profile,
    expand_table_shorthand,
    full_name,
    lift,
    lift_table,
    parse,
    register,
)

__all__ = ["DUCKDB", "PORTABLE", "PROFILES", "Lifted", "Profile", "lift", "parse"]

#: The areas, each a module that registers its rules in `RULES`, imported in
#: this order.
AREAS = ("core", "strings", "temporal", "nested", "relations", "casts", "blackbox")

for _area in AREAS:
    importlib.import_module(f"{__name__}.{_area}")
