### Reports as data for tools built on sverify

What sverify-dbt, a package that checks dbt projects with sverify, needed
from the public API
([#177](https://github.com/AlexanderNenninger/substrait-lean/issues/177);
the gaps left open are [#699](https://github.com/AlexanderNenninger/substrait-lean/issues/699) to [#710](https://github.com/AlexanderNenninger/substrait-lean/issues/710)):

- `sverify.errors.Unsupported` is the one class every refusal raises: the
  SQL lift's and the Ibis producer's, the SQL writer's and the Polars
  translator's derive from it. `sverify.engines.Unsupported` is the same
  class; before, `verify`'s refusals of SQL escaped
  `except sverify.engines.Unsupported`.
- `Report.needs` lists the preconditions `on_inferred="error"` needs as
  `Needed` records: table, column, comparison, bound, the condition as SQL
  and as the Python `requires` takes (`code`, `_.qty != 0`), and the
  runtime error each rules out.
- `CheckedCondition.reason` says why a postcondition is not proved, as a
  code (`"not_a_key"`, `"may_be_false"`, `"may_be_null"`, `"ties"`, …), and
  `CheckedCondition.condition` is the condition as it was given.
- `verify(tables=...)` takes DuckDB's type names (`{"id": "BIGINT", "name":
  "VARCHAR NOT NULL"}`) beside Ibis's.
- The SQL lift reads `IS [NOT] TRUE` and `IS [NOT] FALSE`.
- The checker's pipes close when it stops, so a script no longer ends with
  a `ResourceWarning`.
