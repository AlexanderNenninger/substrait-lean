# How the engines are made to agree

The checked plan has one meaning, `Rel.eval` in the Lean model. Each
translation writes that meaning out explicitly, and raises or refuses where
an engine can't follow it. The differential tests compare every engine with
the model on random tables.

* **NULL logic.** Filters and join conditions keep a row only when the
  condition is TRUE (`IS TRUE`); `AND`/`OR` are three-valued; equi-join keys
  never match on NULL. Every `ORDER BY` says where NULLs go.
* **Integers** have their declared widths. Overflow raises on DuckDB, Polars
  and Spark (ANSI mode), and Snowflake's NUMBER(38) is range-checked. Integer division and remainder truncate toward zero everywhere.
  Division by zero, `MIN / -1`, bad `POWER`s and out-of-range casts raise.
* **Doubles** have one zero (−0.0 is 0.0) and one NaN, equal to itself and
  above every number, in comparisons, joins, grouping and sorts. `SUM` and
  `AVG` of doubles add in the model's order on DuckDB and Polars; on
  Snowflake and Spark, whose tables have no order, they are refused.
* **Order.** Ties and the rows of a `LIMIT` are open, as the reference leaves
  them (`rows="multiset"`): the sort's keys order the rows, and a plan's last
  sort orders its result. Lenses with `rows="sequence"` carry the
  model's row order in an ordinal column on DuckDB and refuses on Snowflake
  and Spark.
* **Strings** count characters, not bytes, in lengths, positions and
  `substring`; `LIKE` names its escape character.
* **Time.** Timestamps are microseconds without a time zone (`TIMESTAMP_NTZ`
  on Snowflake and Spark); `date_part` and `date_trunc` follow the model's
  calendar (ISO weeks), not the session's week start.
