# How the engines are made to agree

The checked plan has one meaning, `Rel.eval` in the Lean model. Each
translation writes that meaning out explicitly, and raises or refuses where
an engine can't follow it. The differential tests compare every engine with
the model on random tables.

* **NULL logic.** Filters and join conditions keep a row only when the
  condition is TRUE (`IS TRUE`); `AND`/`OR` are three-valued; equi-join keys
  never match on NULL. Every `ORDER BY` says where NULLs go.
* **Integers** are 64-bit. Overflow raises on DuckDB, Polars and Spark (ANSI
  mode), and Snowflake's NUMBER(38) is range-checked, where DataFusion wraps
  silently. Integer division and remainder truncate toward zero everywhere.
  Division by zero, `MIN / -1`, bad `POWER`s and out-of-range casts raise.
* **Doubles** have one zero (−0.0 is 0.0) and one NaN, equal to itself and
  above every number, in comparisons, joins, grouping and sorts. `SUM` and
  `AVG` of doubles add in the model's order on DuckDB and Polars; on
  Snowflake and Spark, whose tables have no order, they are refused.
* **Order.** Below a `LIMIT`, a window or a sort, an ordinal column carries
  the model's row order, so ties break the same way on DuckDB and Polars.
  Snowflake and Spark need `tie_free=True`.
* **Strings** count characters, not bytes, in lengths, positions and
  `substring`; `LIKE` names its escape character.
* **Time.** Timestamps are microseconds without a time zone (`TIMESTAMP_NTZ`
  on Snowflake and Spark); `date_part` and `date_trunc` follow the model's
  calendar (ISO weeks), not the session's week start.

DataFusion runs the plan through its own Substrait consumer, so its own
semantics apply there; the project's notebook on DataFusion's quirks
(chapter 16 of the tour) lists where they differ from the model.
