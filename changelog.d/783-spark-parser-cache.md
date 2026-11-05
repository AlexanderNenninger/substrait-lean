### Spark's local session keeps its parser cache bounded

`sverify.engines`' local Spark session turns on Spark's management of the SQL
parser's ANTLR cache (`spark.sql.parser.manageParserCaches`, flushed at 10 % of
the driver heap). The deeply nested SQL that sverify writes for date arithmetic
grew that cache to most of the 1 GB default heap, and later queries failed with
`AGGREGATE_OUT_OF_MEMORY` (the 0.5.0 Wheels run). `SVERIFY_MEMORY_LIMIT`
(#783) now also sets the session's `spark.driver.memory`.
