### A sorted result is sorted once

Under a multiset observation, the SQL Sverify writes for a result that ends in a sort, or a top-N, sorts by the sort's own keys. It no longer numbers the rows by those keys and sorts again by the number. Spark and Snowflake write this by default, and DuckDB's checked runs do where the order of ties can't be observed (#2186).
