### `AVG` of a DECIMAL as a double

DuckDB SQL that averages a DECIMAL column, such as TPC-H Q1's
`avg(l_quantity)`, is now verified. DuckDB returns a DOUBLE, and so does
the plan: the exact sum, converted to a double, divided by the count. NULL
without values. Over windows it is still refused.
