### SQL lift: a CTE named like an input no longer hides the input's qualified name

With an input keyed `main.orders`, `WITH orders AS (SELECT ... FROM orders) SELECT ... FROM orders` was refused as an unknown table: the lift skipped every table named like a CTE anywhere in the query. It now skips only the names a CTE has in scope, so the CTE's body reads the input ([#2169](https://github.com/AlexanderNenninger/substrait-lean/issues/2169)). A CTE named like its own source table already lifts since [#2166](https://github.com/AlexanderNenninger/substrait-lean/issues/2166)'s fix.
