### A report's assumed SUM names its column

`Report.assumed` named an integer `SUM` it assumes fits 64 bits by Lean's
column index (`SUM of $2`), while the hint on the same report named the
column. The assumed line now names the column the `SUM` adds up, as the hint
does (`SUM of amount_cents`), and `Issue.column` holds it
([#480](https://github.com/AlexanderNenninger/substrait-lean/issues/480)). A
report on SQL text, and a `SUM` of an expression, keep Lean's notation.
