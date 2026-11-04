### Rolling means, MIN over a sliding frame, window aggregates of expressions

Sverify verifies `AVG`, a `SUM` of doubles and `MIN` over a frame that does not
start at UNBOUNDED PRECEDING: rolling means over rows or over an interval, and
`MIN` over a sliding frame. DuckDB and Polars run them; DataFusion, which
slides a frame by retracting rows, still refuses them. A window aggregate's
argument may be an expression (`(t.qty * 2).sum().over(group_by="name")`): the
checker computes it in a projection under the window, so its overflow and
other issues are checked as a projection's
([#506](https://github.com/AlexanderNenninger/substrait-lean/issues/506)).
