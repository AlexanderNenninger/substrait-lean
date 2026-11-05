### Keys through either copy of a join column

Columns that an inner join's condition or a filter's equality ties together
count as one column for keys
([#694](https://github.com/AlexanderNenninger/substrait-lean/issues/694)).
After `p JOIN customers c ON c.customer_id = p.customer_id`, a key on
`p.customer_id` is a key on `c.customer_id` too, so a dbt model that projects
the dimension's column proves `unique(customer_id)`, and
`rank() OVER (ORDER BY revenue DESC, c.customer_id)` is determined. Lean proves
it (`KeyOn.eqVariants`). A left join's right copy stays out: its unmatched rows
hold NULL there.
