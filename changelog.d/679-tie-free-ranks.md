### Ranks need no key, and keys pass through joins

`RANK`, `DENSE_RANK`, `PERCENT_RANK` and `CUME_DIST` give tied rows the same
value, so a window of them is deterministic without a key on its order
(`window_tieFree`).

Columns that an inner join's condition or a filter's equality ties together
count as one column for keys (`KeyOn.eqVariants`,
[#694](https://github.com/AlexanderNenninger/substrait-lean/issues/694)).
After `p JOIN customers c ON c.customer_id = p.customer_id`, a key on
`p.customer_id` is a key on `c.customer_id` too, so a dbt model that projects
the dimension's column proves `unique(customer_id)`, and a window ordered by
`revenue DESC, c.customer_id` is determined. A left join's right copy stays
out: its unmatched rows hold NULL there.

Both come from the API critique
([#686](https://github.com/AlexanderNenninger/substrait-lean/pull/686),
[#679](https://github.com/AlexanderNenninger/substrait-lean/issues/679)).
