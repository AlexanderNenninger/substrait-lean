### A key survives a GROUP BY of the key and its attributes

`unique(customer_id)` on the input now proves `unique(customer_id)` after `GROUP BY customer_id, name`, and after the same grouping of `customers LEFT JOIN orders`. Sverify carries functional dependencies through the plan (a key gives every column, and a join's left side keeps its dependencies), and a dependency onto a key makes its left side a key ([#1993](https://github.com/AlexanderNenninger/substrait-lean/issues/1993)).
