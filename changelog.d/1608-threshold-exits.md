### The threshold refusal names the exit for a mean

`a filter, grouping key or sort on a double may keep other rows` now says what to do for each kind of threshold: a constant takes a
precondition that keeps the values away from it, and a threshold computed from the data
(`qty > (SELECT AVG(qty) …)`) takes exact columns, for a mean of integers `x * COUNT(y) > SUM(y)`,
which is the exact mean's comparison and another query than the rounded one
([#1608](https://github.com/AlexanderNenninger/substrait-lean/issues/1608)).
