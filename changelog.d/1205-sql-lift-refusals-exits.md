### The SQL lift's refusals say how to go on

Each construct the SQL lift refuses ends with a rewrite it reads, or with the coverage epic ([#231](https://github.com/AlexanderNenninger/substrait-lean/issues/231)): 133 refusals, from `sql_lift`'s `SqlUnsupported`. Refusals about the query itself (a name that does not resolve, a table that is not an input, HAVING without GROUP BY, a nested aggregate) say what to change ([#1205](https://github.com/AlexanderNenninger/substrait-lean/issues/1205)).
