### The strings a column can hold

Sverify tracks the strings a column can be while they are few (up to 64):
a constant is its string, `s = 'k'` and `s IN ('a', 'b')` narrow a column,
`s <> 'k'` and `NOT IN` take strings out, and `CASE`, `COALESCE`, projections,
joins, grouping and `UNION ALL` carry the sets through. A filter
`status <> 'cancelled'` over a source whose `status` is one of four strings
proves `status IN ('placed', 'shipped', 'returned')`, which is dbt's
`accepted_values`, and a tag that is a constant in each branch of a
`UNION ALL` proves the tag's values. The report's facts name the strings:
"one of the strings 'q1', 'q2', 'q3', 'q4'"
([#708](https://github.com/AlexanderNenninger/substrait-lean/issues/708)).

A key of each branch of a `UNION ALL`, with a column the branches cannot share
a value in (a constant tag, a `GROUPING` level, ranges apart), is a key of the
union. `unique(region, quarter)` over an unpivot by `UNION ALL`, and the
group keys of a rollup written as a union, now prove
([#436](https://github.com/AlexanderNenninger/substrait-lean/issues/436)).
