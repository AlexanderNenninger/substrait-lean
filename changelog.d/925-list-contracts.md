### Contracts on list and struct columns

The checker now describes a list column by its length and its elements, and
a struct column by its fields ([#925](https://github.com/AlexanderNenninger/substrait-lean/issues/925)).
Bounds and NOT NULL pass through `cardinality` (Ibis `length()`), `map`,
`filter`, list elements and `unnest`, so postconditions such as
`_.tags.length() <= 5`, NOT NULL elements after `map(lambda x:
x.fill_null(0))` or an element bound after `unnest` are proved. A
precondition on `length()` or a declared element type (`array<int64>`)
bounds the elements and lengths it starts from. The facts text names lists
("a list (length ≤ 5; of a string or NULL)"). Relations between the
elements of one list are not described (`docs/nested-values.md`).
