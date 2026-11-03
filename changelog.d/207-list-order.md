### Lists compare element by element

`<`, `>`, `ORDER BY`, `MIN` and `MAX` on lists order them lexicographically,
a proper prefix first (#207). A NULL element that decides a comparison makes
it NULL (`[1, NULL] < [1, 3]`); in `ORDER BY`, `MIN` and `MAX` NULL elements
sort after every other value
([reference semantics](../docs/reference-semantics.md)).
