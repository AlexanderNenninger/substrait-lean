### Narrow arithmetic on constants keeps its width

In `(10::TINYINT * 10::TINYINT) * x`, the parser treated the inner product as
a 64-bit value because it reads no column, so the outer multiplication was
not checked at 8 bits: `verify` missed the overflow and the written plan
returned 1000 where DuckDB raises. A call's declared output type now gives its
width (#419), as a column's does, at TINYINT, SMALLINT and INTEGER and for
`+`, `-`, `*`, negation and division.
