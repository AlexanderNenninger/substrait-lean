### A `VALUES` row that raises or misses its type is refused

The parser evaluated each row of a `virtualTable` when it read the plan, so an overflow or a division by zero in a computed row never reached the safety analysis, and it never compared a cell or an integer literal with its declared type, so `--write` could emit a plan no consumer accepts. A field that is not a literal is now refused (as the SQL lift refuses `VALUES` of computed values), a cell must fit its column's type (`Parse.literalFits`), and an `i8`, `i16`, `i32` or `i64` literal must fit its width ([#1491](https://github.com/AlexanderNenninger/substrait-lean/issues/1491)).

`right(s, n)` for `n = -2**63` no longer lifts to an `i64` literal one past the type's range (`1 - n`); the offset is capped at the largest one DuckDB's `substring` takes, so the query stays checkable, which the width check on literals would otherwise have turned into a refusal.
