### A repeated guarded double operation is computed once

The guards of a double operation repeated the operation's SQL, and nested operations multiplied
it: `(x * x + x) / y` wrote 579,251 characters. A projection of double arithmetic
(no branch or short-circuit, so every part is evaluated on every row anyway) now computes
each such operation once, in a layer below it. The same query writes 3,528 characters and
runs in 0.011 s on 3 million rows in DuckDB, against 0.657 s
([#1608](https://github.com/AlexanderNenninger/substrait-lean/issues/1608)).
