### The SQL lift reads `ascii`, `levenshtein`, `if` and `arbitrary`

DuckDB SQL with `ascii(s)`, `levenshtein(s, t)`, `if(c, a, b)` and `arbitrary(x)` lifts (part of [#328](https://github.com/AlexanderNenninger/substrait-lean/issues/328)). `ascii` and `levenshtein` are the model's functions, which agree with DuckDB on ASCII text and raise on other text as the reference does (D43). `if(c, a, b)` is the `CASE` it abbreviates, and `arbitrary` is DuckDB's other name of `first`.
