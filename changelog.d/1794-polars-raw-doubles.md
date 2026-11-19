### Polars keeps the sign of a zero (D31)

The Polars engine made `-0.0` read as `0.0` and canonicalised scalar results, so a plan such as `cot(x)` for a row `x = -0.0` returned `+inf` on Polars where the reference and DuckDB give `-inf`. Reads and scalar results now keep their raw values, as the SQL writers do (#1461); only identity boundaries (comparison, group, join and window keys) read the zeros as one. A sum or difference gets IEEE's zero sign by a shim (`polars-zero-sign`), and so does `x ** y` (`(-0.0) ** 0.5` is `+0.0`). A double group key is the canonical zero (#1794).
