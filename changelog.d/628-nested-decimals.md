### Decimals in lists and structs print with their scale

Rows and counterexamples print a decimal inside a list or struct with its scale: `[1.0, 2.5]` for a `DECIMAL(4, 1)[]`, which printed as `[10, 25]` ([#628](https://github.com/AlexanderNenninger/substrait-lean/issues/628)). The values `Rel.eval` and the written plans compute were right.
