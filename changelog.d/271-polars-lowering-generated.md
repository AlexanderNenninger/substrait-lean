### Polars's lowering is generated and proved

Polars now has a generated lowering, as DuckDB has: each function Polars
computes its own way gets a template, proved to give the reference's value
under Polars's profile (`Lowering.polars_exact`,
[#271](https://github.com/AlexanderNenninger/substrait-lean/issues/271)).
Integer `//` and `%` truncate from Polars's floored ones, `round` and `ceil`
give `0.0` for a negative value that rounds to zero, and `%` of doubles is
refused. Polars's `rounding`, `pow_one_inf`, `negative_start` and
`case_sensitivity` rows, and DuckDB's `round_zero_sign` and `pow_one_inf`
rows, are now proved. `Profile.polars`, which `semantics="polars"` will
verify under, states Polars's `-0.0` from `round` and `ceil`. The translation
to Polars still writes these functions by hand, and a test checks that it
agrees with the table.
